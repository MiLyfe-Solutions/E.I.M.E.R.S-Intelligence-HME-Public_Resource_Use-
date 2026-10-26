import V185TrunkScan23Chunk0588

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3482949 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 2, 5, 2]
def baseStart_3482949 : Nat := 118140960795 + 3482949 * 2 ^ 59
def prefixEnd_3482949 : Nat := 4983230072969 + 3 ^ 40 * 3482949 * 2
def baseEnd_3482949 : Nat := 1788426932096598679719715

theorem tailTrace_3482949 : CollatzResearch.WordTrace tailWord_3482949 prefixEnd_3482949 1788426932096598679719715 := by
  unfold tailWord_3482949
  simp only [CollatzResearch.WordTrace]
  refine ⟨127033586258878088176651901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84689057505918725451101267 127033586258878088176651901)
  ·
    refine ⟨47637594847079283066244463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127033586258878088176651901 47637594847079283066244463)
    ·
      refine ⟨71456392270618924599366695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47637594847079283066244463 71456392270618924599366695)
      ·
        refine ⟨107184588405928386899050043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71456392270618924599366695 107184588405928386899050043)
        ·
          refine ⟨160776882608892580348575065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107184588405928386899050043 160776882608892580348575065)
          ·
            refine ⟨120582661956669435261431299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160776882608892580348575065 120582661956669435261431299)
            ·
              refine ⟨180873992935004152892146949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120582661956669435261431299 180873992935004152892146949)
              ·
                refine ⟨33913873675313278667277553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180873992935004152892146949 33913873675313278667277553)
                ·
                  refine ⟨25435405256484959000458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33913873675313278667277553 25435405256484959000458165)
                  ·
                    refine ⟨2384569242795464906292953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25435405256484959000458165 2384569242795464906292953)
                    ·
                      refine ⟨1788426932096598679719715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384569242795464906292953 1788426932096598679719715)
                      ·
                        rfl

theorem cell23_3482949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_3482949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482949 prefixEnd_3482949 := by exact prefixLift 3482949
  have htrace : WordTrace (prefixWord ++ tailWord_3482949) baseStart_3482949 baseEnd_3482949 := by
    simpa [prefixWord, tailWord_3482949, baseEnd_3482949] using wordTrace_append hprefix tailTrace_3482949
  have hstable : (prefixWord ++ tailWord_3482949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482949).length < 2 ^ (prefixWord ++ tailWord_3482949).sum := by decide
  have hdescent : baseEnd_3482949 < baseStart_3482949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482952 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3482952 : Nat := 118140960795 + 3482952 * 2 ^ 59
def prefixEnd_3482952 : Nat := 4983230072969 + 3 ^ 40 * 3482952 * 2
def baseEnd_3482952 : Nat := 1788428472538562167982201

theorem tailTrace_3482952 : CollatzResearch.WordTrace tailWord_3482952 prefixEnd_3482952 1788428472538562167982201 := by
  unfold tailWord_3482952
  simp only [CollatzResearch.WordTrace]
  refine ⟨63516847838933609844505555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84689130451911479792674073 63516847838933609844505555)
  ·
    refine ⟨95275271758400414766758333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63516847838933609844505555 95275271758400414766758333)
    ·
      refine ⟨35728226909400155537534375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95275271758400414766758333 35728226909400155537534375)
      ·
        refine ⟨53592340364100233306301563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35728226909400155537534375 53592340364100233306301563)
        ·
          refine ⟨80388510546150349959452345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53592340364100233306301563 80388510546150349959452345)
          ·
            refine ⟨60291382909612762469589259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80388510546150349959452345 60291382909612762469589259)
            ·
              refine ⟨90437074364419143704383889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60291382909612762469589259 90437074364419143704383889)
              ·
                refine ⟨67827805773314357778287917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90437074364419143704383889 67827805773314357778287917)
                ·
                  refine ⟨25435427164992884166857969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67827805773314357778287917 25435427164992884166857969)
                  ·
                    refine ⟨19076570373744663125143477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25435427164992884166857969 19076570373744663125143477)
                    ·
                      refine ⟨1788428472538562167982201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19076570373744663125143477 1788428472538562167982201)
                      ·
                        rfl

theorem cell23_3482952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3482952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482952 prefixEnd_3482952 := by exact prefixLift 3482952
  have htrace : WordTrace (prefixWord ++ tailWord_3482952) baseStart_3482952 baseEnd_3482952 := by
    simpa [prefixWord, tailWord_3482952, baseEnd_3482952] using wordTrace_append hprefix tailTrace_3482952
  have hstable : (prefixWord ++ tailWord_3482952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482952).length < 2 ^ (prefixWord ++ tailWord_3482952).sum := by decide
  have hdescent : baseEnd_3482952 < baseStart_3482952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482979 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3482979 : Nat := 118140960795 + 3482979 * 2 ^ 59
def prefixEnd_3482979 : Nat := 4983230072969 + 3 ^ 40 * 3482979 * 2
def baseEnd_3482979 : Nat := 1788442336516233562344577

theorem tailTrace_3482979 : CollatzResearch.WordTrace tailWord_3482979 prefixEnd_3482979 1788442336516233562344577 := by
  unfold tailWord_3482979
  simp only [CollatzResearch.WordTrace]
  refine ⟨127034680448769403300243991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84689786965846268866829327 127034680448769403300243991)
  ·
    refine ⟨190552020673154104950365987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127034680448769403300243991 190552020673154104950365987)
    ·
      refine ⟨285828031009731157425548981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190552020673154104950365987 285828031009731157425548981)
      ·
        refine ⟨26796377907162296008645217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285828031009731157425548981 26796377907162296008645217)
        ·
          refine ⟨20097283430371722006483913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26796377907162296008645217 20097283430371722006483913)
          ·
            refine ⟨15072962572778791504862935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20097283430371722006483913 15072962572778791504862935)
            ·
              refine ⟨22609443859168187257294403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072962572778791504862935 22609443859168187257294403)
              ·
                refine ⟨33914165788752280885941605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22609443859168187257294403 33914165788752280885941605)
                ·
                  refine ⟨6358906085391052666114051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33914165788752280885941605 6358906085391052666114051)
                  ·
                    refine ⟨9538359128086578999171077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358906085391052666114051 9538359128086578999171077)
                    ·
                      refine ⟨1788442336516233562344577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9538359128086578999171077 1788442336516233562344577)
                      ·
                        rfl

theorem cell23_3482979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3482979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482979 prefixEnd_3482979 := by exact prefixLift 3482979
  have htrace : WordTrace (prefixWord ++ tailWord_3482979) baseStart_3482979 baseEnd_3482979 := by
    simpa [prefixWord, tailWord_3482979, baseEnd_3482979] using wordTrace_append hprefix tailTrace_3482979
  have hstable : (prefixWord ++ tailWord_3482979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482979).length < 2 ^ (prefixWord ++ tailWord_3482979).sum := by decide
  have hdescent : baseEnd_3482979 < baseStart_3482979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482986 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3482986 : Nat := 118140960795 + 3482986 * 2 ^ 59
def prefixEnd_3482986 : Nat := 4983230072969 + 3 ^ 40 * 3482986 * 2
def baseEnd_3482986 : Nat := 1788445930880815034957045

theorem tailTrace_3482986 : CollatzResearch.WordTrace tailWord_3482986 prefixEnd_3482986 1788445930880815034957045 := by
  unfold tailWord_3482986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31758733939936010873937203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84689957173162695663832541 31758733939936010873937203)
  ·
    refine ⟨47638100909904016310905805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31758733939936010873937203 47638100909904016310905805)
    ·
      refine ⟨17864287841214006116589677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47638100909904016310905805 17864287841214006116589677)
      ·
        refine ⟨6699107940455252293721129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17864287841214006116589677 6699107940455252293721129)
        ·
          refine ⟨5024330955341439220290847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699107940455252293721129 5024330955341439220290847)
          ·
            refine ⟨7536496433012158830436271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024330955341439220290847 7536496433012158830436271)
            ·
              refine ⟨11304744649518238245654407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7536496433012158830436271 11304744649518238245654407)
              ·
                refine ⟨16957116974277357368481611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11304744649518238245654407 16957116974277357368481611)
                ·
                  refine ⟨25435675461416036052722417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16957116974277357368481611 25435675461416036052722417)
                  ·
                    refine ⟨19076756596062027039541813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25435675461416036052722417 19076756596062027039541813)
                    ·
                      refine ⟨1788445930880815034957045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19076756596062027039541813 1788445930880815034957045)
                      ·
                        rfl

theorem cell23_3482986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3482986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482986 prefixEnd_3482986 := by exact prefixLift 3482986
  have htrace : WordTrace (prefixWord ++ tailWord_3482986) baseStart_3482986 baseEnd_3482986 := by
    simpa [prefixWord, tailWord_3482986, baseEnd_3482986] using wordTrace_append hprefix tailTrace_3482986
  have hstable : (prefixWord ++ tailWord_3482986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482986).length < 2 ^ (prefixWord ++ tailWord_3482986).sum := by decide
  have hdescent : baseEnd_3482986 < baseStart_3482986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482999 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_3482999 : Nat := 118140960795 + 3482999 * 2 ^ 59
def prefixEnd_3482999 : Nat := 4983230072969 + 3 ^ 40 * 3482999 * 2
def baseEnd_3482999 : Nat := 1788452606129323484094485

theorem tailTrace_3482999 : CollatzResearch.WordTrace tailWord_3482999 prefixEnd_3482999 1788452606129323484094485 := by
  unfold tailWord_3482999
  simp only [CollatzResearch.WordTrace]
  refine ⟨127035409908696946715972051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84690273272464631143981367 127035409908696946715972051)
  ·
    refine ⟨190553114863045420073958077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127035409908696946715972051 190553114863045420073958077)
    ·
      refine ⟨71457418073642032527734279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190553114863045420073958077 71457418073642032527734279)
      ·
        refine ⟨107186127110463048791601419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71457418073642032527734279 107186127110463048791601419)
        ·
          refine ⟨160779190665694573187402129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107186127110463048791601419 160779190665694573187402129)
          ·
            refine ⟨120584392999270929890551597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160779190665694573187402129 120584392999270929890551597)
            ·
              refine ⟨45219147374726598708956849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120584392999270929890551597 45219147374726598708956849)
              ·
                refine ⟨33914360531044949031717637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45219147374726598708956849 33914360531044949031717637)
                ·
                  refine ⟨6358942599570927943447057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33914360531044949031717637 6358942599570927943447057)
                  ·
                    refine ⟨4769206949678195957585293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358942599570927943447057 4769206949678195957585293)
                    ·
                      refine ⟨1788452606129323484094485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769206949678195957585293 1788452606129323484094485)
                      ·
                        rfl

theorem cell23_3482999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_3482999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482999 prefixEnd_3482999 := by exact prefixLift 3482999
  have htrace : WordTrace (prefixWord ++ tailWord_3482999) baseStart_3482999 baseEnd_3482999 := by
    simpa [prefixWord, tailWord_3482999, baseEnd_3482999] using wordTrace_append hprefix tailTrace_3482999
  have hstable : (prefixWord ++ tailWord_3482999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482999).length < 2 ^ (prefixWord ++ tailWord_3482999).sum := by decide
  have hdescent : baseEnd_3482999 < baseStart_3482999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483016 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3483016 : Nat := 118140960795 + 3483016 * 2 ^ 59
def prefixEnd_3483016 : Nat := 4983230072969 + 3 ^ 40 * 3483016 * 2
def baseEnd_3483016 : Nat := 1788461335300449917581907

theorem tailTrace_3483016 : CollatzResearch.WordTrace tailWord_3483016 prefixEnd_3483016 1788461335300449917581907 := by
  unfold tailWord_3483016
  simp only [CollatzResearch.WordTrace]
  refine ⟨63518014974817679309670451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84690686633090239079560601 63518014974817679309670451)
  ·
    refine ⟨95277022462226518964505677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63518014974817679309670451 95277022462226518964505677)
    ·
      refine ⟨35728883423334944611689629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95277022462226518964505677 35728883423334944611689629)
      ·
        refine ⟨13398331283750604229383611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35728883423334944611689629 13398331283750604229383611)
        ·
          refine ⟨20097496925625906344075417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13398331283750604229383611 20097496925625906344075417)
          ·
            refine ⟨15073122694219429758056563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20097496925625906344075417 15073122694219429758056563)
            ·
              refine ⟨22609684041329144637084845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073122694219429758056563 22609684041329144637084845)
              ·
                refine ⟨8478631515498429238906817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22609684041329144637084845 8478631515498429238906817)
                ·
                  refine ⟨6358973636623821929180113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8478631515498429238906817 6358973636623821929180113)
                  ·
                    refine ⟨4769230227467866446885085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358973636623821929180113 4769230227467866446885085)
                    ·
                      refine ⟨1788461335300449917581907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769230227467866446885085 1788461335300449917581907)
                      ·
                        rfl

theorem cell23_3483016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3483016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483016 prefixEnd_3483016 := by exact prefixLift 3483016
  have htrace : WordTrace (prefixWord ++ tailWord_3483016) baseStart_3483016 baseEnd_3483016 := by
    simpa [prefixWord, tailWord_3483016, baseEnd_3483016] using wordTrace_append hprefix tailTrace_3483016
  have hstable : (prefixWord ++ tailWord_3483016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483016).length < 2 ^ (prefixWord ++ tailWord_3483016).sum := by decide
  have hdescent : baseEnd_3483016 < baseStart_3483016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483079 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 1, 6]
def baseStart_3483079 : Nat := 118140960795 + 3483079 * 2 ^ 59
def prefixEnd_3483079 : Nat := 4983230072969 + 3 ^ 40 * 3483079 * 2
def baseEnd_3483079 : Nat := 596164561527227723698039

theorem tailTrace_3483079 : CollatzResearch.WordTrace tailWord_3483079 prefixEnd_3483079 596164561527227723698039 := by
  unfold tailWord_3483079
  simp only [CollatzResearch.WordTrace]
  refine ⟨127038327748407120378884291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84692218498938080252589527 127038327748407120378884291)
  ·
    refine ⟨190557491622610680568326437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127038327748407120378884291 190557491622610680568326437)
    ·
      refine ⟨35729529679239502606561207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190557491622610680568326437 35729529679239502606561207)
      ·
        refine ⟨53594294518859253909841811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35729529679239502606561207 53594294518859253909841811)
        ·
          refine ⟨80391441778288880864762717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53594294518859253909841811 80391441778288880864762717)
          ·
            refine ⟨30146790666858330324286019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80391441778288880864762717 30146790666858330324286019)
            ·
              refine ⟨45220186000287495486429029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30146790666858330324286019 45220186000287495486429029)
              ·
                refine ⟨8478784875053905403705443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45220186000287495486429029 8478784875053905403705443)
                ·
                  refine ⟨12718177312580858105558165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478784875053905403705443 12718177312580858105558165)
                  ·
                    refine ⟨596164561527227723698039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12718177312580858105558165 596164561527227723698039)
                    ·
                      rfl

theorem cell23_3483079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_3483079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483079 prefixEnd_3483079 := by exact prefixLift 3483079
  have htrace : WordTrace (prefixWord ++ tailWord_3483079) baseStart_3483079 baseEnd_3483079 := by
    simpa [prefixWord, tailWord_3483079, baseEnd_3483079] using wordTrace_append hprefix tailTrace_3483079
  have hstable : (prefixWord ++ tailWord_3483079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483079).length < 2 ^ (prefixWord ++ tailWord_3483079).sum := by decide
  have hdescent : baseEnd_3483079 < baseStart_3483079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483080 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_3483080 : Nat := 118140960795 + 3483080 * 2 ^ 59
def prefixEnd_3483080 : Nat := 4983230072969 + 3 ^ 40 * 3483080 * 2
def baseEnd_3483080 : Nat := 1788494198062337667181613

theorem tailTrace_3483080 : CollatzResearch.WordTrace tailWord_3483080 prefixEnd_3483080 1788494198062337667181613 := by
  unfold tailWord_3483080
  simp only [CollatzResearch.WordTrace]
  refine ⟨63519182110701748774835347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84692242814268998366447129 63519182110701748774835347)
  ·
    refine ⟨95278773166052623162253021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63519182110701748774835347 95278773166052623162253021)
    ·
      refine ⟨35729539937269733685844883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95278773166052623162253021 35729539937269733685844883)
      ·
        refine ⟨53594309905904600528767325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35729539937269733685844883 53594309905904600528767325)
        ·
          refine ⟨20097866214714225198287747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53594309905904600528767325 20097866214714225198287747)
          ·
            refine ⟨30146799322071337797431621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20097866214714225198287747 30146799322071337797431621)
            ·
              refine ⟨5652524872888375837018429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30146799322071337797431621 5652524872888375837018429)
              ·
                refine ⟨2119696827333140938881911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5652524872888375837018429 2119696827333140938881911)
                ·
                  refine ⟨3179545240999711408322867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119696827333140938881911 3179545240999711408322867)
                  ·
                    refine ⟨4769317861499567112484301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3179545240999711408322867 4769317861499567112484301)
                    ·
                      refine ⟨1788494198062337667181613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769317861499567112484301 1788494198062337667181613)
                      ·
                        rfl

theorem cell23_3483080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_3483080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483080 prefixEnd_3483080 := by exact prefixLift 3483080
  have htrace : WordTrace (prefixWord ++ tailWord_3483080) baseStart_3483080 baseEnd_3483080 := by
    simpa [prefixWord, tailWord_3483080, baseEnd_3483080] using wordTrace_append hprefix tailTrace_3483080
  have hstable : (prefixWord ++ tailWord_3483080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483080).length < 2 ^ (prefixWord ++ tailWord_3483080).sum := by decide
  have hdescent : baseEnd_3483080 < baseStart_3483080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483126 : List Nat := [5, 1, 1, 1, 2, 3, 1, 9]
def baseStart_3483126 : Nat := 118140960795 + 3483126 * 2 ^ 59
def prefixEnd_3483126 : Nat := 4983230072969 + 3 ^ 40 * 3483126 * 2
def baseEnd_3483126 : Nat := 66241400673053499526163

theorem tailTrace_3483126 : CollatzResearch.WordTrace tailWord_3483126 prefixEnd_3483126 66241400673053499526163 := by
  unfold tailWord_3483126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7940002623702302962865327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84693361319491231603896821 7940002623702302962865327)
  ·
    refine ⟨11910003935553454444297991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7940002623702302962865327 11910003935553454444297991)
    ·
      refine ⟨17865005903330181666446987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11910003935553454444297991 17865005903330181666446987)
      ·
        refine ⟨26797508854995272499670481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17865005903330181666446987 26797508854995272499670481)
        ·
          refine ⟨20098131641246454374752861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26797508854995272499670481 20098131641246454374752861)
          ·
            refine ⟨7536799365467420390532323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20098131641246454374752861 7536799365467420390532323)
            ·
              refine ⟨11305199048201130585798485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7536799365467420390532323 11305199048201130585798485)
              ·
                refine ⟨66241400673053499526163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11305199048201130585798485 66241400673053499526163)
                ·
                  rfl

theorem cell23_3483126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_3483126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483126 prefixEnd_3483126 := by exact prefixLift 3483126
  have htrace : WordTrace (prefixWord ++ tailWord_3483126) baseStart_3483126 baseEnd_3483126 := by
    simpa [prefixWord, tailWord_3483126, baseEnd_3483126] using wordTrace_append hprefix tailTrace_3483126
  have hstable : (prefixWord ++ tailWord_3483126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483126).length < 2 ^ (prefixWord ++ tailWord_3483126).sum := by decide
  have hdescent : baseEnd_3483126 < baseStart_3483126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483153 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_3483153 : Nat := 118140960795 + 3483153 * 2 ^ 59
def prefixEnd_3483153 : Nat := 4983230072969 + 3 ^ 40 * 3483153 * 2
def baseEnd_3483153 : Nat := 1788531682150115881568777

theorem tailTrace_3483153 : CollatzResearch.WordTrace tailWord_3483153 prefixEnd_3483153 1788531682150115881568777 := by
  unfold tailWord_3483153
  simp only [CollatzResearch.WordTrace]
  refine ⟨127041026750139031017078113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84694017833426020678052075 127041026750139031017078113)
  ·
    refine ⟨95280770062604273262808585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127041026750139031017078113 95280770062604273262808585)
    ·
      refine ⟨71460577546953204947106439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95280770062604273262808585 71460577546953204947106439)
      ·
        refine ⟨107190866320429807420659659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71460577546953204947106439 107190866320429807420659659)
        ·
          refine ⟨160786299480644711130989489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107190866320429807420659659 160786299480644711130989489)
          ·
            refine ⟨120589724610483533348242117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160786299480644711130989489 120589724610483533348242117)
            ·
              refine ⟨22610573364465662502795397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120589724610483533348242117 22610573364465662502795397)
              ·
                refine ⟨4239482505837311719274137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22610573364465662502795397 4239482505837311719274137)
                ·
                  refine ⟨3179611879377983789455603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239482505837311719274137 3179611879377983789455603)
                  ·
                    refine ⟨4769417819066975684183405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3179611879377983789455603 4769417819066975684183405)
                    ·
                      refine ⟨1788531682150115881568777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769417819066975684183405 1788531682150115881568777)
                      ·
                        rfl

theorem cell23_3483153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_3483153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483153 prefixEnd_3483153 := by exact prefixLift 3483153
  have htrace : WordTrace (prefixWord ++ tailWord_3483153) baseStart_3483153 baseEnd_3483153 := by
    simpa [prefixWord, tailWord_3483153, baseEnd_3483153] using wordTrace_append hprefix tailTrace_3483153
  have hstable : (prefixWord ++ tailWord_3483153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483153).length < 2 ^ (prefixWord ++ tailWord_3483153).sum := by decide
  have hdescent : baseEnd_3483153 < baseStart_3483153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483193 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3483193 : Nat := 118140960795 + 3483193 * 2 ^ 59
def prefixEnd_3483193 : Nat := 4983230072969 + 3 ^ 40 * 3483193 * 2
def baseEnd_3483193 : Nat := 1788552221376295725068593

theorem tailTrace_3483193 : CollatzResearch.WordTrace tailWord_3483193 prefixEnd_3483193 1788552221376295725068593 := by
  unfold tailWord_3483193
  simp only [CollatzResearch.WordTrace]
  refine ⟨127042485669994117848534233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84694990446662745232356155 127042485669994117848534233)
  ·
    refine ⟨95281864252495588386400675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127042485669994117848534233 95281864252495588386400675)
    ·
      refine ⟨142922796378743382579601013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95281864252495588386400675 142922796378743382579601013)
      ·
        refine ⟨13399012160507192116837595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142922796378743382579601013 13399012160507192116837595)
        ·
          refine ⟨20098518240760788175256393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399012160507192116837595 20098518240760788175256393)
          ·
            refine ⟨15073888680570591131442295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20098518240760788175256393 15073888680570591131442295)
            ·
              refine ⟨22610833020855886697163443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073888680570591131442295 22610833020855886697163443)
              ·
                refine ⟨33916249531283830045745165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22610833020855886697163443 33916249531283830045745165)
                ·
                  refine ⟨12718593574231436267154437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33916249531283830045745165 12718593574231436267154437)
                  ·
                    refine ⟨2384736295168394300091457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12718593574231436267154437 2384736295168394300091457)
                    ·
                      refine ⟨1788552221376295725068593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384736295168394300091457 1788552221376295725068593)
                      ·
                        rfl

theorem cell23_3483193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3483193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483193 prefixEnd_3483193 := by exact prefixLift 3483193
  have htrace : WordTrace (prefixWord ++ tailWord_3483193) baseStart_3483193 baseEnd_3483193 := by
    simpa [prefixWord, tailWord_3483193, baseEnd_3483193] using wordTrace_append hprefix tailTrace_3483193
  have hstable : (prefixWord ++ tailWord_3483193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483193).length < 2 ^ (prefixWord ++ tailWord_3483193).sum := by decide
  have hdescent : baseEnd_3483193 < baseStart_3483193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483209 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_3483209 : Nat := 118140960795 + 3483209 * 2 ^ 59
def prefixEnd_3483209 : Nat := 4983230072969 + 3 ^ 40 * 3483209 * 2
def baseEnd_3483209 : Nat := 1788560437066767662468519

theorem tailTrace_3483209 : CollatzResearch.WordTrace tailWord_3483209 prefixEnd_3483209 1788560437066767662468519 := by
  unfold tailWord_3483209
  simp only [CollatzResearch.WordTrace]
  refine ⟨127043069237936152581116681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84695379491957435054077787 127043069237936152581116681)
  ·
    refine ⟨95282301928452114435837511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127043069237936152581116681 95282301928452114435837511)
    ·
      refine ⟨142923452892678171653756267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95282301928452114435837511 142923452892678171653756267)
      ·
        refine ⟨214385179339017257480634401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142923452892678171653756267 214385179339017257480634401)
        ·
          refine ⟨160788884504262943110475801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214385179339017257480634401 160788884504262943110475801)
          ·
            refine ⟨120591663378197207332856851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160788884504262943110475801 120591663378197207332856851)
            ·
              refine ⟨180887495067295810999285277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120591663378197207332856851 180887495067295810999285277)
              ·
                refine ⟨67832810650235929124731979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180887495067295810999285277 67832810650235929124731979)
                ·
                  refine ⟨101749215975353893687097969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67832810650235929124731979 101749215975353893687097969)
                  ·
                    refine ⟨76311911981515420265323477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101749215975353893687097969 76311911981515420265323477)
                    ·
                      refine ⟨1788560437066767662468519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76311911981515420265323477 1788560437066767662468519)
                      ·
                        rfl

theorem cell23_3483209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_3483209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483209 prefixEnd_3483209 := by exact prefixLift 3483209
  have htrace : WordTrace (prefixWord ++ tailWord_3483209) baseStart_3483209 baseEnd_3483209 := by
    simpa [prefixWord, tailWord_3483209, baseEnd_3483209] using wordTrace_append hprefix tailTrace_3483209
  have hstable : (prefixWord ++ tailWord_3483209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483209).length < 2 ^ (prefixWord ++ tailWord_3483209).sum := by decide
  have hdescent : baseEnd_3483209 < baseStart_3483209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483250 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_3483250 : Nat := 118140960795 + 3483250 * 2 ^ 59
def prefixEnd_3483250 : Nat := 4983230072969 + 3 ^ 40 * 3483250 * 2
def baseEnd_3483250 : Nat := 198731276641511333561759

theorem tailTrace_3483250 : CollatzResearch.WordTrace tailWord_3483250 prefixEnd_3483250 198731276641511333561759 := by
  unfold tailWord_3483250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31761141157696904145839801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84696376420525077722239469 31761141157696904145839801)
  ·
    refine ⟨23820855868272678109379851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31761141157696904145839801 23820855868272678109379851)
    ·
      refine ⟨35731283802409017164069777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23820855868272678109379851 35731283802409017164069777)
      ·
        refine ⟨26798462851806762873052333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35731283802409017164069777 26798462851806762873052333)
        ·
          refine ⟨10049423569427536077394625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26798462851806762873052333 10049423569427536077394625)
          ·
            refine ⟨7537067677070652058045969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10049423569427536077394625 7537067677070652058045969)
            ·
              refine ⟨5652800757802989043534477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537067677070652058045969 5652800757802989043534477)
              ·
                refine ⟨2119800284176120891325429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5652800757802989043534477 2119800284176120891325429)
                ·
                  refine ⟨198731276641511333561759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2119800284176120891325429 198731276641511333561759)
                  ·
                    rfl

theorem cell23_3483250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_3483250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483250 prefixEnd_3483250 := by exact prefixLift 3483250
  have htrace : WordTrace (prefixWord ++ tailWord_3483250) baseStart_3483250 baseEnd_3483250 := by
    simpa [prefixWord, tailWord_3483250, baseEnd_3483250] using wordTrace_append hprefix tailTrace_3483250
  have hstable : (prefixWord ++ tailWord_3483250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483250).length < 2 ^ (prefixWord ++ tailWord_3483250).sum := by decide
  have hdescent : baseEnd_3483250 < baseStart_3483250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483327 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 1, 4]
def baseStart_3483327 : Nat := 118140960795 + 3483327 * 2 ^ 59
def prefixEnd_3483327 : Nat := 4983230072969 + 3 ^ 40 * 3483327 * 2
def baseEnd_3483327 : Nat := 596207009261332733597659

theorem tailTrace_3483327 : CollatzResearch.WordTrace tailWord_3483327 prefixEnd_3483327 596207009261332733597659 := by
  unfold tailWord_3483327
  simp only [CollatzResearch.WordTrace]
  refine ⟨127047373051508658733912235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84698248701005772489274823 127047373051508658733912235)
  ·
    refine ⟨190571059577262988100868353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127047373051508658733912235 190571059577262988100868353)
    ·
      refine ⟨142928294682947241075651265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190571059577262988100868353 142928294682947241075651265)
      ·
        refine ⟨107196221012210430806738449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142928294682947241075651265 107196221012210430806738449)
        ·
          refine ⟨80397165759157823105053837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107196221012210430806738449 80397165759157823105053837)
          ·
            refine ⟨30148937159684183664395189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80397165759157823105053837 30148937159684183664395189)
            ·
              refine ⟨2826462858720392218537049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30148937159684183664395189 2826462858720392218537049)
              ·
                refine ⟨2119847144040294163902787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826462858720392218537049 2119847144040294163902787)
                ·
                  refine ⟨3179770716060441245854181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119847144040294163902787 3179770716060441245854181)
                  ·
                    refine ⟨596207009261332733597659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179770716060441245854181 596207009261332733597659)
                    ·
                      rfl

theorem cell23_3483327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 4].length) (baseStart_3483327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483327 prefixEnd_3483327 := by exact prefixLift 3483327
  have htrace : WordTrace (prefixWord ++ tailWord_3483327) baseStart_3483327 baseEnd_3483327 := by
    simpa [prefixWord, tailWord_3483327, baseEnd_3483327] using wordTrace_append hprefix tailTrace_3483327
  have hstable : (prefixWord ++ tailWord_3483327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483327).length < 2 ^ (prefixWord ++ tailWord_3483327).sum := by decide
  have hdescent : baseEnd_3483327 < baseStart_3483327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483340 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 6]
def baseStart_3483340 : Nat := 118140960795 + 3483340 * 2 ^ 59
def prefixEnd_3483340 : Nat := 4983230072969 + 3 ^ 40 * 3483340 * 2
def baseEnd_3483340 : Nat := 198736411448056294436713

theorem tailTrace_3483340 : CollatzResearch.WordTrace tailWord_3483340 prefixEnd_3483340 198736411448056294436713 := by
  unfold tailWord_3483340
  simp only [CollatzResearch.WordTrace]
  refine ⟨63523923600230780977067737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84698564800307707969423649 63523923600230780977067737)
  ·
    refine ⟨47642942700173085732800803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63523923600230780977067737 47642942700173085732800803)
    ·
      refine ⟨71464414050259628599201205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47642942700173085732800803 71464414050259628599201205)
      ·
        refine ⟨6699788817211840181175113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71464414050259628599201205 6699788817211840181175113)
        ·
          refine ⟨5024841612908880135881335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699788817211840181175113 5024841612908880135881335)
          ·
            refine ⟨7537262419363320203822003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024841612908880135881335 7537262419363320203822003)
            ·
              refine ⟨11305893629044980305733005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537262419363320203822003 11305893629044980305733005)
              ·
                refine ⟨4239710110891867614649877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11305893629044980305733005 4239710110891867614649877)
                ·
                  refine ⟨198736411448056294436713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4239710110891867614649877 198736411448056294436713)
                  ·
                    rfl

theorem cell23_3483340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_3483340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483340 prefixEnd_3483340 := by exact prefixLift 3483340
  have htrace : WordTrace (prefixWord ++ tailWord_3483340) baseStart_3483340 baseEnd_3483340 := by
    simpa [prefixWord, tailWord_3483340, baseEnd_3483340] using wordTrace_append hprefix tailTrace_3483340
  have hstable : (prefixWord ++ tailWord_3483340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483340).length < 2 ^ (prefixWord ++ tailWord_3483340).sum := by decide
  have hdescent : baseEnd_3483340 < baseStart_3483340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483343 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 3, 5, 2]
def baseStart_3483343 : Nat := 118140960795 + 3483343 * 2 ^ 59
def prefixEnd_3483343 : Nat := 4983230072969 + 3 ^ 40 * 3483343 * 2
def baseEnd_3483343 : Nat := 1788629243474470138192903

theorem tailTrace_3483343 : CollatzResearch.WordTrace tailWord_3483343 prefixEnd_3483343 1788629243474470138192903 := by
  unfold tailWord_3483343
  simp only [CollatzResearch.WordTrace]
  refine ⟨127047956619450693466494683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84698637746300462310996455 127047956619450693466494683)
  ·
    refine ⟨190571934929176040199742025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127047956619450693466494683 190571934929176040199742025)
    ·
      refine ⟨142928951196882030149806519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190571934929176040199742025 142928951196882030149806519)
      ·
        refine ⟨214393426795323045224709779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142928951196882030149806519 214393426795323045224709779)
        ·
          refine ⟨321590140192984567837064669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214393426795323045224709779 321590140192984567837064669)
          ·
            refine ⟨120596302572369212938899251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321590140192984567837064669 120596302572369212938899251)
            ·
              refine ⟨180894453858553819408348877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120596302572369212938899251 180894453858553819408348877)
              ·
                refine ⟨67835420196957682278130829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180894453858553819408348877 67835420196957682278130829)
                ·
                  refine ⟨25438282573859130854299061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67835420196957682278130829 25438282573859130854299061)
                  ·
                    refine ⟨2384838991299293517590537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25438282573859130854299061 2384838991299293517590537)
                    ·
                      refine ⟨1788629243474470138192903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384838991299293517590537 1788629243474470138192903)
                      ·
                        rfl

theorem cell23_3483343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5, 2].length) (baseStart_3483343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483343 prefixEnd_3483343 := by exact prefixLift 3483343
  have htrace : WordTrace (prefixWord ++ tailWord_3483343) baseStart_3483343 baseEnd_3483343 := by
    simpa [prefixWord, tailWord_3483343, baseEnd_3483343] using wordTrace_append hprefix tailTrace_3483343
  have hstable : (prefixWord ++ tailWord_3483343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483343).length < 2 ^ (prefixWord ++ tailWord_3483343).sum := by decide
  have hdescent : baseEnd_3483343 < baseStart_3483343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483353 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_3483353 : Nat := 118140960795 + 3483353 * 2 ^ 59
def prefixEnd_3483353 : Nat := 4983230072969 + 3 ^ 40 * 3483353 * 2
def baseEnd_3483353 : Nat := 596211459427005033022619

theorem tailTrace_3483353 : CollatzResearch.WordTrace tailWord_3483353 prefixEnd_3483353 596211459427005033022619 := by
  unfold tailWord_3483353
  simp only [CollatzResearch.WordTrace]
  refine ⟨127048321349414465174358713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84698880899609643449572475 127048321349414465174358713)
  ·
    refine ⟨95286241012060848880769035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127048321349414465174358713 95286241012060848880769035)
    ·
      refine ⟨142929361518091273321153553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95286241012060848880769035 142929361518091273321153553)
      ·
        refine ⟨107197021138568454990865165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142929361518091273321153553 107197021138568454990865165)
        ·
          refine ⟨40198882926963170621574437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107197021138568454990865165 40198882926963170621574437)
          ·
            refine ⟨7537290548805594491545207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40198882926963170621574437 7537290548805594491545207)
            ·
              refine ⟨11305935823208391737317811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537290548805594491545207 11305935823208391737317811)
              ·
                refine ⟨16958903734812587605976717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305935823208391737317811 16958903734812587605976717)
                ·
                  refine ⟨6359588900554720352241269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16958903734812587605976717 6359588900554720352241269)
                  ·
                    refine ⟨596211459427005033022619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6359588900554720352241269 596211459427005033022619)
                    ·
                      rfl

theorem cell23_3483353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_3483353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483353 prefixEnd_3483353 := by exact prefixLift 3483353
  have htrace : WordTrace (prefixWord ++ tailWord_3483353) baseStart_3483353 baseEnd_3483353 := by
    simpa [prefixWord, tailWord_3483353, baseEnd_3483353] using wordTrace_append hprefix tailTrace_3483353
  have hstable : (prefixWord ++ tailWord_3483353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483353).length < 2 ^ (prefixWord ++ tailWord_3483353).sum := by decide
  have hdescent : baseEnd_3483353 < baseStart_3483353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483360 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 2, 3, 2]
def baseStart_3483360 : Nat := 118140960795 + 3483360 * 2 ^ 59
def prefixEnd_3483360 : Nat := 4983230072969 + 3 ^ 40 * 3483360 * 2
def baseEnd_3483360 : Nat := 1788637972645596571680325

theorem tailTrace_3483360 : CollatzResearch.WordTrace tailWord_3483360 prefixEnd_3483360 1788637972645596571680325 := by
  unfold tailWord_3483360
  simp only [CollatzResearch.WordTrace]
  refine ⟨63524288330194552684931767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84699051106926070246575689 63524288330194552684931767)
  ·
    refine ⟨95286432495291829027397651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63524288330194552684931767 95286432495291829027397651)
    ·
      refine ⟨142929648742937743541096477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95286432495291829027397651 142929648742937743541096477)
      ·
        refine ⟨53598618278601653827911179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142929648742937743541096477 53598618278601653827911179)
        ·
          refine ⟨80397927417902480741866769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53598618278601653827911179 80397927417902480741866769)
          ·
            refine ⟨60298445563426860556400077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80397927417902480741866769 60298445563426860556400077)
            ·
              refine ⟨22611917086285072708650029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60298445563426860556400077 22611917086285072708650029)
              ·
                refine ⟨8479468907356902265743761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22611917086285072708650029 8479468907356902265743761)
                ·
                  refine ⟨6359601680517676699307821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479468907356902265743761 6359601680517676699307821)
                  ·
                    refine ⟨2384850630194128762240433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6359601680517676699307821 2384850630194128762240433)
                    ·
                      refine ⟨1788637972645596571680325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384850630194128762240433 1788637972645596571680325)
                      ·
                        rfl

theorem cell23_3483360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_3483360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483360 prefixEnd_3483360 := by exact prefixLift 3483360
  have htrace : WordTrace (prefixWord ++ tailWord_3483360) baseStart_3483360 baseEnd_3483360 := by
    simpa [prefixWord, tailWord_3483360, baseEnd_3483360] using wordTrace_append hprefix tailTrace_3483360
  have hstable : (prefixWord ++ tailWord_3483360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483360).length < 2 ^ (prefixWord ++ tailWord_3483360).sum := by decide
  have hdescent : baseEnd_3483360 < baseStart_3483360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483383 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 4, 4]
def baseStart_3483383 : Nat := 118140960795 + 3483383 * 2 ^ 59
def prefixEnd_3483383 : Nat := 4983230072969 + 3 ^ 40 * 3483383 * 2
def baseEnd_3483383 : Nat := 596216594233549993897573

theorem tailTrace_3483383 : CollatzResearch.WordTrace tailWord_3483383 prefixEnd_3483383 596216594233549993897573 := by
  unfold tailWord_3483383
  simp only [CollatzResearch.WordTrace]
  refine ⟨127049415539305780297950803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84699610359537186865300535 127049415539305780297950803)
  ·
    refine ⟨190574123308958670446926205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127049415539305780297950803 190574123308958670446926205)
    ·
      refine ⟨71465296240859501417597327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190574123308958670446926205 71465296240859501417597327)
      ·
        refine ⟨107197944361289252126395991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71465296240859501417597327 107197944361289252126395991)
        ·
          refine ⟨160796916541933878189593987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107197944361289252126395991 160796916541933878189593987)
          ·
            refine ⟨241195374812900817284390981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160796916541933878189593987 241195374812900817284390981)
            ·
              refine ⟨45224132777418903240823309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241195374812900817284390981 45224132777418903240823309)
              ·
                refine ⟨16959049791532088715308741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45224132777418903240823309 16959049791532088715308741)
                ·
                  refine ⟨3179821835912266634120389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16959049791532088715308741 3179821835912266634120389)
                  ·
                    refine ⟨596216594233549993897573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179821835912266634120389 596216594233549993897573)
                    ·
                      rfl

theorem cell23_3483383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_3483383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483383 prefixEnd_3483383 := by exact prefixLift 3483383
  have htrace : WordTrace (prefixWord ++ tailWord_3483383) baseStart_3483383 baseEnd_3483383 := by
    simpa [prefixWord, tailWord_3483383, baseEnd_3483383] using wordTrace_append hprefix tailTrace_3483383
  have hstable : (prefixWord ++ tailWord_3483383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483383).length < 2 ^ (prefixWord ++ tailWord_3483383).sum := by decide
  have hdescent : baseEnd_3483383 < baseStart_3483383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483393 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3483393 : Nat := 118140960795 + 3483393 * 2 ^ 59
def prefixEnd_3483393 : Nat := 4983230072969 + 3 ^ 40 * 3483393 * 2
def baseEnd_3483393 : Nat := 1788654917507194942567673

theorem tailTrace_3483393 : CollatzResearch.WordTrace tailWord_3483393 prefixEnd_3483393 1788654917507194942567673 := by
  unfold tailWord_3483393
  simp only [CollatzResearch.WordTrace]
  refine ⟨127049780269269552005814833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84699853512846368003876555 127049780269269552005814833)
  ·
    refine ⟨95287335201952164004361125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127049780269269552005814833 95287335201952164004361125)
    ·
      refine ⟨17866375350366030750817711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95287335201952164004361125 17866375350366030750817711)
      ·
        refine ⟨26799563025549046126226567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17866375350366030750817711 26799563025549046126226567)
        ·
          refine ⟨40199344538323569189339851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26799563025549046126226567 40199344538323569189339851)
          ·
            refine ⟨60299016807485353784009777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40199344538323569189339851 60299016807485353784009777)
            ·
              refine ⟨45224262605614015338007333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60299016807485353784009777 45224262605614015338007333)
              ·
                refine ⟨8479549238552627875876375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45224262605614015338007333 8479549238552627875876375)
                ·
                  refine ⟨12719323857828941813814563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8479549238552627875876375 12719323857828941813814563)
                  ·
                    refine ⟨19078985786743412720721845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12719323857828941813814563 19078985786743412720721845)
                    ·
                      refine ⟨1788654917507194942567673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19078985786743412720721845 1788654917507194942567673)
                      ·
                        rfl

theorem cell23_3483393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3483393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483393 prefixEnd_3483393 := by exact prefixLift 3483393
  have htrace : WordTrace (prefixWord ++ tailWord_3483393) baseStart_3483393 baseEnd_3483393 := by
    simpa [prefixWord, tailWord_3483393, baseEnd_3483393] using wordTrace_append hprefix tailTrace_3483393
  have hstable : (prefixWord ++ tailWord_3483393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483393).length < 2 ^ (prefixWord ++ tailWord_3483393).sum := by decide
  have hdescent : baseEnd_3483393 < baseStart_3483393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483400 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 2, 4]
def baseStart_3483400 : Nat := 118140960795 + 3483400 * 2 ^ 59
def prefixEnd_3483400 : Nat := 4983230072969 + 3 ^ 40 * 3483400 * 2
def baseEnd_3483400 : Nat := 596219503957258805060047

theorem tailTrace_3483400 : CollatzResearch.WordTrace tailWord_3483400 prefixEnd_3483400 596219503957258805060047 := by
  unfold tailWord_3483400
  simp only [CollatzResearch.WordTrace]
  refine ⟨63525017790122096100659827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84700023720162794800879769 63525017790122096100659827)
  ·
    refine ⟨95287526685183144150989741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63525017790122096100659827 95287526685183144150989741)
    ·
      refine ⟨35732822506943679056621153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95287526685183144150989741 35732822506943679056621153)
      ·
        refine ⟨26799616880207759292465865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35732822506943679056621153 26799616880207759292465865)
        ·
          refine ⟨20099712660155819469349399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26799616880207759292465865 20099712660155819469349399)
          ·
            refine ⟨30149568990233729204024099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20099712660155819469349399 30149568990233729204024099)
            ·
              refine ⟨45224353485350593806036149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30149568990233729204024099 45224353485350593806036149)
              ·
                refine ⟨4239783139251618169315889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45224353485350593806036149 4239783139251618169315889)
                ·
                  refine ⟨3179837354438713626986917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239783139251618169315889 3179837354438713626986917)
                  ·
                    refine ⟨596219503957258805060047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179837354438713626986917 596219503957258805060047)
                    ·
                      rfl

theorem cell23_3483400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_3483400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483400 prefixEnd_3483400 := by exact prefixLift 3483400
  have htrace : WordTrace (prefixWord ++ tailWord_3483400) baseStart_3483400 baseEnd_3483400 := by
    simpa [prefixWord, tailWord_3483400, baseEnd_3483400] using wordTrace_append hprefix tailTrace_3483400
  have hstable : (prefixWord ++ tailWord_3483400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483400).length < 2 ^ (prefixWord ++ tailWord_3483400).sum := by decide
  have hdescent : baseEnd_3483400 < baseStart_3483400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483403 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4]
def baseStart_3483403 : Nat := 118140960795 + 3483403 * 2 ^ 59
def prefixEnd_3483403 : Nat := 4983230072969 + 3 ^ 40 * 3483403 * 2
def baseEnd_3483403 : Nat := 1788660052313739903442627

theorem tailTrace_3483403 : CollatzResearch.WordTrace tailWord_3483403 prefixEnd_3483403 1788660052313739903442627 := by
  unfold tailWord_3483403
  simp only [CollatzResearch.WordTrace]
  refine ⟨127050144999233323713678863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84700096666155549142452575 127050144999233323713678863)
  ·
    refine ⟨190575217498849985570518295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127050144999233323713678863 190575217498849985570518295)
    ·
      refine ⟨285862826248274978355777443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190575217498849985570518295 285862826248274978355777443)
      ·
        refine ⟨428794239372412467533666165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285862826248274978355777443 428794239372412467533666165)
        ·
          refine ⟨40199459941163668831281203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 428794239372412467533666165 40199459941163668831281203)
          ·
            refine ⟨60299189911745503246921805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40199459941163668831281203 60299189911745503246921805)
            ·
              refine ⟨22612196216904563717595677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60299189911745503246921805 22612196216904563717595677)
              ·
                refine ⟨8479573581339211394098379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22612196216904563717595677 8479573581339211394098379)
                ·
                  refine ⟨12719360372008817091147569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8479573581339211394098379 12719360372008817091147569)
                  ·
                    refine ⟨9539520279006612818360677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12719360372008817091147569 9539520279006612818360677)
                    ·
                      refine ⟨1788660052313739903442627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9539520279006612818360677 1788660052313739903442627)
                      ·
                        rfl

theorem cell23_3483403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].length) (baseStart_3483403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483403 prefixEnd_3483403 := by exact prefixLift 3483403
  have htrace : WordTrace (prefixWord ++ tailWord_3483403) baseStart_3483403 baseEnd_3483403 := by
    simpa [prefixWord, tailWord_3483403, baseEnd_3483403] using wordTrace_append hprefix tailTrace_3483403
  have hstable : (prefixWord ++ tailWord_3483403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483403).length < 2 ^ (prefixWord ++ tailWord_3483403).sum := by decide
  have hdescent : baseEnd_3483403 < baseStart_3483403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483405 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3483405 : Nat := 118140960795 + 3483405 * 2 ^ 59
def prefixEnd_3483405 : Nat := 4983230072969 + 3 ^ 40 * 3483405 * 2
def baseEnd_3483405 : Nat := 1788661079275048895617619

theorem tailTrace_3483405 : CollatzResearch.WordTrace tailWord_3483405 prefixEnd_3483405 1788661079275048895617619 := by
  unfold tailWord_3483405
  simp only [CollatzResearch.WordTrace]
  refine ⟨127050217945226078055251669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84700145296817385370167779 127050217945226078055251669)
  ·
    refine ⟨2977739483091236204419961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127050217945226078055251669 2977739483091236204419961)
    ·
      refine ⟨2233304612318427153314971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2977739483091236204419961 2233304612318427153314971)
      ·
        refine ⟨3349956918477640729972457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233304612318427153314971 3349956918477640729972457)
        ·
          refine ⟨2512467688858230547479343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349956918477640729972457 2512467688858230547479343)
          ·
            refine ⟨3768701533287345821219015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512467688858230547479343 3768701533287345821219015)
            ·
              refine ⟨5653052299931018731828523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3768701533287345821219015 5653052299931018731828523)
              ·
                refine ⟨8479578449896528097742785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653052299931018731828523 8479578449896528097742785)
                ·
                  refine ⟨6359683837422396073307089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479578449896528097742785 6359683837422396073307089)
                  ·
                    refine ⟨4769762878066797054980317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6359683837422396073307089 4769762878066797054980317)
                    ·
                      refine ⟨1788661079275048895617619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769762878066797054980317 1788661079275048895617619)
                      ·
                        rfl

theorem cell23_3483405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3483405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483405 prefixEnd_3483405 := by exact prefixLift 3483405
  have htrace : WordTrace (prefixWord ++ tailWord_3483405) baseStart_3483405 baseEnd_3483405 := by
    simpa [prefixWord, tailWord_3483405, baseEnd_3483405] using wordTrace_append hprefix tailTrace_3483405
  have hstable : (prefixWord ++ tailWord_3483405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483405).length < 2 ^ (prefixWord ++ tailWord_3483405).sum := by decide
  have hdescent : baseEnd_3483405 < baseStart_3483405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483427 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 1, 2, 3]
def baseStart_3483427 : Nat := 118140960795 + 3483427 * 2 ^ 59
def prefixEnd_3483427 : Nat := 4983230072969 + 3 ^ 40 * 3483427 * 2
def baseEnd_3483427 : Nat := 1788672375849447809542517

theorem tailTrace_3483427 : CollatzResearch.WordTrace tailWord_3483427 prefixEnd_3483427 1788672375849447809542517 := by
  unfold tailWord_3483427
  simp only [CollatzResearch.WordTrace]
  refine ⟨127051020351146375812552535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84700680234097583875035023 127051020351146375812552535)
  ·
    refine ⟨190576530526719563718828803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127051020351146375812552535 190576530526719563718828803)
    ·
      refine ⟨285864795790079345578243205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190576530526719563718828803 285864795790079345578243205)
      ·
        refine ⟨53599649210639877295920601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285864795790079345578243205 53599649210639877295920601)
        ·
          refine ⟨40199736907979907971940451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53599649210639877295920601 40199736907979907971940451)
          ·
            refine ⟨60299605361969861957910677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40199736907979907971940451 60299605361969861957910677)
            ·
              refine ⟨2826544001342337279277063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60299605361969861957910677 2826544001342337279277063)
              ·
                refine ⟨4239816002013505918915595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826544001342337279277063 4239816002013505918915595)
                ·
                  refine ⟨6359724003020258878373393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239816002013505918915595 6359724003020258878373393)
                  ·
                    refine ⟨4769793002265194158780045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6359724003020258878373393 4769793002265194158780045)
                    ·
                      refine ⟨1788672375849447809542517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769793002265194158780045 1788672375849447809542517)
                      ·
                        rfl

theorem cell23_3483427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_3483427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483427 prefixEnd_3483427 := by exact prefixLift 3483427
  have htrace : WordTrace (prefixWord ++ tailWord_3483427) baseStart_3483427 baseEnd_3483427 := by
    simpa [prefixWord, tailWord_3483427, baseEnd_3483427] using wordTrace_append hprefix tailTrace_3483427
  have hstable : (prefixWord ++ tailWord_3483427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483427).length < 2 ^ (prefixWord ++ tailWord_3483427).sum := by decide
  have hdescent : baseEnd_3483427 < baseStart_3483427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483463 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3483463 : Nat := 118140960795 + 3483463 * 2 ^ 59
def prefixEnd_3483463 : Nat := 4983230072969 + 3 ^ 40 * 3483463 * 2
def baseEnd_3483463 : Nat := 1788690861153009668692351

theorem tailTrace_3483463 : CollatzResearch.WordTrace tailWord_3483463 prefixEnd_3483463 1788690861153009668692351 := by
  unfold tailWord_3483463
  simp only [CollatzResearch.WordTrace]
  refine ⟨127052333379015953960863043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84701555586010635973908695 127052333379015953960863043)
  ·
    refine ⟨190578500068523930941294565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127052333379015953960863043 190578500068523930941294565)
    ·
      refine ⟨35733468762848237051492731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190578500068523930941294565 35733468762848237051492731)
      ·
        refine ⟨53600203144272355577239097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35733468762848237051492731 53600203144272355577239097)
        ·
          refine ⟨40200152358204266682929323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53600203144272355577239097 40200152358204266682929323)
          ·
            refine ⟨60300228537306400024393985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40200152358204266682929323 60300228537306400024393985)
            ·
              refine ⟨45225171402979800018295489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60300228537306400024393985 45225171402979800018295489)
              ·
                refine ⟨33918878552234850013721617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45225171402979800018295489 33918878552234850013721617)
                ·
                  refine ⟨25439158914176137510291213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33918878552234850013721617 25439158914176137510291213)
                  ·
                    refine ⟨9539684592816051566359205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25439158914176137510291213 9539684592816051566359205)
                    ·
                      refine ⟨1788690861153009668692351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9539684592816051566359205 1788690861153009668692351)
                      ·
                        rfl

theorem cell23_3483463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3483463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483463 prefixEnd_3483463 := by exact prefixLift 3483463
  have htrace : WordTrace (prefixWord ++ tailWord_3483463) baseStart_3483463 baseEnd_3483463 := by
    simpa [prefixWord, tailWord_3483463, baseEnd_3483463] using wordTrace_append hprefix tailTrace_3483463
  have hstable : (prefixWord ++ tailWord_3483463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483463).length < 2 ^ (prefixWord ++ tailWord_3483463).sum := by decide
  have hdescent : baseEnd_3483463 < baseStart_3483463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483518 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3483518 : Nat := 118140960795 + 3483518 * 2 ^ 59
def prefixEnd_3483518 : Nat := 4983230072969 + 3 ^ 40 * 3483518 * 2
def baseEnd_3483518 : Nat := 1788719102589006953504599

theorem tailTrace_3483518 : CollatzResearch.WordTrace tailWord_3483518 prefixEnd_3483518 1788719102589006953504599 := by
  unfold tailWord_3483518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881792424227087294264401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84702892929211132236076805 15881792424227087294264401)
  ·
    refine ⟨11911344318170315470698301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15881792424227087294264401 11911344318170315470698301)
    ·
      refine ⟨4466754119313868301511863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11911344318170315470698301 4466754119313868301511863)
      ·
        refine ⟨6700131178970802452267795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466754119313868301511863 6700131178970802452267795)
        ·
          refine ⟨10050196768456203678401693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700131178970802452267795 10050196768456203678401693)
          ·
            refine ⟨3768823788171076379400635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10050196768456203678401693 3768823788171076379400635)
            ·
              refine ⟨5653235682256614569100953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3768823788171076379400635 5653235682256614569100953)
              ·
                refine ⟨4239926761692460926825715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653235682256614569100953 4239926761692460926825715)
                ·
                  refine ⟨6359890142538691390238573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239926761692460926825715 6359890142538691390238573)
                  ·
                    refine ⟨2384958803452009271339465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6359890142538691390238573 2384958803452009271339465)
                    ·
                      refine ⟨1788719102589006953504599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384958803452009271339465 1788719102589006953504599)
                      ·
                        rfl

theorem cell23_3483518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3483518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483518 prefixEnd_3483518 := by exact prefixLift 3483518
  have htrace : WordTrace (prefixWord ++ tailWord_3483518) baseStart_3483518 baseEnd_3483518 := by
    simpa [prefixWord, tailWord_3483518, baseEnd_3483518] using wordTrace_append hprefix tailTrace_3483518
  have hstable : (prefixWord ++ tailWord_3483518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483518).length < 2 ^ (prefixWord ++ tailWord_3483518).sum := by decide
  have hdescent : baseEnd_3483518 < baseStart_3483518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483554 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_3483554 : Nat := 118140960795 + 3483554 * 2 ^ 59
def prefixEnd_3483554 : Nat := 4983230072969 + 3 ^ 40 * 3483554 * 2
def baseEnd_3483554 : Nat := 198748620876952090294937

theorem tailTrace_3483554 : CollatzResearch.WordTrace tailWord_3483554 prefixEnd_3483554 198748620876952090294937 := by
  unfold tailWord_3483554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763913105421569125606429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84703768281124184334950477 31763913105421569125606429)
  ·
    refine ⟨11911467414533088422102411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31763913105421569125606429 11911467414533088422102411)
    ·
      refine ⟨17867201121799632633153617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11911467414533088422102411 17867201121799632633153617)
      ·
        refine ⟨13400400841349724474865213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17867201121799632633153617 13400400841349724474865213)
        ·
          refine ⟨5025150315506146678074455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13400400841349724474865213 5025150315506146678074455)
          ·
            refine ⟨7537725473259220017111683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025150315506146678074455 7537725473259220017111683)
            ·
              refine ⟨11306588209888830025667525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537725473259220017111683 11306588209888830025667525)
              ·
                refine ⟨2119985289354155629812661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11306588209888830025667525 2119985289354155629812661)
                ·
                  refine ⟨198748620876952090294937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2119985289354155629812661 198748620876952090294937)
                  ·
                    rfl

theorem cell23_3483554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_3483554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483554 prefixEnd_3483554 := by exact prefixLift 3483554
  have htrace : WordTrace (prefixWord ++ tailWord_3483554) baseStart_3483554 baseEnd_3483554 := by
    simpa [prefixWord, tailWord_3483554, baseEnd_3483554] using wordTrace_append hprefix tailTrace_3483554
  have hstable : (prefixWord ++ tailWord_3483554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483554).length < 2 ^ (prefixWord ++ tailWord_3483554).sum := by decide
  have hdescent : baseEnd_3483554 < baseStart_3483554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483570 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_3483570 : Nat := 118140960795 + 3483570 * 2 ^ 59
def prefixEnd_3483570 : Nat := 4983230072969 + 3 ^ 40 * 3483570 * 2
def baseEnd_3483570 : Nat := 1788745803583040750054359

theorem tailTrace_3483570 : CollatzResearch.WordTrace tailWord_3483570 prefixEnd_3483570 1788745803583040750054359 := by
  unfold tailWord_3483570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31764058997407077808752041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84704157326418874156672109 31764058997407077808752041)
  ·
    refine ⟨23823044248055308356564031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31764058997407077808752041 23823044248055308356564031)
    ·
      refine ⟨35734566372082962534846047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23823044248055308356564031 35734566372082962534846047)
      ·
        refine ⟨53601849558124443802269071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35734566372082962534846047 53601849558124443802269071)
        ·
          refine ⟨80402774337186665703403607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53601849558124443802269071 80402774337186665703403607)
          ·
            refine ⟨120604161505779998555105411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80402774337186665703403607 120604161505779998555105411)
            ·
              refine ⟨180906242258669997832658117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120604161505779998555105411 180906242258669997832658117)
              ·
                refine ⟨33919920423500624593623397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180906242258669997832658117 33919920423500624593623397)
                ·
                  refine ⟨6359985079406367111304387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33919920423500624593623397 6359985079406367111304387)
                  ·
                    refine ⟨9539977619109550666956581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6359985079406367111304387 9539977619109550666956581)
                    ·
                      refine ⟨1788745803583040750054359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9539977619109550666956581 1788745803583040750054359)
                      ·
                        rfl

theorem cell23_3483570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_3483570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483570 prefixEnd_3483570 := by exact prefixLift 3483570
  have htrace : WordTrace (prefixWord ++ tailWord_3483570) baseStart_3483570 baseEnd_3483570 := by
    simpa [prefixWord, tailWord_3483570, baseEnd_3483570] using wordTrace_append hprefix tailTrace_3483570
  have hstable : (prefixWord ++ tailWord_3483570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483570).length < 2 ^ (prefixWord ++ tailWord_3483570).sum := by decide
  have hdescent : baseEnd_3483570 < baseStart_3483570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483593 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 10]
def baseStart_3483593 : Nat := 118140960795 + 3483593 * 2 ^ 59
def prefixEnd_3483593 : Nat := 4983230072969 + 3 ^ 40 * 3483593 * 2
def baseEnd_3483593 : Nat := 198750845959788240007417

theorem tailTrace_3483593 : CollatzResearch.WordTrace tailWord_3483593 prefixEnd_3483593 198750845959788240007417 := by
  unfold tailWord_3483593
  simp only [CollatzResearch.WordTrace]
  refine ⟨127057074868544986163095433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84704716579029990775396955 127057074868544986163095433)
  ·
    refine ⟨95292806151408739622321575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127057074868544986163095433 95292806151408739622321575)
    ·
      refine ⟨142939209227113109433482363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95292806151408739622321575 142939209227113109433482363)
      ·
        refine ⟨214408813840669664150223545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142939209227113109433482363 214408813840669664150223545)
        ·
          refine ⟨160806610380502248112667659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214408813840669664150223545 160806610380502248112667659)
          ·
            refine ⟨241209915570753372169001489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160806610380502248112667659 241209915570753372169001489)
            ·
              refine ⟨180907436678065029126751117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241209915570753372169001489 180907436678065029126751117)
              ·
                refine ⟨67840288754274385922531669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180907436678065029126751117 67840288754274385922531669)
                ·
                  refine ⟨198750845959788240007417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67840288754274385922531669 198750845959788240007417)
                  ·
                    rfl

theorem cell23_3483593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_3483593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483593 prefixEnd_3483593 := by exact prefixLift 3483593
  have htrace : WordTrace (prefixWord ++ tailWord_3483593) baseStart_3483593 baseEnd_3483593 := by
    simpa [prefixWord, tailWord_3483593, baseEnd_3483593] using wordTrace_append hprefix tailTrace_3483593
  have hstable : (prefixWord ++ tailWord_3483593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483593).length < 2 ^ (prefixWord ++ tailWord_3483593).sum := by decide
  have hdescent : baseEnd_3483593 < baseStart_3483593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483603 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_3483603 : Nat := 118140960795 + 3483603 * 2 ^ 59
def prefixEnd_3483603 : Nat := 4983230072969 + 3 ^ 40 * 3483603 * 2
def baseEnd_3483603 : Nat := 1788762748444639120941707

theorem tailTrace_3483603 : CollatzResearch.WordTrace tailWord_3483603 prefixEnd_3483603 1788762748444639120941707 := by
  unfold tailWord_3483603
  simp only [CollatzResearch.WordTrace]
  refine ⟨127057439598508757870959463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84704959732339171913972975 127057439598508757870959463)
  ·
    refine ⟨190586159397763136806439195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127057439598508757870959463 190586159397763136806439195)
    ·
      refine ⟨285879239096644705209658793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190586159397763136806439195 285879239096644705209658793)
      ·
        refine ⟨214409429322483528907244095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285879239096644705209658793 214409429322483528907244095)
        ·
          refine ⟨321614143983725293360866143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214409429322483528907244095 321614143983725293360866143)
          ·
            refine ⟨482421215975587940041299215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321614143983725293360866143 482421215975587940041299215)
            ·
              refine ⟨723631823963381910061948823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482421215975587940041299215 723631823963381910061948823)
              ·
                refine ⟨1085447735945072865092923235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723631823963381910061948823 1085447735945072865092923235)
                ·
                  refine ⟨1628171603917609297639384853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085447735945072865092923235 1628171603917609297639384853)
                  ·
                    refine ⟨76320543933637935826846165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1628171603917609297639384853 76320543933637935826846165)
                    ·
                      refine ⟨1788762748444639120941707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76320543933637935826846165 1788762748444639120941707)
                      ·
                        rfl

theorem cell23_3483603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_3483603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483603 prefixEnd_3483603 := by exact prefixLift 3483603
  have htrace : WordTrace (prefixWord ++ tailWord_3483603) baseStart_3483603 baseEnd_3483603 := by
    simpa [prefixWord, tailWord_3483603, baseEnd_3483603] using wordTrace_append hprefix tailTrace_3483603
  have hstable : (prefixWord ++ tailWord_3483603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483603).length < 2 ^ (prefixWord ++ tailWord_3483603).sum := by decide
  have hdescent : baseEnd_3483603 < baseStart_3483603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483640 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_3483640 : Nat := 118140960795 + 3483640 * 2 ^ 59
def prefixEnd_3483640 : Nat := 4983230072969 + 3 ^ 40 * 3483640 * 2
def baseEnd_3483640 : Nat := 596260582409618492059679

theorem tailTrace_3483640 : CollatzResearch.WordTrace tailWord_3483640 prefixEnd_3483640 596260582409618492059679 := by
  unfold tailWord_3483640
  simp only [CollatzResearch.WordTrace]
  refine ⟨63529394549687356595028187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84705859399583142126704249 63529394549687356595028187)
  ·
    refine ⟨95294091824531034892542281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63529394549687356595028187 95294091824531034892542281)
    ·
      refine ⟨71470568868398276169406711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95294091824531034892542281 71470568868398276169406711)
      ·
        refine ⟨107205853302597414254110067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71470568868398276169406711 107205853302597414254110067)
        ·
          refine ⟨160808779953896121381165101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107205853302597414254110067 160808779953896121381165101)
          ·
            refine ⟨60303292482711045517936913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160808779953896121381165101 60303292482711045517936913)
            ·
              refine ⟨45227469362033284138452685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60303292482711045517936913 45227469362033284138452685)
              ·
                refine ⟨16960301010762481551919757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45227469362033284138452685 16960301010762481551919757)
                ·
                  refine ⟨6360112879035930581969909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16960301010762481551919757 6360112879035930581969909)
                  ·
                    refine ⟨596260582409618492059679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6360112879035930581969909 596260582409618492059679)
                    ·
                      rfl

theorem cell23_3483640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_3483640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483640 prefixEnd_3483640 := by exact prefixLift 3483640
  have htrace : WordTrace (prefixWord ++ tailWord_3483640) baseStart_3483640 baseEnd_3483640 := by
    simpa [prefixWord, tailWord_3483640, baseEnd_3483640] using wordTrace_append hprefix tailTrace_3483640
  have hstable : (prefixWord ++ tailWord_3483640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483640).length < 2 ^ (prefixWord ++ tailWord_3483640).sum := by decide
  have hdescent : baseEnd_3483640 < baseStart_3483640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483647 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 6, 3, 2]
def baseStart_3483647 : Nat := 118140960795 + 3483647 * 2 ^ 59
def prefixEnd_3483647 : Nat := 4983230072969 + 3 ^ 40 * 3483647 * 2
def baseEnd_3483647 : Nat := 1788785341593436948791505

theorem tailTrace_3483647 : CollatzResearch.WordTrace tailWord_3483647 prefixEnd_3483647 1788785341593436948791505 := by
  unfold tailWord_3483647
  simp only [CollatzResearch.WordTrace]
  refine ⟨127059044410349353385561195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84706029606899568923707463 127059044410349353385561195)
  ·
    refine ⟨190588566615524030078341793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127059044410349353385561195 190588566615524030078341793)
    ·
      refine ⟨142941424961643022558756345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190588566615524030078341793 142941424961643022558756345)
      ·
        refine ⟨107206068721232266919067259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142941424961643022558756345 107206068721232266919067259)
        ·
          refine ⟨160809103081848400378600889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107206068721232266919067259 160809103081848400378600889)
          ·
            refine ⟨120606827311386300283950667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160809103081848400378600889 120606827311386300283950667)
            ·
              refine ⟨180910240967079450425926001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120606827311386300283950667 180910240967079450425926001)
              ·
                refine ⟨135682680725309587819444501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180910240967079450425926001 135682680725309587819444501)
                ·
                  refine ⟨6360125658998886929036461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135682680725309587819444501 6360125658998886929036461)
                  ·
                    refine ⟨2385047122124582598388673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6360125658998886929036461 2385047122124582598388673)
                    ·
                      refine ⟨1788785341593436948791505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385047122124582598388673 1788785341593436948791505)
                      ·
                        rfl

theorem cell23_3483647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_3483647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483647 prefixEnd_3483647 := by exact prefixLift 3483647
  have htrace : WordTrace (prefixWord ++ tailWord_3483647) baseStart_3483647 baseEnd_3483647 := by
    simpa [prefixWord, tailWord_3483647, baseEnd_3483647] using wordTrace_append hprefix tailTrace_3483647
  have hstable : (prefixWord ++ tailWord_3483647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483647).length < 2 ^ (prefixWord ++ tailWord_3483647).sum := by decide
  have hdescent : baseEnd_3483647 < baseStart_3483647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483694 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3483694 : Nat := 118140960795 + 3483694 * 2 ^ 59
def prefixEnd_3483694 : Nat := 4983230072969 + 3 ^ 40 * 3483694 * 2
def baseEnd_3483694 : Nat := 1788809475184198264903789

theorem tailTrace_3483694 : CollatzResearch.WordTrace tailWord_3483694 prefixEnd_3483694 1788809475184198264903789 := by
  unfold tailWord_3483694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882594830147385051565267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84707172427452720275014757 15882594830147385051565267)
  ·
    refine ⟨23823892245221077577347901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15882594830147385051565267 23823892245221077577347901)
    ·
      refine ⟨8933959591957904091505463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23823892245221077577347901 8933959591957904091505463)
      ·
        refine ⟨13400939387936856137258195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933959591957904091505463 13400939387936856137258195)
        ·
          refine ⟨20101409081905284205887293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13400939387936856137258195 20101409081905284205887293)
          ·
            refine ⟨7538028405714481577207735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20101409081905284205887293 7538028405714481577207735)
            ·
              refine ⟨11307042608571722365811603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538028405714481577207735 11307042608571722365811603)
              ·
                refine ⟨16960563912857583548717405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11307042608571722365811603 16960563912857583548717405)
                ·
                  refine ⟨6360211467321593830769027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16960563912857583548717405 6360211467321593830769027)
                  ·
                    refine ⟨9540317200982390746153541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6360211467321593830769027 9540317200982390746153541)
                    ·
                      refine ⟨1788809475184198264903789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9540317200982390746153541 1788809475184198264903789)
                      ·
                        rfl

theorem cell23_3483694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3483694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483694 prefixEnd_3483694 := by exact prefixLift 3483694
  have htrace : WordTrace (prefixWord ++ tailWord_3483694) baseStart_3483694 baseEnd_3483694 := by
    simpa [prefixWord, tailWord_3483694, baseEnd_3483694] using wordTrace_append hprefix tailTrace_3483694
  have hstable : (prefixWord ++ tailWord_3483694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483694).length < 2 ^ (prefixWord ++ tailWord_3483694).sum := by decide
  have hdescent : baseEnd_3483694 < baseStart_3483694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483720 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3483720 : Nat := 118140960795 + 3483720 * 2 ^ 59
def prefixEnd_3483720 : Nat := 4983230072969 + 3 ^ 40 * 3483720 * 2
def baseEnd_3483720 : Nat := 1788822825681215163178669

theorem tailTrace_3483720 : CollatzResearch.WordTrace tailWord_3483720 prefixEnd_3483720 1788822825681215163178669 := by
  unfold tailWord_3483720
  simp only [CollatzResearch.WordTrace]
  refine ⟨63530853469542443426484307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84707804626056591235312409 63530853469542443426484307)
  ·
    refine ⟨95296280204313665139726461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63530853469542443426484307 95296280204313665139726461)
    ·
      refine ⟨35736105076617624427397423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95296280204313665139726461 35736105076617624427397423)
      ·
        refine ⟨53604157614926436641096135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35736105076617624427397423 53604157614926436641096135)
        ·
          refine ⟨80406236422389654961644203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53604157614926436641096135 80406236422389654961644203)
          ·
            refine ⟨120609354633584482442466305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80406236422389654961644203 120609354633584482442466305)
            ·
              refine ⟨90457015975188361831849729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120609354633584482442466305 90457015975188361831849729)
              ·
                refine ⟨67842761981391271373887297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90457015975188361831849729 67842761981391271373887297)
                ·
                  refine ⟨50882071486043453530415473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67842761981391271373887297 50882071486043453530415473)
                  ·
                    refine ⟨38161553614532590147811605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50882071486043453530415473 38161553614532590147811605)
                    ·
                      refine ⟨1788822825681215163178669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38161553614532590147811605 1788822825681215163178669)
                      ·
                        rfl

theorem cell23_3483720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3483720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483720 prefixEnd_3483720 := by exact prefixLift 3483720
  have htrace : WordTrace (prefixWord ++ tailWord_3483720) baseStart_3483720 baseEnd_3483720 := by
    simpa [prefixWord, tailWord_3483720, baseEnd_3483720] using wordTrace_append hprefix tailTrace_3483720
  have hstable : (prefixWord ++ tailWord_3483720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483720).length < 2 ^ (prefixWord ++ tailWord_3483720).sum := by decide
  have hdescent : baseEnd_3483720 < baseStart_3483720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483741 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3483741 : Nat := 118140960795 + 3483741 * 2 ^ 59
def prefixEnd_3483741 : Nat := 4983230072969 + 3 ^ 40 * 3483741 * 2
def baseEnd_3483741 : Nat := 1788833608774959581016073

theorem tailTrace_3483741 : CollatzResearch.WordTrace tailWord_3483741 prefixEnd_3483741 1788833608774959581016073 := by
  unfold tailWord_3483741
  simp only [CollatzResearch.WordTrace]
  refine ⟨127062472872008807439483077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84708315248005871626322051 127062472872008807439483077)
  ·
    refine ⟨23824213663501651394903077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127062472872008807439483077 23824213663501651394903077)
    ·
      refine ⟨4467040061906559636544327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23824213663501651394903077 4467040061906559636544327)
      ·
        refine ⟨6700560092859839454816491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467040061906559636544327 6700560092859839454816491)
        ·
          refine ⟨10050840139289759182224737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700560092859839454816491 10050840139289759182224737)
          ·
            refine ⟨7538130104467319386668553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10050840139289759182224737 7538130104467319386668553)
            ·
              refine ⟨5653597578350489540001415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538130104467319386668553 5653597578350489540001415)
              ·
                refine ⟨8480396367525734310002123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653597578350489540001415 8480396367525734310002123)
                ·
                  refine ⟨12720594551288601465003185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480396367525734310002123 12720594551288601465003185)
                  ·
                    refine ⟨9540445913466451098752389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12720594551288601465003185 9540445913466451098752389)
                    ·
                      refine ⟨1788833608774959581016073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9540445913466451098752389 1788833608774959581016073)
                      ·
                        rfl

theorem cell23_3483741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3483741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483741 prefixEnd_3483741 := by exact prefixLift 3483741
  have htrace : WordTrace (prefixWord ++ tailWord_3483741) baseStart_3483741 baseEnd_3483741 := by
    simpa [prefixWord, tailWord_3483741, baseEnd_3483741] using wordTrace_append hprefix tailTrace_3483741
  have hstable : (prefixWord ++ tailWord_3483741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483741).length < 2 ^ (prefixWord ++ tailWord_3483741).sum := by decide
  have hdescent : baseEnd_3483741 < baseStart_3483741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483744 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_3483744 : Nat := 118140960795 + 3483744 * 2 ^ 59
def prefixEnd_3483744 : Nat := 4983230072969 + 3 ^ 40 * 3483744 * 2
def baseEnd_3483744 : Nat := 1788835149216923069278559

theorem tailTrace_3483744 : CollatzResearch.WordTrace tailWord_3483744 prefixEnd_3483744 1788835149216923069278559 := by
  unfold tailWord_3483744
  simp only [CollatzResearch.WordTrace]
  refine ⟨63531291145498969475921143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84708388193998625967894857 63531291145498969475921143)
  ·
    refine ⟨95296936718248454213881715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63531291145498969475921143 95296936718248454213881715)
    ·
      refine ⟨142945405077372681320822573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95296936718248454213881715 142945405077372681320822573)
      ·
        refine ⟨53604526904014755495308465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142945405077372681320822573 53604526904014755495308465)
        ·
          refine ⟨40203395178011066621481349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53604526904014755495308465 40203395178011066621481349)
          ·
            refine ⟨7538136595877074991527753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40203395178011066621481349 7538136595877074991527753)
            ·
              refine ⟨5653602446907806243645815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538136595877074991527753 5653602446907806243645815)
              ·
                refine ⟨8480403670361709365468723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653602446907806243645815 8480403670361709365468723)
                ·
                  refine ⟨12720605505542564048203085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480403670361709365468723 12720605505542564048203085)
                  ·
                    refine ⟨4770227064578461518076157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12720605505542564048203085 4770227064578461518076157)
                    ·
                      refine ⟨1788835149216923069278559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4770227064578461518076157 1788835149216923069278559)
                      ·
                        rfl

theorem cell23_3483744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_3483744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483744 prefixEnd_3483744 := by exact prefixLift 3483744
  have htrace : WordTrace (prefixWord ++ tailWord_3483744) baseStart_3483744 baseEnd_3483744 := by
    simpa [prefixWord, tailWord_3483744, baseEnd_3483744] using wordTrace_append hprefix tailTrace_3483744
  have hstable : (prefixWord ++ tailWord_3483744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483744).length < 2 ^ (prefixWord ++ tailWord_3483744).sum := by decide
  have hdescent : baseEnd_3483744 < baseStart_3483744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483757 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3483757 : Nat := 118140960795 + 3483757 * 2 ^ 59
def prefixEnd_3483757 : Nat := 4983230072969 + 3 ^ 40 * 3483757 * 2
def baseEnd_3483757 : Nat := 1788841824465431518415999

theorem tailTrace_3483757 : CollatzResearch.WordTrace tailWord_3483757 prefixEnd_3483757 1788841824465431518415999 := by
  unfold tailWord_3483757
  simp only [CollatzResearch.WordTrace]
  refine ⟨127063056439950842172065525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84708704293300561448043683 127063056439950842172065525)
  ·
    refine ⟨11912161541245391453631143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127063056439950842172065525 11912161541245391453631143)
    ·
      refine ⟨17868242311868087180446715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912161541245391453631143 17868242311868087180446715)
      ·
        refine ⟨26802363467802130770670073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17868242311868087180446715 26802363467802130770670073)
        ·
          refine ⟨20101772600851598078002555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26802363467802130770670073 20101772600851598078002555)
          ·
            refine ⟨30152658901277397117003833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20101772600851598078002555 30152658901277397117003833)
            ·
              refine ⟨22614494175958047837752875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30152658901277397117003833 22614494175958047837752875)
              ·
                refine ⟨33921741263937071756629313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22614494175958047837752875 33921741263937071756629313)
                ·
                  refine ⟨25441305947952803817471985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33921741263937071756629313 25441305947952803817471985)
                  ·
                    refine ⟨19080979460964602863103989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25441305947952803817471985 19080979460964602863103989)
                    ·
                      refine ⟨1788841824465431518415999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19080979460964602863103989 1788841824465431518415999)
                      ·
                        rfl

theorem cell23_3483757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3483757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483757 prefixEnd_3483757 := by exact prefixLift 3483757
  have htrace : WordTrace (prefixWord ++ tailWord_3483757) baseStart_3483757 baseEnd_3483757 := by
    simpa [prefixWord, tailWord_3483757, baseEnd_3483757] using wordTrace_append hprefix tailTrace_3483757
  have hstable : (prefixWord ++ tailWord_3483757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483757).length < 2 ^ (prefixWord ++ tailWord_3483757).sum := by decide
  have hdescent : baseEnd_3483757 < baseStart_3483757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483797 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_3483797 : Nat := 118140960795 + 3483797 * 2 ^ 59
def prefixEnd_3483797 : Nat := 4983230072969 + 3 ^ 40 * 3483797 * 2
def baseEnd_3483797 : Nat := 1788862363691611361915815

theorem tailTrace_3483797 : CollatzResearch.WordTrace tailWord_3483797 prefixEnd_3483797 1788862363691611361915815 := by
  unfold tailWord_3483797
  simp only [CollatzResearch.WordTrace]
  refine ⟨127064515359805929003521645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84709676906537286002347763 127064515359805929003521645)
  ·
    refine ⟨47649193259927223376320617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127064515359805929003521645 47649193259927223376320617)
    ·
      refine ⟨35736894944945417532240463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47649193259927223376320617 35736894944945417532240463)
      ·
        refine ⟨53605342417418126298360695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35736894944945417532240463 53605342417418126298360695)
        ·
          refine ⟨80408013626127189447541043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53605342417418126298360695 80408013626127189447541043)
          ·
            refine ⟨120612020439190784171311565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80408013626127189447541043 120612020439190784171311565)
            ·
              refine ⟨45229507664696544064241837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120612020439190784171311565 45229507664696544064241837)
              ·
                refine ⟨16961065374261204024090689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45229507664696544064241837 16961065374261204024090689)
                ·
                  refine ⟨12720799030695903018068017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16961065374261204024090689 12720799030695903018068017)
                  ·
                    refine ⟨9540599273021927263551013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12720799030695903018068017 9540599273021927263551013)
                    ·
                      refine ⟨1788862363691611361915815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9540599273021927263551013 1788862363691611361915815)
                      ·
                        rfl

theorem cell23_3483797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_3483797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483797 prefixEnd_3483797 := by exact prefixLift 3483797
  have htrace : WordTrace (prefixWord ++ tailWord_3483797) baseStart_3483797 baseEnd_3483797 := by
    simpa [prefixWord, tailWord_3483797, baseEnd_3483797] using wordTrace_append hprefix tailTrace_3483797
  have hstable : (prefixWord ++ tailWord_3483797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483797).length < 2 ^ (prefixWord ++ tailWord_3483797).sum := by decide
  have hdescent : baseEnd_3483797 < baseStart_3483797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483801 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 2, 2, 2]
def baseStart_3483801 : Nat := 118140960795 + 3483801 * 2 ^ 59
def prefixEnd_3483801 : Nat := 4983230072969 + 3 ^ 40 * 3483801 * 2
def baseEnd_3483801 : Nat := 1788864417614229346265797

theorem tailTrace_3483801 : CollatzResearch.WordTrace tailWord_3483801 prefixEnd_3483801 1788864417614229346265797 := by
  unfold tailWord_3483801
  simp only [CollatzResearch.WordTrace]
  refine ⟨127064661251791437686667257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84709774167860958457778171 127064661251791437686667257)
  ·
    refine ⟨95298495938843578265000443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127064661251791437686667257 95298495938843578265000443)
    ·
      refine ⟨142947743908265367397500665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95298495938843578265000443 142947743908265367397500665)
      ·
        refine ⟨107210807931199025548125499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142947743908265367397500665 107210807931199025548125499)
        ·
          refine ⟨160816211896798538322188249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107210807931199025548125499 160816211896798538322188249)
          ·
            refine ⟨120612158922598903741641187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160816211896798538322188249 120612158922598903741641187)
            ·
              refine ⟨180918238383898355612461781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120612158922598903741641187 180918238383898355612461781)
              ·
                refine ⟨4240271212122617709667073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 180918238383898355612461781 4240271212122617709667073)
                ·
                  refine ⟨3180203409091963282250305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4240271212122617709667073 3180203409091963282250305)
                  ·
                    refine ⟨2385152556818972461687729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3180203409091963282250305 2385152556818972461687729)
                    ·
                      refine ⟨1788864417614229346265797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385152556818972461687729 1788864417614229346265797)
                      ·
                        rfl

theorem cell23_3483801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_3483801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483801 prefixEnd_3483801 := by exact prefixLift 3483801
  have htrace : WordTrace (prefixWord ++ tailWord_3483801) baseStart_3483801 baseEnd_3483801 := by
    simpa [prefixWord, tailWord_3483801, baseEnd_3483801] using wordTrace_append hprefix tailTrace_3483801
  have hstable : (prefixWord ++ tailWord_3483801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483801).length < 2 ^ (prefixWord ++ tailWord_3483801).sum := by decide
  have hdescent : baseEnd_3483801 < baseStart_3483801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483857 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3483857 : Nat := 118140960795 + 3483857 * 2 ^ 59
def prefixEnd_3483857 : Nat := 4983230072969 + 3 ^ 40 * 3483857 * 2
def baseEnd_3483857 : Nat := 1788893172530881127165539

theorem tailTrace_3483857 : CollatzResearch.WordTrace tailWord_3483857 prefixEnd_3483857 1788893172530881127165539 := by
  unfold tailWord_3483857
  simp only [CollatzResearch.WordTrace]
  refine ⟨127066703739588559250705825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84711135826392372833803883 127066703739588559250705825)
  ·
    refine ⟨95300027804691419438029369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127066703739588559250705825 95300027804691419438029369)
    ·
      refine ⟨71475020853518564578522027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95300027804691419438029369 71475020853518564578522027)
      ·
        refine ⟨107212531280277846867783041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71475020853518564578522027 107212531280277846867783041)
        ·
          refine ⟨80409398460208385150837281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107212531280277846867783041 80409398460208385150837281)
          ·
            refine ⟨60307048845156288863127961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80409398460208385150837281 60307048845156288863127961)
            ·
              refine ⟨45230286633867216647345971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60307048845156288863127961 45230286633867216647345971)
              ·
                refine ⟨67845429950800824971018957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45230286633867216647345971 67845429950800824971018957)
                ·
                  refine ⟨25442036231550309364132109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67845429950800824971018957 25442036231550309364132109)
                  ·
                    refine ⟨9540763586831366011549541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25442036231550309364132109 9540763586831366011549541)
                    ·
                      refine ⟨1788893172530881127165539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9540763586831366011549541 1788893172530881127165539)
                      ·
                        rfl

theorem cell23_3483857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3483857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483857 prefixEnd_3483857 := by exact prefixLift 3483857
  have htrace : WordTrace (prefixWord ++ tailWord_3483857) baseStart_3483857 baseEnd_3483857 := by
    simpa [prefixWord, tailWord_3483857, baseEnd_3483857] using wordTrace_append hprefix tailTrace_3483857
  have hstable : (prefixWord ++ tailWord_3483857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483857).length < 2 ^ (prefixWord ++ tailWord_3483857).sum := by decide
  have hdescent : baseEnd_3483857 < baseStart_3483857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483908 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3483908 : Nat := 118140960795 + 3483908 * 2 ^ 59
def prefixEnd_3483908 : Nat := 4983230072969 + 3 ^ 40 * 3483908 * 2
def baseEnd_3483908 : Nat := 1788919360044260427627805

theorem tailTrace_3483908 : CollatzResearch.WordTrace tailWord_3483908 prefixEnd_3483908 1788919360044260427627805 := by
  unfold tailWord_3483908
  simp only [CollatzResearch.WordTrace]
  refine ⟨63534281931201897480406189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84712375908269196640541585 63534281931201897480406189)
  ·
    refine ⟨23825355724200711555152321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63534281931201897480406189 23825355724200711555152321)
    ·
      refine ⟨17869016793150533666364241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23825355724200711555152321 17869016793150533666364241)
      ·
        refine ⟨13401762594862900249773181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17869016793150533666364241 13401762594862900249773181)
        ·
          refine ⟨5025660973073587593664943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13401762594862900249773181 5025660973073587593664943)
          ·
            refine ⟨7538491459610381390497415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025660973073587593664943 7538491459610381390497415)
            ·
              refine ⟨11307737189415572085746123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538491459610381390497415 11307737189415572085746123)
              ·
                refine ⟨16961605784123358128619185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11307737189415572085746123 16961605784123358128619185)
                ·
                  refine ⟨12721204338092518596464389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16961605784123358128619185 12721204338092518596464389)
                  ·
                    refine ⟨2385225813392347236837073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12721204338092518596464389 2385225813392347236837073)
                    ·
                      refine ⟨1788919360044260427627805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385225813392347236837073 1788919360044260427627805)
                      ·
                        rfl

theorem cell23_3483908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3483908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483908 prefixEnd_3483908 := by exact prefixLift 3483908
  have htrace : WordTrace (prefixWord ++ tailWord_3483908) baseStart_3483908 baseEnd_3483908 := by
    simpa [prefixWord, tailWord_3483908, baseEnd_3483908] using wordTrace_append hprefix tailTrace_3483908
  have hstable : (prefixWord ++ tailWord_3483908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483908).length < 2 ^ (prefixWord ++ tailWord_3483908).sum := by decide
  have hdescent : baseEnd_3483908 < baseStart_3483908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483914 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_3483914 : Nat := 118140960795 + 3483914 * 2 ^ 59
def prefixEnd_3483914 : Nat := 4983230072969 + 3 ^ 40 * 3483914 * 2
def baseEnd_3483914 : Nat := 198769160103131933794753

theorem tailTrace_3483914 : CollatzResearch.WordTrace tailWord_3483914 prefixEnd_3483914 198769160103131933794753 := by
  unfold tailWord_3483914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31767195675095514496382699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84712521800254705323687197 31767195675095514496382699)
  ·
    refine ⟨47650793512643271744574049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31767195675095514496382699 47650793512643271744574049)
    ·
      refine ⟨35738095134482453808430537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47650793512643271744574049 35738095134482453808430537)
      ·
        refine ⟨26803571350861840356322903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35738095134482453808430537 26803571350861840356322903)
        ·
          refine ⟨40205357026292760534484355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26803571350861840356322903 40205357026292760534484355)
          ·
            refine ⟨60308035539439140801726533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40205357026292760534484355 60308035539439140801726533)
            ·
              refine ⟨11307756663644838900323725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60308035539439140801726533 11307756663644838900323725)
              ·
                refine ⟨4240408748866814587621397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11307756663644838900323725 4240408748866814587621397)
                ·
                  refine ⟨198769160103131933794753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4240408748866814587621397 198769160103131933794753)
                  ·
                    rfl

theorem cell23_3483914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_3483914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483914 prefixEnd_3483914 := by exact prefixLift 3483914
  have htrace : WordTrace (prefixWord ++ tailWord_3483914) baseStart_3483914 baseEnd_3483914 := by
    simpa [prefixWord, tailWord_3483914, baseEnd_3483914] using wordTrace_append hprefix tailTrace_3483914
  have hstable : (prefixWord ++ tailWord_3483914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483914).length < 2 ^ (prefixWord ++ tailWord_3483914).sum := by decide
  have hdescent : baseEnd_3483914 < baseStart_3483914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483951 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 2, 3, 2]
def baseStart_3483951 : Nat := 118140960795 + 3483951 * 2 ^ 59
def prefixEnd_3483951 : Nat := 4983230072969 + 3 ^ 40 * 3483951 * 2
def baseEnd_3483951 : Nat := 1788941439712403759390107

theorem tailTrace_3483951 : CollatzResearch.WordTrace tailWord_3483951 prefixEnd_3483951 1788941439712403759390107 := by
  unfold tailWord_3483951
  simp only [CollatzResearch.WordTrace]
  refine ⟨127070132201248013304627707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84713421467498675536418471 127070132201248013304627707)
  ·
    refine ⟨190605198301872019956941561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127070132201248013304627707 190605198301872019956941561)
    ·
      refine ⟨142953898726404014967706171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190605198301872019956941561 142953898726404014967706171)
      ·
        refine ⟨214430848089606022451559257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142953898726404014967706171 214430848089606022451559257)
        ·
          refine ⟨160823136067204516838669443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214430848089606022451559257 160823136067204516838669443)
          ·
            refine ⟨241234704100806775258004165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160823136067204516838669443 241234704100806775258004165)
            ·
              refine ⟨45231507018901270360875781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241234704100806775258004165 45231507018901270360875781)
              ·
                refine ⟨8480907566043988192664209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45231507018901270360875781 8480907566043988192664209)
                ·
                  refine ⟨6360680674532991144498157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8480907566043988192664209 6360680674532991144498157)
                  ·
                    refine ⟨2385255252949871679186809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6360680674532991144498157 2385255252949871679186809)
                    ·
                      refine ⟨1788941439712403759390107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385255252949871679186809 1788941439712403759390107)
                      ·
                        rfl

theorem cell23_3483951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3, 2].length) (baseStart_3483951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483951 prefixEnd_3483951 := by exact prefixLift 3483951
  have htrace : WordTrace (prefixWord ++ tailWord_3483951) baseStart_3483951 baseEnd_3483951 := by
    simpa [prefixWord, tailWord_3483951, baseEnd_3483951] using wordTrace_append hprefix tailTrace_3483951
  have hstable : (prefixWord ++ tailWord_3483951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483951).length < 2 ^ (prefixWord ++ tailWord_3483951).sum := by decide
  have hdescent : baseEnd_3483951 < baseStart_3483951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483994 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_3483994 : Nat := 118140960795 + 3483994 * 2 ^ 59
def prefixEnd_3483994 : Nat := 4983230072969 + 3 ^ 40 * 3483994 * 2
def baseEnd_3483994 : Nat := 1788963519380547091152409

theorem tailTrace_3483994 : CollatzResearch.WordTrace tailWord_3483994 prefixEnd_3483994 1788963519380547091152409 := by
  unfold tailWord_3483994
  simp only [CollatzResearch.WordTrace]
  refine ⟨31767925135023057912110759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84714467026728154432295357 31767925135023057912110759)
  ·
    refine ⟨47651887702534586868166139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31767925135023057912110759 47651887702534586868166139)
    ·
      refine ⟨71477831553801880302249209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47651887702534586868166139 71477831553801880302249209)
      ·
        refine ⟨53608373665351410226686907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71477831553801880302249209 53608373665351410226686907)
        ·
          refine ⟨80412560498027115340030361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53608373665351410226686907 80412560498027115340030361)
          ·
            refine ⟨60309420373520336505022771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80412560498027115340030361 60309420373520336505022771)
            ·
              refine ⟨90464130560280504757534157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60309420373520336505022771 90464130560280504757534157)
              ·
                refine ⟨33924048960105189284075309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90464130560280504757534157 33924048960105189284075309)
                ·
                  refine ⟨12721518360039445981528241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33924048960105189284075309 12721518360039445981528241)
                  ·
                    refine ⟨9541138770029584486146181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12721518360039445981528241 9541138770029584486146181)
                    ·
                      refine ⟨1788963519380547091152409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9541138770029584486146181 1788963519380547091152409)
                      ·
                        rfl

theorem cell23_3483994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_3483994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3483994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3483994 prefixEnd_3483994 := by exact prefixLift 3483994
  have htrace : WordTrace (prefixWord ++ tailWord_3483994) baseStart_3483994 baseEnd_3483994 := by
    simpa [prefixWord, tailWord_3483994, baseEnd_3483994] using wordTrace_append hprefix tailTrace_3483994
  have hstable : (prefixWord ++ tailWord_3483994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483994).length < 2 ^ (prefixWord ++ tailWord_3483994).sum := by decide
  have hdescent : baseEnd_3483994 < baseStart_3483994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484021 : List Nat := [1, 3, 4, 1, 2, 2, 2, 8]
def baseStart_3484021 : Nat := 118140960795 + 3484021 * 2 ^ 59
def prefixEnd_3484021 : Nat := 4983230072969 + 3 ^ 40 * 3484021 * 2
def baseEnd_3484021 : Nat := 66258421605859943907955

theorem tailTrace_3484021 : CollatzResearch.WordTrace tailWord_3484021 prefixEnd_3484021 66258421605859943907955 := by
  unfold tailWord_3484021
  simp only [CollatzResearch.WordTrace]
  refine ⟨127072685310994415259675917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84715123540662943506450611 127072685310994415259675917)
  ·
    refine ⟨47652256991622905722378469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127072685310994415259675917 47652256991622905722378469)
    ·
      refine ⟨8934798185929294822945963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47652256991622905722378469 8934798185929294822945963)
      ·
        refine ⟨13402197278893942234418945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934798185929294822945963 13402197278893942234418945)
        ·
          refine ⟨10051647959170456675814209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13402197278893942234418945 10051647959170456675814209)
          ·
            refine ⟨7538735969377842506860657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10051647959170456675814209 7538735969377842506860657)
            ·
              refine ⟨5654051977033381880145493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538735969377842506860657 5654051977033381880145493)
              ·
                refine ⟨66258421605859943907955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5654051977033381880145493 66258421605859943907955)
                ·
                  rfl

theorem cell23_3484021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 8].length) (baseStart_3484021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484021 prefixEnd_3484021 := by exact prefixLift 3484021
  have htrace : WordTrace (prefixWord ++ tailWord_3484021) baseStart_3484021 baseEnd_3484021 := by
    simpa [prefixWord, tailWord_3484021, baseEnd_3484021] using wordTrace_append hprefix tailTrace_3484021
  have hstable : (prefixWord ++ tailWord_3484021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484021).length < 2 ^ (prefixWord ++ tailWord_3484021).sum := by decide
  have hdescent : baseEnd_3484021 < baseStart_3484021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484035 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 3]
def baseStart_3484035 : Nat := 118140960795 + 3484035 * 2 ^ 59
def prefixEnd_3484035 : Nat := 4983230072969 + 3 ^ 40 * 3484035 * 2
def baseEnd_3484035 : Nat := 1788984572087381430739721

theorem tailTrace_3484035 : CollatzResearch.WordTrace tailWord_3484035 prefixEnd_3484035 1788984572087381430739721 := by
  unfold tailWord_3484035
  simp only [CollatzResearch.WordTrace]
  refine ⟨127073195932943695650685559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84715463955295797100457039 127073195932943695650685559)
  ·
    refine ⟨190609793899415543476028339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127073195932943695650685559 190609793899415543476028339)
    ·
      refine ⟨285914690849123315214042509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190609793899415543476028339 285914690849123315214042509)
      ·
        refine ⟨107218009068421243205265941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285914690849123315214042509 107218009068421243205265941)
        ·
          refine ⟨5025844175082245775246841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107218009068421243205265941 5025844175082245775246841)
          ·
            refine ⟨3769383131311684331435131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5025844175082245775246841 3769383131311684331435131)
            ·
              refine ⟨5654074696967526497152697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769383131311684331435131 5654074696967526497152697)
              ·
                refine ⟨4240556022725644872864523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5654074696967526497152697 4240556022725644872864523)
                ·
                  refine ⟨6360834034088467309296785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240556022725644872864523 6360834034088467309296785)
                  ·
                    refine ⟨4770625525566350481972589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6360834034088467309296785 4770625525566350481972589)
                    ·
                      refine ⟨1788984572087381430739721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4770625525566350481972589 1788984572087381430739721)
                      ·
                        rfl

theorem cell23_3484035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_3484035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484035 prefixEnd_3484035 := by exact prefixLift 3484035
  have htrace : WordTrace (prefixWord ++ tailWord_3484035) baseStart_3484035 baseEnd_3484035 := by
    simpa [prefixWord, tailWord_3484035, baseEnd_3484035] using wordTrace_append hprefix tailTrace_3484035
  have hstable : (prefixWord ++ tailWord_3484035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484035).length < 2 ^ (prefixWord ++ tailWord_3484035).sum := by decide
  have hdescent : baseEnd_3484035 < baseStart_3484035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484052 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_3484052 : Nat := 118140960795 + 3484052 * 2 ^ 59
def prefixEnd_3484052 : Nat := 4983230072969 + 3 ^ 40 * 3484052 * 2
def baseEnd_3484052 : Nat := 1788993301258507864227143

theorem tailTrace_3484052 : CollatzResearch.WordTrace tailWord_3484052 prefixEnd_3484052 1788993301258507864227143 := by
  unfold tailWord_3484052
  simp only [CollatzResearch.WordTrace]
  refine ⟨63536907986941053777027205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84715877315921405036036273 63536907986941053777027205)
  ·
    refine ⟨11913170247551447583192601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63536907986941053777027205 11913170247551447583192601)
    ·
      refine ⟨8934877685663585687394451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11913170247551447583192601 8934877685663585687394451)
      ·
        refine ⟨13402316528495378531091677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934877685663585687394451 13402316528495378531091677)
        ·
          refine ⟨5025868698185766949159379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13402316528495378531091677 5025868698185766949159379)
          ·
            refine ⟨7538803047278650423739069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025868698185766949159379 7538803047278650423739069)
            ·
              refine ⟨2827051142729493908902151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7538803047278650423739069 2827051142729493908902151)
              ·
                refine ⟨4240576714094240863353227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827051142729493908902151 4240576714094240863353227)
                ·
                  refine ⟨6360865071141361295029841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240576714094240863353227 6360865071141361295029841)
                  ·
                    refine ⟨4770648803356020971272381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6360865071141361295029841 4770648803356020971272381)
                    ·
                      refine ⟨1788993301258507864227143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4770648803356020971272381 1788993301258507864227143)
                      ·
                        rfl

theorem cell23_3484052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_3484052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484052 prefixEnd_3484052 := by exact prefixLift 3484052
  have htrace : WordTrace (prefixWord ++ tailWord_3484052) baseStart_3484052 baseEnd_3484052 := by
    simpa [prefixWord, tailWord_3484052, baseEnd_3484052] using wordTrace_append hprefix tailTrace_3484052
  have hstable : (prefixWord ++ tailWord_3484052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484052).length < 2 ^ (prefixWord ++ tailWord_3484052).sum := by decide
  have hdescent : baseEnd_3484052 < baseStart_3484052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484071 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3484071 : Nat := 118140960795 + 3484071 * 2 ^ 59
def prefixEnd_3484071 : Nat := 4983230072969 + 3 ^ 40 * 3484071 * 2
def baseEnd_3484071 : Nat := 1789003057390943289889555

theorem tailTrace_3484071 : CollatzResearch.WordTrace tailWord_3484071 prefixEnd_3484071 1789003057390943289889555 := by
  unfold tailWord_3484071
  simp only [CollatzResearch.WordTrace]
  refine ⟨127074508960813273798996067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84716339307208849199330711 127074508960813273798996067)
  ·
    refine ⟨190611763441219910698494101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127074508960813273798996067 190611763441219910698494101)
    ·
      refine ⟨8934926411307183313991911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190611763441219910698494101 8934926411307183313991911)
      ·
        refine ⟨13402389616960774970987867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934926411307183313991911 13402389616960774970987867)
        ·
          refine ⟨20103584425441162456481801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402389616960774970987867 20103584425441162456481801)
          ·
            refine ⟨15077688319080871842361351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20103584425441162456481801 15077688319080871842361351)
            ·
              refine ⟨22616532478621307763542027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15077688319080871842361351 22616532478621307763542027)
              ·
                refine ⟨33924798717931961645313041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22616532478621307763542027 33924798717931961645313041)
                ·
                  refine ⟨25443599038448971233984781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33924798717931961645313041 25443599038448971233984781)
                  ·
                    refine ⟨9541349639418364212744293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25443599038448971233984781 9541349639418364212744293)
                    ·
                      refine ⟨1789003057390943289889555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9541349639418364212744293 1789003057390943289889555)
                      ·
                        rfl

theorem cell23_3484071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3484071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484071 prefixEnd_3484071 := by exact prefixLift 3484071
  have htrace : WordTrace (prefixWord ++ tailWord_3484071) baseStart_3484071 baseEnd_3484071 := by
    simpa [prefixWord, tailWord_3484071, baseEnd_3484071] using wordTrace_append hprefix tailTrace_3484071
  have hstable : (prefixWord ++ tailWord_3484071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484071).length < 2 ^ (prefixWord ++ tailWord_3484071).sum := by decide
  have hdescent : baseEnd_3484071 < baseStart_3484071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484081 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_3484081 : Nat := 118140960795 + 3484081 * 2 ^ 59
def prefixEnd_3484081 : Nat := 4983230072969 + 3 ^ 40 * 3484081 * 2
def baseEnd_3484081 : Nat := 596336064065829416921503

theorem tailTrace_3484081 : CollatzResearch.WordTrace tailWord_3484081 prefixEnd_3484081 596336064065829416921503 := by
  unfold tailWord_3484081
  simp only [CollatzResearch.WordTrace]
  refine ⟨127074873690777045506860097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84716582460518030337906731 127074873690777045506860097)
  ·
    refine ⟨95306155268082784130145073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127074873690777045506860097 95306155268082784130145073)
    ·
      refine ⟨71479616451062088097608805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95306155268082784130145073 71479616451062088097608805)
      ·
        refine ⟨13402428084574141518301651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71479616451062088097608805 13402428084574141518301651)
        ·
          refine ⟨20103642126861212277452477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402428084574141518301651 20103642126861212277452477)
          ·
            refine ⟨7538865797572954604044679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20103642126861212277452477 7538865797572954604044679)
            ·
              refine ⟨11308298696359431906067019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538865797572954604044679 11308298696359431906067019)
              ·
                refine ⟨16962448044539147859100529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11308298696359431906067019 16962448044539147859100529)
                ·
                  refine ⟨12721836033404360894325397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16962448044539147859100529 12721836033404360894325397)
                  ·
                    refine ⟨596336064065829416921503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12721836033404360894325397 596336064065829416921503)
                    ·
                      rfl

theorem cell23_3484081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_3484081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484081 prefixEnd_3484081 := by exact prefixLift 3484081
  have htrace : WordTrace (prefixWord ++ tailWord_3484081) baseStart_3484081 baseEnd_3484081 := by
    simpa [prefixWord, tailWord_3484081, baseEnd_3484081] using wordTrace_append hprefix tailTrace_3484081
  have hstable : (prefixWord ++ tailWord_3484081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484081).length < 2 ^ (prefixWord ++ tailWord_3484081).sum := by decide
  have hdescent : baseEnd_3484081 < baseStart_3484081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484088 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 6, 2, 2]
def baseStart_3484088 : Nat := 118140960795 + 3484088 * 2 ^ 59
def prefixEnd_3484088 : Nat := 4983230072969 + 3 ^ 40 * 3484088 * 2
def baseEnd_3484088 : Nat := 1789011786562069723376977

theorem tailTrace_3484088 : CollatzResearch.WordTrace tailWord_3484088 prefixEnd_3484088 1789011786562069723376977 := by
  unfold tailWord_3484088
  simp only [CollatzResearch.WordTrace]
  refine ⟨63537564500875842851182459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84716752667834457134909945 63537564500875842851182459)
  ·
    refine ⟨95306346751313764276773689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63537564500875842851182459 95306346751313764276773689)
    ·
      refine ⟨71479760063485323207580267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95306346751313764276773689 71479760063485323207580267)
      ·
        refine ⟨107219640095227984811370401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71479760063485323207580267 107219640095227984811370401)
        ·
          refine ⟨80414730071420988608527801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107219640095227984811370401 80414730071420988608527801)
          ·
            refine ⟨60311047553565741456395851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80414730071420988608527801 60311047553565741456395851)
            ·
              refine ⟨90466571330348612184593777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60311047553565741456395851 90466571330348612184593777)
              ·
                refine ⟨67849928497761459138445333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90466571330348612184593777 67849928497761459138445333)
                ·
                  refine ⟨3180465398332568397114625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67849928497761459138445333 3180465398332568397114625)
                  ·
                    refine ⟨2385349048749426297835969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3180465398332568397114625 2385349048749426297835969)
                    ·
                      refine ⟨1789011786562069723376977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385349048749426297835969 1789011786562069723376977)
                      ·
                        rfl

theorem cell23_3484088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_3484088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484088 prefixEnd_3484088 := by exact prefixLift 3484088
  have htrace : WordTrace (prefixWord ++ tailWord_3484088) baseStart_3484088 baseEnd_3484088 := by
    simpa [prefixWord, tailWord_3484088, baseEnd_3484088] using wordTrace_append hprefix tailTrace_3484088
  have hstable : (prefixWord ++ tailWord_3484088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484088).length < 2 ^ (prefixWord ++ tailWord_3484088).sum := by decide
  have hdescent : baseEnd_3484088 < baseStart_3484088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484118 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3484118 : Nat := 118140960795 + 3484118 * 2 ^ 59
def prefixEnd_3484118 : Nat := 4983230072969 + 3 ^ 40 * 3484118 * 2
def baseEnd_3484118 : Nat := 1789027190981704606001839

theorem tailTrace_3484118 : CollatzResearch.WordTrace tailWord_3484118 prefixEnd_3484118 1789027190981704606001839 := by
  unfold tailWord_3484118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942263949477687551622313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84717482127762000550638005 7942263949477687551622313)
  ·
    refine ⟨5956697962108265663716735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7942263949477687551622313 5956697962108265663716735)
    ·
      refine ⟨8935046943162398495575103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956697962108265663716735 8935046943162398495575103)
      ·
        refine ⟨13402570414743597743362655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935046943162398495575103 13402570414743597743362655)
        ·
          refine ⟨20103855622115396615043983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402570414743597743362655 20103855622115396615043983)
          ·
            refine ⟨30155783433173094922565975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20103855622115396615043983 30155783433173094922565975)
            ·
              refine ⟨45233675149759642383848963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30155783433173094922565975 45233675149759642383848963)
              ·
                refine ⟨67850512724639463575773445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45233675149759642383848963 67850512724639463575773445)
                ·
                  refine ⟨12721971135869899420457521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67850512724639463575773445 12721971135869899420457521)
                  ·
                    refine ⟨9541478351902424565343141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12721971135869899420457521 9541478351902424565343141)
                    ·
                      refine ⟨1789027190981704606001839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9541478351902424565343141 1789027190981704606001839)
                      ·
                        rfl

theorem cell23_3484118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3484118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484118 prefixEnd_3484118 := by exact prefixLift 3484118
  have htrace : WordTrace (prefixWord ++ tailWord_3484118) baseStart_3484118 baseEnd_3484118 := by
    simpa [prefixWord, tailWord_3484118, baseEnd_3484118] using wordTrace_append hprefix tailTrace_3484118
  have hstable : (prefixWord ++ tailWord_3484118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484118).length < 2 ^ (prefixWord ++ tailWord_3484118).sum := by decide
  have hdescent : baseEnd_3484118 < baseStart_3484118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484121 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_3484121 : Nat := 118140960795 + 3484121 * 2 ^ 59
def prefixEnd_3484121 : Nat := 4983230072969 + 3 ^ 40 * 3484121 * 2
def baseEnd_3484121 : Nat := 1789028731423668094264325

theorem tailTrace_3484121 : CollatzResearch.WordTrace tailWord_3484121 prefixEnd_3484121 1789028731423668094264325 := by
  unfold tailWord_3484121
  simp only [CollatzResearch.WordTrace]
  refine ⟨127076332610632132338316217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84717555073754754892210811 127076332610632132338316217)
  ·
    refine ⟨95307249457974099253737163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127076332610632132338316217 95307249457974099253737163)
    ·
      refine ⟨142960874186961148880605745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95307249457974099253737163 142960874186961148880605745)
      ·
        refine ⟨107220655640220861660454309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142960874186961148880605745 107220655640220861660454309)
        ·
          refine ⟨20103872932541411561335183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107220655640220861660454309 20103872932541411561335183)
          ·
            refine ⟨30155809398812117342002775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20103872932541411561335183 30155809398812117342002775)
            ·
              refine ⟨45233714098218176013004163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30155809398812117342002775 45233714098218176013004163)
              ·
                refine ⟨67850571147327264019506245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45233714098218176013004163 67850571147327264019506245)
                ·
                  refine ⟨12721982090123862003657421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67850571147327264019506245 12721982090123862003657421)
                  ·
                    refine ⟨4770743283796448251371533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12721982090123862003657421 4770743283796448251371533)
                    ·
                      refine ⟨1789028731423668094264325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4770743283796448251371533 1789028731423668094264325)
                      ·
                        rfl

theorem cell23_3484121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_3484121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484121 prefixEnd_3484121 := by exact prefixLift 3484121
  have htrace : WordTrace (prefixWord ++ tailWord_3484121) baseStart_3484121 baseEnd_3484121 := by
    simpa [prefixWord, tailWord_3484121, baseEnd_3484121] using wordTrace_append hprefix tailTrace_3484121
  have hstable : (prefixWord ++ tailWord_3484121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484121).length < 2 ^ (prefixWord ++ tailWord_3484121).sum := by decide
  have hdescent : baseEnd_3484121 < baseStart_3484121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484138 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_3484138 : Nat := 118140960795 + 3484138 * 2 ^ 59
def prefixEnd_3484138 : Nat := 4983230072969 + 3 ^ 40 * 3484138 * 2
def baseEnd_3484138 : Nat := 1789037460594794527751747

theorem tailTrace_3484138 : CollatzResearch.WordTrace tailWord_3484138 prefixEnd_3484138 1789037460594794527751747 := by
  unfold tailWord_3484138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31769238162892636060421267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84717968434380362827790045 31769238162892636060421267)
  ·
    refine ⟨47653857244338954090631901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31769238162892636060421267 47653857244338954090631901)
    ·
      refine ⟨17870196466627107783986963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47653857244338954090631901 17870196466627107783986963)
      ·
        refine ⟨26805294699940661675980445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17870196466627107783986963 26805294699940661675980445)
        ·
          refine ⟨10051985512477748128492667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26805294699940661675980445 10051985512477748128492667)
          ·
            refine ⟨15077978268716622192739001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10051985512477748128492667 15077978268716622192739001)
            ·
              refine ⟨11308483701537466644554251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15077978268716622192739001 11308483701537466644554251)
              ·
                refine ⟨16962725552306199966831377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11308483701537466644554251 16962725552306199966831377)
                ·
                  refine ⟨12722044164229649975123533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16962725552306199966831377 12722044164229649975123533)
                  ·
                    refine ⟨4770766561586118740671325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12722044164229649975123533 4770766561586118740671325)
                    ·
                      refine ⟨1789037460594794527751747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4770766561586118740671325 1789037460594794527751747)
                      ·
                        rfl

theorem cell23_3484138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_3484138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484138 prefixEnd_3484138 := by exact prefixLift 3484138
  have htrace : WordTrace (prefixWord ++ tailWord_3484138) baseStart_3484138 baseEnd_3484138 := by
    simpa [prefixWord, tailWord_3484138, baseEnd_3484138] using wordTrace_append hprefix tailTrace_3484138
  have hstable : (prefixWord ++ tailWord_3484138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484138).length < 2 ^ (prefixWord ++ tailWord_3484138).sum := by decide
  have hdescent : baseEnd_3484138 < baseStart_3484138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484268 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_3484268 : Nat := 118140960795 + 3484268 * 2 ^ 59
def prefixEnd_3484268 : Nat := 4983230072969 + 3 ^ 40 * 3484268 * 2
def baseEnd_3484268 : Nat := 1789104213079879019126149

theorem tailTrace_3484268 : CollatzResearch.WordTrace tailWord_3484268 prefixEnd_3484268 1789104213079879019126149 := by
  unfold tailWord_3484268
  simp only [CollatzResearch.WordTrace]
  refine ⟨63540847070549788221958729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84721129427399717629278305 63540847070549788221958729)
  ·
    refine ⟨47655635302912341166469047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63540847070549788221958729 47655635302912341166469047)
    ·
      refine ⟨71483452954368511749703571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47655635302912341166469047 71483452954368511749703571)
      ·
        refine ⟨107225179431552767624555357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71483452954368511749703571 107225179431552767624555357)
        ·
          refine ⟨40209442286832287859208259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107225179431552767624555357 40209442286832287859208259)
          ·
            refine ⟨60314163430248431788812389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40209442286832287859208259 60314163430248431788812389)
            ·
              refine ⟨11308905643171580960402323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60314163430248431788812389 11308905643171580960402323)
              ·
                refine ⟨16963358464757371440603485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11308905643171580960402323 16963358464757371440603485)
                ·
                  refine ⟨6361259424284014290226307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16963358464757371440603485 6361259424284014290226307)
                  ·
                    refine ⟨9541889136426021435339461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6361259424284014290226307 9541889136426021435339461)
                    ·
                      refine ⟨1789104213079879019126149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9541889136426021435339461 1789104213079879019126149)
                      ·
                        rfl

theorem cell23_3484268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_3484268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484268 prefixEnd_3484268 := by exact prefixLift 3484268
  have htrace : WordTrace (prefixWord ++ tailWord_3484268) baseStart_3484268 baseEnd_3484268 := by
    simpa [prefixWord, tailWord_3484268, baseEnd_3484268] using wordTrace_append hprefix tailTrace_3484268
  have hstable : (prefixWord ++ tailWord_3484268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484268).length < 2 ^ (prefixWord ++ tailWord_3484268).sum := by decide
  have hdescent : baseEnd_3484268 < baseStart_3484268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484312 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 2, 4]
def baseStart_3484312 : Nat := 118140960795 + 3484312 * 2 ^ 59
def prefixEnd_3484312 : Nat := 4983230072969 + 3 ^ 40 * 3484312 * 2
def baseEnd_3484312 : Nat := 596375602076225615658649

theorem tailTrace_3484312 : CollatzResearch.WordTrace tailWord_3484312 prefixEnd_3484312 596375602076225615658649 := by
  unfold tailWord_3484312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63541649476470085979259595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84722199301960114639012793 63541649476470085979259595)
  ·
    refine ⟨95312474214705128968889393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63541649476470085979259595 95312474214705128968889393)
    ·
      refine ⟨71484355661028846726667045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95312474214705128968889393 71484355661028846726667045)
      ·
        refine ⟨13403316686442908761250071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71484355661028846726667045 13403316686442908761250071)
        ·
          refine ⟨20104975029664363141875107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403316686442908761250071 20104975029664363141875107)
          ·
            refine ⟨30157462544496544712812661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20104975029664363141875107 30157462544496544712812661)
            ·
              refine ⟨2827262113546551066826187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30157462544496544712812661 2827262113546551066826187)
              ·
                refine ⟨4240893170319826600239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827262113546551066826187 4240893170319826600239281)
                ·
                  refine ⟨3180669877739869950179461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4240893170319826600239281 3180669877739869950179461)
                  ·
                    refine ⟨596375602076225615658649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3180669877739869950179461 596375602076225615658649)
                    ·
                      rfl

theorem cell23_3484312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_3484312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484312 prefixEnd_3484312 := by exact prefixLift 3484312
  have htrace : WordTrace (prefixWord ++ tailWord_3484312) baseStart_3484312 baseEnd_3484312 := by
    simpa [prefixWord, tailWord_3484312, baseEnd_3484312] using wordTrace_append hprefix tailTrace_3484312
  have hstable : (prefixWord ++ tailWord_3484312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484312).length < 2 ^ (prefixWord ++ tailWord_3484312).sum := by decide
  have hdescent : baseEnd_3484312 < baseStart_3484312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484330 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3484330 : Nat := 118140960795 + 3484330 * 2 ^ 59
def prefixEnd_3484330 : Nat := 4983230072969 + 3 ^ 40 * 3484330 * 2
def baseEnd_3484330 : Nat := 1789136048880457776550865

theorem tailTrace_3484330 : CollatzResearch.WordTrace tailWord_3484330 prefixEnd_3484330 1789136048880457776550865 := by
  unfold tailWord_3484330
  simp only [CollatzResearch.WordTrace]
  refine ⟨31770988866718740258168611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84722636977916640688449629 31770988866718740258168611)
  ·
    refine ⟨47656483300078110387252917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31770988866718740258168611 47656483300078110387252917)
    ·
      refine ⟨4467795309382322848804961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47656483300078110387252917 4467795309382322848804961)
      ·
        refine ⟨3350846482036742136603721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467795309382322848804961 3350846482036742136603721)
        ·
          refine ⟨2513134861527556602452791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3350846482036742136603721 2513134861527556602452791)
          ·
            refine ⟨3769702292291334903679187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513134861527556602452791 3769702292291334903679187)
            ·
              refine ⟨5654553438437002355518781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769702292291334903679187 5654553438437002355518781)
              ·
                refine ⟨2120457539413875883319543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5654553438437002355518781 2120457539413875883319543)
                ·
                  refine ⟨3180686309120813824979315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120457539413875883319543 3180686309120813824979315)
                  ·
                    refine ⟨4771029463681220737468973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3180686309120813824979315 4771029463681220737468973)
                    ·
                      refine ⟨1789136048880457776550865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4771029463681220737468973 1789136048880457776550865)
                      ·
                        rfl

theorem cell23_3484330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3484330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484330 prefixEnd_3484330 := by exact prefixLift 3484330
  have htrace : WordTrace (prefixWord ++ tailWord_3484330) baseStart_3484330 baseEnd_3484330 := by
    simpa [prefixWord, tailWord_3484330, baseEnd_3484330] using wordTrace_append hprefix tailTrace_3484330
  have hstable : (prefixWord ++ tailWord_3484330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484330).length < 2 ^ (prefixWord ++ tailWord_3484330).sum := by decide
  have hdescent : baseEnd_3484330 < baseStart_3484330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484335 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 3]
def baseStart_3484335 : Nat := 118140960795 + 3484335 * 2 ^ 59
def prefixEnd_3484335 : Nat := 4983230072969 + 3 ^ 40 * 3484335 * 2
def baseEnd_3484335 : Nat := 1789138616283730256988341

theorem tailTrace_3484335 : CollatzResearch.WordTrace tailWord_3484335 prefixEnd_3484335 1789138616283730256988341 := by
  unfold tailWord_3484335
  simp only [CollatzResearch.WordTrace]
  refine ⟨127084137831856846886606459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84722758554571231257737639 127084137831856846886606459)
  ·
    refine ⟨190626206747785270329909689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127084137831856846886606459 190626206747785270329909689)
    ·
      refine ⟨142969655060838952747432267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190626206747785270329909689 142969655060838952747432267)
      ·
        refine ⟨214454482591258429121148401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142969655060838952747432267 214454482591258429121148401)
        ·
          refine ⟨160840861943443821840861301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214454482591258429121148401 160840861943443821840861301)
          ·
            refine ⟨15078830807197858297580747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160840861943443821840861301 15078830807197858297580747)
            ·
              refine ⟨22618246210796787446371121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15078830807197858297580747 22618246210796787446371121)
              ·
                refine ⟨16963684658097590584778341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22618246210796787446371121 16963684658097590584778341)
                ·
                  refine ⟨3180690873393298234645939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16963684658097590584778341 3180690873393298234645939)
                  ·
                    refine ⟨4771036310089947351968909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3180690873393298234645939 4771036310089947351968909)
                    ·
                      refine ⟨1789138616283730256988341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4771036310089947351968909 1789138616283730256988341)
                      ·
                        rfl

theorem cell23_3484335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_3484335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484335 prefixEnd_3484335 := by exact prefixLift 3484335
  have htrace : WordTrace (prefixWord ++ tailWord_3484335) baseStart_3484335 baseEnd_3484335 := by
    simpa [prefixWord, tailWord_3484335, baseEnd_3484335] using wordTrace_append hprefix tailTrace_3484335
  have hstable : (prefixWord ++ tailWord_3484335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484335).length < 2 ^ (prefixWord ++ tailWord_3484335).sum := by decide
  have hdescent : baseEnd_3484335 < baseStart_3484335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484342 : List Nat := [5, 1, 3, 1, 2, 2, 9]
def baseStart_3484342 : Nat := 118140960795 + 3484342 * 2 ^ 59
def prefixEnd_3484342 : Nat := 4983230072969 + 3 ^ 40 * 3484342 * 2
def baseEnd_3484342 : Nat := 22088175440102613945689

theorem tailTrace_3484342 : CollatzResearch.WordTrace tailWord_3484342 prefixEnd_3484342 22088175440102613945689 := by
  unfold tailWord_3484342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942774571426967942631955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84722928761887658054740853 7942774571426967942631955)
  ·
    refine ⟨11914161857140451913947933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942774571426967942631955 11914161857140451913947933)
    ·
      refine ⟨4467810696427669467730475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11914161857140451913947933 4467810696427669467730475)
      ·
        refine ⟨6701716044641504201595713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467810696427669467730475 6701716044641504201595713)
        ·
          refine ⟨5026287033481128151196785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6701716044641504201595713 5026287033481128151196785)
          ·
            refine ⟨3769715275110846113397589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026287033481128151196785 3769715275110846113397589)
            ·
              refine ⟨22088175440102613945689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3769715275110846113397589 22088175440102613945689)
              ·
                rfl

theorem cell23_3484342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 9].length) (baseStart_3484342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484342 prefixEnd_3484342 := by exact prefixLift 3484342
  have htrace : WordTrace (prefixWord ++ tailWord_3484342) baseStart_3484342 baseEnd_3484342 := by
    simpa [prefixWord, tailWord_3484342, baseEnd_3484342] using wordTrace_append hprefix tailTrace_3484342
  have hstable : (prefixWord ++ tailWord_3484342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484342).length < 2 ^ (prefixWord ++ tailWord_3484342).sum := by decide
  have hdescent : baseEnd_3484342 < baseStart_3484342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484345 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3484345 : Nat := 118140960795 + 3484345 * 2 ^ 59
def prefixEnd_3484345 : Nat := 4983230072969 + 3 ^ 40 * 3484345 * 2
def baseEnd_3484345 : Nat := 1789143751090275217863295

theorem tailTrace_3484345 : CollatzResearch.WordTrace tailWord_3484345 prefixEnd_3484345 1789143751090275217863295 := by
  unfold tailWord_3484345
  simp only [CollatzResearch.WordTrace]
  refine ⟨127084502561820618594470489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84723001707880412396313659 127084502561820618594470489)
  ·
    refine ⟨95313376921365463945852867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127084502561820618594470489 95313376921365463945852867)
    ·
      refine ⟨142970065382048195918779301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95313376921365463945852867 142970065382048195918779301)
      ·
        refine ⟨26806887259134036734771119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142970065382048195918779301 26806887259134036734771119)
        ·
          refine ⟨40210330888701055102156679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26806887259134036734771119 40210330888701055102156679)
          ·
            refine ⟨60315496333051582653235019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40210330888701055102156679 60315496333051582653235019)
            ·
              refine ⟨90473244499577373979852529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60315496333051582653235019 90473244499577373979852529)
              ·
                refine ⟨67854933374683030484889397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90473244499577373979852529 67854933374683030484889397)
                ·
                  refine ⟨6361400003876534107958381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67854933374683030484889397 6361400003876534107958381)
                  ·
                    refine ⟨2385525001453700290484393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6361400003876534107958381 2385525001453700290484393)
                    ·
                      refine ⟨1789143751090275217863295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385525001453700290484393 1789143751090275217863295)
                      ·
                        rfl

theorem cell23_3484345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3484345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484345 prefixEnd_3484345 := by exact prefixLift 3484345
  have htrace : WordTrace (prefixWord ++ tailWord_3484345) baseStart_3484345 baseEnd_3484345 := by
    simpa [prefixWord, tailWord_3484345, baseEnd_3484345] using wordTrace_append hprefix tailTrace_3484345
  have hstable : (prefixWord ++ tailWord_3484345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484345).length < 2 ^ (prefixWord ++ tailWord_3484345).sum := by decide
  have hdescent : baseEnd_3484345 < baseStart_3484345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484348 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3484348 : Nat := 118140960795 + 3484348 * 2 ^ 59
def prefixEnd_3484348 : Nat := 4983230072969 + 3 ^ 40 * 3484348 * 2
def baseEnd_3484348 : Nat := 1789145291532238706125781

theorem tailTrace_3484348 : CollatzResearch.WordTrace tailWord_3484348 prefixEnd_3484348 1789145291532238706125781 := by
  unfold tailWord_3484348
  simp only [CollatzResearch.WordTrace]
  refine ⟨63542305990404875053414849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84723074653873166737886465 63542305990404875053414849)
  ·
    refine ⟨47656729492803656290061137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63542305990404875053414849 47656729492803656290061137)
    ·
      refine ⟨35742547119602742217545853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47656729492803656290061137 35742547119602742217545853)
      ·
        refine ⟨13403455169851028331579695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35742547119602742217545853 13403455169851028331579695)
        ·
          refine ⟨20105182754776542497369543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403455169851028331579695 20105182754776542497369543)
          ·
            refine ⟨30157774132164813746054315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105182754776542497369543 30157774132164813746054315)
            ·
              refine ⟨45236661198247220619081473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30157774132164813746054315 45236661198247220619081473)
              ·
                refine ⟨33927495898685415464311105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45236661198247220619081473 33927495898685415464311105)
                ·
                  refine ⟨25445621924014061598233329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33927495898685415464311105 25445621924014061598233329)
                  ·
                    refine ⟨19084216443010546198674997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25445621924014061598233329 19084216443010546198674997)
                    ·
                      refine ⟨1789145291532238706125781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19084216443010546198674997 1789145291532238706125781)
                      ·
                        rfl

theorem cell23_3484348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3484348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484348 prefixEnd_3484348 := by exact prefixLift 3484348
  have htrace : WordTrace (prefixWord ++ tailWord_3484348) baseStart_3484348 baseEnd_3484348 := by
    simpa [prefixWord, tailWord_3484348, baseEnd_3484348] using wordTrace_append hprefix tailTrace_3484348
  have hstable : (prefixWord ++ tailWord_3484348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484348).length < 2 ^ (prefixWord ++ tailWord_3484348).sum := by decide
  have hdescent : baseEnd_3484348 < baseStart_3484348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484353 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3484353 : Nat := 118140960795 + 3484353 * 2 ^ 59
def prefixEnd_3484353 : Nat := 4983230072969 + 3 ^ 40 * 3484353 * 2
def baseEnd_3484353 : Nat := 1789147858935511186563259

theorem tailTrace_3484353 : CollatzResearch.WordTrace tailWord_3484353 prefixEnd_3484353 1789147858935511186563259 := by
  unfold tailWord_3484353
  simp only [CollatzResearch.WordTrace]
  refine ⟨127084794345791635960761713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84723196230527757307174475 127084794345791635960761713)
  ·
    refine ⟨95313595759343726970571285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127084794345791635960761713 95313595759343726970571285)
    ·
      refine ⟨4467824801219237201745529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95313595759343726970571285 4467824801219237201745529)
      ·
        refine ⟨3350868600914427901309147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467824801219237201745529 3350868600914427901309147)
        ·
          refine ⟨5026302901371641851963721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350868600914427901309147 5026302901371641851963721)
          ·
            refine ⟨3769727176028731388972791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026302901371641851963721 3769727176028731388972791)
            ·
              refine ⟨5654590764043097083459187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769727176028731388972791 5654590764043097083459187)
              ·
                refine ⟨8481886146064645625188781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654590764043097083459187 8481886146064645625188781)
                ·
                  refine ⟨3180707304774242109445793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8481886146064645625188781 3180707304774242109445793)
                  ·
                    refine ⟨2385530478580681582084345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3180707304774242109445793 2385530478580681582084345)
                    ·
                      refine ⟨1789147858935511186563259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385530478580681582084345 1789147858935511186563259)
                      ·
                        rfl

theorem cell23_3484353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3484353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484353 prefixEnd_3484353 := by exact prefixLift 3484353
  have htrace : WordTrace (prefixWord ++ tailWord_3484353) baseStart_3484353 baseEnd_3484353 := by
    simpa [prefixWord, tailWord_3484353, baseEnd_3484353] using wordTrace_append hprefix tailTrace_3484353
  have hstable : (prefixWord ++ tailWord_3484353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484353).length < 2 ^ (prefixWord ++ tailWord_3484353).sum := by decide
  have hdescent : baseEnd_3484353 < baseStart_3484353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484378 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_3484378 : Nat := 118140960795 + 3484378 * 2 ^ 59
def prefixEnd_3484378 : Nat := 4983230072969 + 3 ^ 40 * 3484378 * 2
def baseEnd_3484378 : Nat := 1789160695951873588750643

theorem tailTrace_3484378 : CollatzResearch.WordTrace tailWord_3484378 prefixEnd_3484378 1789160695951873588750643 := by
  unfold tailWord_3484378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31771426542675266307605447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84723804113800710153614525 31771426542675266307605447)
  ·
    refine ⟨47657139814012899461408171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31771426542675266307605447 47657139814012899461408171)
    ·
      refine ⟨71485709721019349192112257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47657139814012899461408171 71485709721019349192112257)
      ·
        refine ⟨53614282290764511894084193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71485709721019349192112257 53614282290764511894084193)
        ·
          refine ⟨40210711718073383920563145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53614282290764511894084193 40210711718073383920563145)
          ·
            refine ⟨30158033788555037940422359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40210711718073383920563145 30158033788555037940422359)
            ·
              refine ⟨45237050682832556910633539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30158033788555037940422359 45237050682832556910633539)
              ·
                refine ⟨67855576024248835365950309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45237050682832556910633539 67855576024248835365950309)
                ·
                  refine ⟨12722920504546656631115683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67855576024248835365950309 12722920504546656631115683)
                  ·
                    refine ⟨19084380756819984946673525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12722920504546656631115683 19084380756819984946673525)
                    ·
                      refine ⟨1789160695951873588750643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19084380756819984946673525 1789160695951873588750643)
                      ·
                        rfl

theorem cell23_3484378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_3484378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484378 prefixEnd_3484378 := by exact prefixLift 3484378
  have htrace : WordTrace (prefixWord ++ tailWord_3484378) baseStart_3484378 baseEnd_3484378 := by
    simpa [prefixWord, tailWord_3484378, baseEnd_3484378] using wordTrace_append hprefix tailTrace_3484378
  have hstable : (prefixWord ++ tailWord_3484378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484378).length < 2 ^ (prefixWord ++ tailWord_3484378).sum := by decide
  have hdescent : baseEnd_3484378 < baseStart_3484378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484404 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3484404 : Nat := 118140960795 + 3484404 * 2 ^ 59
def prefixEnd_3484404 : Nat := 4983230072969 + 3 ^ 40 * 3484404 * 2
def baseEnd_3484404 : Nat := 1789174046448890487025525

theorem tailTrace_3484404 : CollatzResearch.WordTrace tailWord_3484404 prefixEnd_3484404 1789174046448890487025525 := by
  unfold tailWord_3484404
  simp only [CollatzResearch.WordTrace]
  refine ⟨63543327234303435835434133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84724436312404581113912177 63543327234303435835434133)
  ·
    refine ⟨2978593464107973554785975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63543327234303435835434133 2978593464107973554785975)
    ·
      refine ⟨4467890196161960332178963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978593464107973554785975 4467890196161960332178963)
      ·
        refine ⟨6701835294242940498268445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467890196161960332178963 6701835294242940498268445)
        ·
          refine ⟨2513188235341102686850667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6701835294242940498268445 2513188235341102686850667)
          ·
            refine ⟨3769782353011654030276001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513188235341102686850667 3769782353011654030276001)
            ·
              refine ⟨2827336764758740522707001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769782353011654030276001 2827336764758740522707001)
              ·
                refine ⟨2120502573569055392030251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827336764758740522707001 2120502573569055392030251)
                ·
                  refine ⟨3180753860353583088045377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120502573569055392030251 3180753860353583088045377)
                  ·
                    refine ⟨2385565395265187316034033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3180753860353583088045377 2385565395265187316034033)
                    ·
                      refine ⟨1789174046448890487025525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385565395265187316034033 1789174046448890487025525)
                      ·
                        rfl

theorem cell23_3484404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3484404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484404 prefixEnd_3484404 := by exact prefixLift 3484404
  have htrace : WordTrace (prefixWord ++ tailWord_3484404) baseStart_3484404 baseEnd_3484404 := by
    simpa [prefixWord, tailWord_3484404, baseEnd_3484404] using wordTrace_append hprefix tailTrace_3484404
  have hstable : (prefixWord ++ tailWord_3484404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484404).length < 2 ^ (prefixWord ++ tailWord_3484404).sum := by decide
  have hdescent : baseEnd_3484404 < baseStart_3484404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484428 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_3484428 : Nat := 118140960795 + 3484428 * 2 ^ 59
def prefixEnd_3484428 : Nat := 4983230072969 + 3 ^ 40 * 3484428 * 2
def baseEnd_3484428 : Nat := 596395456661532797708471

theorem tailTrace_3484428 : CollatzResearch.WordTrace tailWord_3484428 prefixEnd_3484428 596395456661532797708471 := by
  unfold tailWord_3484428
  simp only [CollatzResearch.WordTrace]
  refine ⟨63543764910259961884870969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84725019880346615846494625 63543764910259961884870969)
  ·
    refine ⟨47657823682694971413653227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63543764910259961884870969 47657823682694971413653227)
    ·
      refine ⟨71486735524042457120479841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47657823682694971413653227 71486735524042457120479841)
      ·
        refine ⟨53615051643031842840359881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71486735524042457120479841 53615051643031842840359881)
        ·
          refine ⟨40211288732273882130269911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53615051643031842840359881 40211288732273882130269911)
          ·
            refine ⟨60316933098410823195404867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40211288732273882130269911 60316933098410823195404867)
            ·
              refine ⟨90475399647616234793107301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60316933098410823195404867 90475399647616234793107301)
              ·
                refine ⟨16964137433928044023707619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90475399647616234793107301 16964137433928044023707619)
                ·
                  refine ⟨25446206150892066035561429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16964137433928044023707619 25446206150892066035561429)
                  ·
                    refine ⟨596395456661532797708471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25446206150892066035561429 596395456661532797708471)
                    ·
                      rfl

theorem cell23_3484428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_3484428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484428 prefixEnd_3484428 := by exact prefixLift 3484428
  have htrace : WordTrace (prefixWord ++ tailWord_3484428) baseStart_3484428 baseEnd_3484428 := by
    simpa [prefixWord, tailWord_3484428, baseEnd_3484428] using wordTrace_append hprefix tailTrace_3484428
  have hstable : (prefixWord ++ tailWord_3484428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484428).length < 2 ^ (prefixWord ++ tailWord_3484428).sum := by decide
  have hdescent : baseEnd_3484428 < baseStart_3484428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484435 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 2, 5, 2]
def baseStart_3484435 : Nat := 118140960795 + 3484435 * 2 ^ 59
def prefixEnd_3484435 : Nat := 4983230072969 + 3 ^ 40 * 3484435 * 2
def baseEnd_3484435 : Nat := 1789189964349179865737881

theorem tailTrace_3484435 : CollatzResearch.WordTrace tailWord_3484435 prefixEnd_3484435 1789189964349179865737881 := by
  unfold tailWord_3484435
  simp only [CollatzResearch.WordTrace]
  refine ⟨127087785131494563965246759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84725190087663042643497839 127087785131494563965246759)
  ·
    refine ⟨190631677697241845947870139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127087785131494563965246759 190631677697241845947870139)
    ·
      refine ⟨285947516545862768921805209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190631677697241845947870139 285947516545862768921805209)
      ·
        refine ⟨214460637409397076691353907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285947516545862768921805209 214460637409397076691353907)
        ·
          refine ⟨321690956114095615037030861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214460637409397076691353907 321690956114095615037030861)
          ·
            refine ⟨120634108542785855638886573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321690956114095615037030861 120634108542785855638886573)
            ·
              refine ⟨45237790703544695864582465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120634108542785855638886573 45237790703544695864582465)
              ·
                refine ⟨33928343027658521898436849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45237790703544695864582465 33928343027658521898436849)
                ·
                  refine ⟨25446257270743891423827637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33928343027658521898436849 25446257270743891423827637)
                  ·
                    refine ⟨2385586619132239820983841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25446257270743891423827637 2385586619132239820983841)
                    ·
                      refine ⟨1789189964349179865737881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385586619132239820983841 1789189964349179865737881)
                      ·
                        rfl

theorem cell23_3484435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5, 2].length) (baseStart_3484435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484435 prefixEnd_3484435 := by exact prefixLift 3484435
  have htrace : WordTrace (prefixWord ++ tailWord_3484435) baseStart_3484435 baseEnd_3484435 := by
    simpa [prefixWord, tailWord_3484435, baseEnd_3484435] using wordTrace_append hprefix tailTrace_3484435
  have hstable : (prefixWord ++ tailWord_3484435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484435).length < 2 ^ (prefixWord ++ tailWord_3484435).sum := by decide
  have hdescent : baseEnd_3484435 < baseStart_3484435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484465 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3484465 : Nat := 118140960795 + 3484465 * 2 ^ 59
def prefixEnd_3484465 : Nat := 4983230072969 + 3 ^ 40 * 3484465 * 2
def baseEnd_3484465 : Nat := 1789205368768814748362743

theorem tailTrace_3484465 : CollatzResearch.WordTrace tailWord_3484465 prefixEnd_3484465 1789205368768814748362743 := by
  unfold tailWord_3484465
  simp only [CollatzResearch.WordTrace]
  refine ⟨127088879321385879088838849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84725919547590586059225899 127088879321385879088838849)
  ·
    refine ⟨95316659491039409316629137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127088879321385879088838849 95316659491039409316629137)
    ·
      refine ⟨71487494618279556987471853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95316659491039409316629137 71487494618279556987471853)
      ·
        refine ⟨26807810481854833870301945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71487494618279556987471853 26807810481854833870301945)
        ·
          refine ⟨20105857861391125402726459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26807810481854833870301945 20105857861391125402726459)
          ·
            refine ⟨30158786792086688104089689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105857861391125402726459 30158786792086688104089689)
            ·
              refine ⟨22619090094065016078067267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30158786792086688104089689 22619090094065016078067267)
              ·
                refine ⟨33928635141097524117100901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22619090094065016078067267 33928635141097524117100901)
                ·
                  refine ⟨6361619088955785771956419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33928635141097524117100901 6361619088955785771956419)
                  ·
                    refine ⟨9542428633433678657934629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6361619088955785771956419 9542428633433678657934629)
                    ·
                      refine ⟨1789205368768814748362743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9542428633433678657934629 1789205368768814748362743)
                      ·
                        rfl

theorem cell23_3484465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3484465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484465 prefixEnd_3484465 := by exact prefixLift 3484465
  have htrace : WordTrace (prefixWord ++ tailWord_3484465) baseStart_3484465 baseEnd_3484465 := by
    simpa [prefixWord, tailWord_3484465, baseEnd_3484465] using wordTrace_append hprefix tailTrace_3484465
  have hstable : (prefixWord ++ tailWord_3484465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484465).length < 2 ^ (prefixWord ++ tailWord_3484465).sum := by decide
  have hdescent : baseEnd_3484465 < baseStart_3484465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484485 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_3484485 : Nat := 118140960795 + 3484485 * 2 ^ 59
def prefixEnd_3484485 : Nat := 4983230072969 + 3 ^ 40 * 3484485 * 2
def baseEnd_3484485 : Nat := 1789215638381904670112651

theorem tailTrace_3484485 : CollatzResearch.WordTrace tailWord_3484485 prefixEnd_3484485 1789215638381904670112651 := by
  unfold tailWord_3484485
  simp only [CollatzResearch.WordTrace]
  refine ⟨127089608781313422504566909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84726405854208948336377939 127089608781313422504566909)
  ·
    refine ⟨47658603292992533439212591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127089608781313422504566909 47658603292992533439212591)
    ·
      refine ⟨71487904939488800158818887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47658603292992533439212591 71487904939488800158818887)
      ·
        refine ⟨107231857409233200238228331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71487904939488800158818887 107231857409233200238228331)
        ·
          refine ⟨160847786113849800357342497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107231857409233200238228331 160847786113849800357342497)
          ·
            refine ⟨120635839585387350268006873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160847786113849800357342497 120635839585387350268006873)
            ·
              refine ⟨90476879689040512701005155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120635839585387350268006873 90476879689040512701005155)
              ·
                refine ⟨135715319533560769051507733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90476879689040512701005155 135715319533560769051507733)
                ·
                  refine ⟨6361655603135661049289425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135715319533560769051507733 6361655603135661049289425)
                  ·
                    refine ⟨4771241702351745786967069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361655603135661049289425 4771241702351745786967069)
                    ·
                      refine ⟨1789215638381904670112651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4771241702351745786967069 1789215638381904670112651)
                      ·
                        rfl

theorem cell23_3484485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_3484485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484485 prefixEnd_3484485 := by exact prefixLift 3484485
  have htrace : WordTrace (prefixWord ++ tailWord_3484485) baseStart_3484485 baseEnd_3484485 := by
    simpa [prefixWord, tailWord_3484485, baseEnd_3484485] using wordTrace_append hprefix tailTrace_3484485
  have hstable : (prefixWord ++ tailWord_3484485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484485).length < 2 ^ (prefixWord ++ tailWord_3484485).sum := by decide
  have hdescent : baseEnd_3484485 < baseStart_3484485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484492 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_3484492 : Nat := 118140960795 + 3484492 * 2 ^ 59
def prefixEnd_3484492 : Nat := 4983230072969 + 3 ^ 40 * 3484492 * 2
def baseEnd_3484492 : Nat := 596406410915495380908373

theorem tailTrace_3484492 : CollatzResearch.WordTrace tailWord_3484492 prefixEnd_3484492 596406410915495380908373 := by
  unfold tailWord_3484492
  simp only [CollatzResearch.WordTrace]
  refine ⟨63544932046144031350035865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84726576061525375133381153 63544932046144031350035865)
  ·
    refine ⟨47658699034608023512526899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63544932046144031350035865 47658699034608023512526899)
    ·
      refine ⟨71488048551912035268790349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47658699034608023512526899 71488048551912035268790349)
      ·
        refine ⟨26808018206967013225796381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71488048551912035268790349 26808018206967013225796381)
        ·
          refine ⟨10053006827612629959673643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26808018206967013225796381 10053006827612629959673643)
          ·
            refine ⟨15079510241418944939510465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053006827612629959673643 15079510241418944939510465)
            ·
              refine ⟨11309632681064208704632849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15079510241418944939510465 11309632681064208704632849)
              ·
                refine ⟨8482224510798156528474637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11309632681064208704632849 8482224510798156528474637)
                ·
                  refine ⟨3180834191549308698177989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8482224510798156528474637 3180834191549308698177989)
                  ·
                    refine ⟨596406410915495380908373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3180834191549308698177989 596406410915495380908373)
                    ·
                      rfl

theorem cell23_3484492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_3484492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484492 prefixEnd_3484492 := by exact prefixLift 3484492
  have htrace : WordTrace (prefixWord ++ tailWord_3484492) baseStart_3484492 baseEnd_3484492 := by
    simpa [prefixWord, tailWord_3484492, baseEnd_3484492] using wordTrace_append hprefix tailTrace_3484492
  have hstable : (prefixWord ++ tailWord_3484492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484492).length < 2 ^ (prefixWord ++ tailWord_3484492).sum := by decide
  have hdescent : baseEnd_3484492 < baseStart_3484492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484526 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3484526 : Nat := 118140960795 + 3484526 * 2 ^ 59
def prefixEnd_3484526 : Nat := 4983230072969 + 3 ^ 40 * 3484526 * 2
def baseEnd_3484526 : Nat := 596412230362913003233321

theorem tailTrace_3484526 : CollatzResearch.WordTrace tailWord_3484526 prefixEnd_3484526 596412230362913003233321 := by
  unfold tailWord_3484526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886388021770610813351179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84727402782776591004539621 15886388021770610813351179)
  ·
    refine ⟨23829582032655916220026769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15886388021770610813351179 23829582032655916220026769)
    ·
      refine ⟨17872186524491937165020077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23829582032655916220026769 17872186524491937165020077)
      ·
        refine ⟨6702069946684476436882529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17872186524491937165020077 6702069946684476436882529)
        ·
          refine ⟨5026552460013357327661897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702069946684476436882529 5026552460013357327661897)
          ·
            refine ⟨3769914345010017995746423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026552460013357327661897 3769914345010017995746423)
            ·
              refine ⟨5654871517515026993619635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769914345010017995746423 5654871517515026993619635)
              ·
                refine ⟨8482307276272540490429453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654871517515026993619635 8482307276272540490429453)
                ·
                  refine ⟨3180865228602202683911045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8482307276272540490429453 3180865228602202683911045)
                  ·
                    refine ⟨596412230362913003233321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3180865228602202683911045 596412230362913003233321)
                    ·
                      rfl

theorem cell23_3484526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3484526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484526 prefixEnd_3484526 := by exact prefixLift 3484526
  have htrace : WordTrace (prefixWord ++ tailWord_3484526) baseStart_3484526 baseEnd_3484526 := by
    simpa [prefixWord, tailWord_3484526, baseEnd_3484526] using wordTrace_append hprefix tailTrace_3484526
  have hstable : (prefixWord ++ tailWord_3484526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484526).length < 2 ^ (prefixWord ++ tailWord_3484526).sum := by decide
  have hdescent : baseEnd_3484526 < baseStart_3484526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484552 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_3484552 : Nat := 118140960795 + 3484552 * 2 ^ 59
def prefixEnd_3484552 : Nat := 4983230072969 + 3 ^ 40 * 3484552 * 2
def baseEnd_3484552 : Nat := 596416680528585302658281

theorem tailTrace_3484552 : CollatzResearch.WordTrace tailWord_3484552 prefixEnd_3484552 596416680528585302658281 := by
  unfold tailWord_3484552
  simp only [CollatzResearch.WordTrace]
  refine ⟨63546026236035346473627955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84728034981380461964837273 63546026236035346473627955)
  ·
    refine ⟨95319039354053019710441933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63546026236035346473627955 95319039354053019710441933)
    ·
      refine ⟨35744639757769882391415725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95319039354053019710441933 35744639757769882391415725)
      ·
        refine ⟨13404239909163705896780897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35744639757769882391415725 13404239909163705896780897)
        ·
          refine ⟨10053179931872779422585673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13404239909163705896780897 10053179931872779422585673)
          ·
            refine ⟨7539884948904584566939255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10053179931872779422585673 7539884948904584566939255)
            ·
              refine ⟨11309827423356876850408883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539884948904584566939255 11309827423356876850408883)
              ·
                refine ⟨16964741135035315275613325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11309827423356876850408883 16964741135035315275613325)
                ·
                  refine ⟨6361777925638243228354997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16964741135035315275613325 6361777925638243228354997)
                  ·
                    refine ⟨596416680528585302658281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6361777925638243228354997 596416680528585302658281)
                    ·
                      rfl

theorem cell23_3484552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_3484552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484552 prefixEnd_3484552 := by exact prefixLift 3484552
  have htrace : WordTrace (prefixWord ++ tailWord_3484552) baseStart_3484552 baseEnd_3484552 := by
    simpa [prefixWord, tailWord_3484552, baseEnd_3484552] using wordTrace_append hprefix tailTrace_3484552
  have hstable : (prefixWord ++ tailWord_3484552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484552).length < 2 ^ (prefixWord ++ tailWord_3484552).sum := by decide
  have hdescent : baseEnd_3484552 < baseStart_3484552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484565 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_3484565 : Nat := 118140960795 + 3484565 * 2 ^ 59
def prefixEnd_3484565 : Nat := 4983230072969 + 3 ^ 40 * 3484565 * 2
def baseEnd_3484565 : Nat := 596418905611421452370761

theorem tailTrace_3484565 : CollatzResearch.WordTrace tailWord_3484565 prefixEnd_3484565 596418905611421452370761 := by
  unfold tailWord_3484565
  simp only [CollatzResearch.WordTrace]
  refine ⟨127092526621023596167479149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84728351080682397444986099 127092526621023596167479149)
  ·
    refine ⟨47659697482883848562804681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127092526621023596167479149 47659697482883848562804681)
    ·
      refine ⟨35744773112162886422103511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47659697482883848562804681 35744773112162886422103511)
      ·
        refine ⟨53617159668244329633155267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35744773112162886422103511 53617159668244329633155267)
        ·
          refine ⟨80425739502366494449732901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53617159668244329633155267 80425739502366494449732901)
          ·
            refine ⟨15079826156693717709324919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80425739502366494449732901 15079826156693717709324919)
            ·
              refine ⟨22619739235040576563987379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15079826156693717709324919 22619739235040576563987379)
              ·
                refine ⟨33929608852560864845981069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22619739235040576563987379 33929608852560864845981069)
                ·
                  refine ⟨12723603319710324317242901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33929608852560864845981069 12723603319710324317242901)
                  ·
                    refine ⟨596418905611421452370761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12723603319710324317242901 596418905611421452370761)
                    ·
                      rfl

theorem cell23_3484565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_3484565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484565 prefixEnd_3484565 := by exact prefixLift 3484565
  have htrace : WordTrace (prefixWord ++ tailWord_3484565) baseStart_3484565 baseEnd_3484565 := by
    simpa [prefixWord, tailWord_3484565, baseEnd_3484565] using wordTrace_append hprefix tailTrace_3484565
  have hstable : (prefixWord ++ tailWord_3484565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484565).length < 2 ^ (prefixWord ++ tailWord_3484565).sum := by decide
  have hdescent : baseEnd_3484565 < baseStart_3484565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484583 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_3484583 : Nat := 118140960795 + 3484583 * 2 ^ 59
def prefixEnd_3484583 : Nat := 4983230072969 + 3 ^ 40 * 3484583 * 2
def baseEnd_3484583 : Nat := 1789265959486045286687201

theorem tailTrace_3484583 : CollatzResearch.WordTrace tailWord_3484583 prefixEnd_3484583 1789265959486045286687201 := by
  unfold tailWord_3484583
  simp only [CollatzResearch.WordTrace]
  refine ⟨127093183134958385241634403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84728788756638923494422935 127093183134958385241634403)
  ·
    refine ⟨190639774702437577862451605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127093183134958385241634403 190639774702437577862451605)
    ·
      refine ⟨8936239439176761462302419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190639774702437577862451605 8936239439176761462302419)
      ·
        refine ⟨13404359158765142193453629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8936239439176761462302419 13404359158765142193453629)
        ·
          refine ⟨5026634684536928322545111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13404359158765142193453629 5026634684536928322545111)
          ·
            refine ⟨7539952026805392483817667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5026634684536928322545111 7539952026805392483817667)
            ·
              refine ⟨11309928040208088725726501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539952026805392483817667 11309928040208088725726501)
              ·
                refine ⟨2120611507539016636073719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11309928040208088725726501 2120611507539016636073719)
                ·
                  refine ⟨3180917261308524954110579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120611507539016636073719 3180917261308524954110579)
                  ·
                    refine ⟨4771375891962787431165869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3180917261308524954110579 4771375891962787431165869)
                    ·
                      refine ⟨1789265959486045286687201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4771375891962787431165869 1789265959486045286687201)
                      ·
                        rfl

theorem cell23_3484583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_3484583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484583 prefixEnd_3484583 := by exact prefixLift 3484583
  have htrace : WordTrace (prefixWord ++ tailWord_3484583) baseStart_3484583 baseEnd_3484583 := by
    simpa [prefixWord, tailWord_3484583, baseEnd_3484583] using wordTrace_append hprefix tailTrace_3484583
  have hstable : (prefixWord ++ tailWord_3484583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484583).length < 2 ^ (prefixWord ++ tailWord_3484583).sum := by decide
  have hdescent : baseEnd_3484583 < baseStart_3484583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484585 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_3484585 : Nat := 118140960795 + 3484585 * 2 ^ 59
def prefixEnd_3484585 : Nat := 4983230072969 + 3 ^ 40 * 3484585 * 2
def baseEnd_3484585 : Nat := 1789266986447354278862191

theorem tailTrace_3484585 : CollatzResearch.WordTrace tailWord_3484585 prefixEnd_3484585 1789266986447354278862191 := by
  unfold tailWord_3484585
  simp only [CollatzResearch.WordTrace]
  refine ⟨127093256080951139583207209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84728837387300759722138139 127093256080951139583207209)
  ·
    refine ⟨95319942060713354687405407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127093256080951139583207209 95319942060713354687405407)
    ·
      refine ⟨142979913091070032031108111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95319942060713354687405407 142979913091070032031108111)
      ·
        refine ⟨214469869636605048046662167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142979913091070032031108111 214469869636605048046662167)
        ·
          refine ⟨321704804454907572069993251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214469869636605048046662167 321704804454907572069993251)
          ·
            refine ⟨482557206682361358104989877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321704804454907572069993251 482557206682361358104989877)
            ·
              refine ⟨45239738126471377322342801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 482557206682361358104989877 45239738126471377322342801)
              ·
                refine ⟨33929803594853532991757101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45239738126471377322342801 33929803594853532991757101)
                ·
                  refine ⟨12723676348070074871908913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33929803594853532991757101 12723676348070074871908913)
                  ·
                    refine ⟨9542757261052556153931685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12723676348070074871908913 9542757261052556153931685)
                    ·
                      refine ⟨1789266986447354278862191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9542757261052556153931685 1789266986447354278862191)
                      ·
                        rfl

theorem cell23_3484585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_3484585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484585 prefixEnd_3484585 := by exact prefixLift 3484585
  have htrace : WordTrace (prefixWord ++ tailWord_3484585) baseStart_3484585 baseEnd_3484585 := by
    simpa [prefixWord, tailWord_3484585, baseEnd_3484585] using wordTrace_append hprefix tailTrace_3484585
  have hstable : (prefixWord ++ tailWord_3484585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484585).length < 2 ^ (prefixWord ++ tailWord_3484585).sum := by decide
  have hdescent : baseEnd_3484585 < baseStart_3484585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484602 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_3484602 : Nat := 118140960795 + 3484602 * 2 ^ 59
def prefixEnd_3484602 : Nat := 4983230072969 + 3 ^ 40 * 3484602 * 2
def baseEnd_3484602 : Nat := 1789275715618480712349613

theorem tailTrace_3484602 : CollatzResearch.WordTrace tailWord_3484602 prefixEnd_3484602 1789275715618480712349613 := by
  unfold tailWord_3484602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31773469030472387871644015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84729250747926367657717373 31773469030472387871644015)
  ·
    refine ⟨47660203545708581807466023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31773469030472387871644015 47660203545708581807466023)
    ·
      refine ⟨71490305318562872711199035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47660203545708581807466023 71490305318562872711199035)
      ·
        refine ⟨107235457977844309066798553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71490305318562872711199035 107235457977844309066798553)
        ·
          refine ⟨80426593483383231800098915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107235457977844309066798553 80426593483383231800098915)
          ·
            refine ⟨120639890225074847700148373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80426593483383231800098915 120639890225074847700148373)
            ·
              refine ⟨5654994854300383485944455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120639890225074847700148373 5654994854300383485944455)
              ·
                refine ⟨8482492281450575228916683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654994854300383485944455 8482492281450575228916683)
                ·
                  refine ⟨12723738422175862843375025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482492281450575228916683 12723738422175862843375025)
                  ·
                    refine ⟨9542803816631897132531269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12723738422175862843375025 9542803816631897132531269)
                    ·
                      refine ⟨1789275715618480712349613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9542803816631897132531269 1789275715618480712349613)
                      ·
                        rfl

theorem cell23_3484602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_3484602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484602 prefixEnd_3484602 := by exact prefixLift 3484602
  have htrace : WordTrace (prefixWord ++ tailWord_3484602) baseStart_3484602 baseEnd_3484602 := by
    simpa [prefixWord, tailWord_3484602, baseEnd_3484602] using wordTrace_append hprefix tailTrace_3484602
  have hstable : (prefixWord ++ tailWord_3484602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484602).length < 2 ^ (prefixWord ++ tailWord_3484602).sum := by decide
  have hdescent : baseEnd_3484602 < baseStart_3484602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484606 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_3484606 : Nat := 118140960795 + 3484606 * 2 ^ 59
def prefixEnd_3484606 : Nat := 4983230072969 + 3 ^ 40 * 3484606 * 2
def baseEnd_3484606 : Nat := 1789277769541098696699595

theorem tailTrace_3484606 : CollatzResearch.WordTrace tailWord_3484606 prefixEnd_3484606 1789277769541098696699595 := by
  unfold tailWord_3484606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886752751734382521215209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84729348009250040113147781 15886752751734382521215209)
  ·
    refine ⟨11915064563800786890911407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15886752751734382521215209 11915064563800786890911407)
    ·
      refine ⟨17872596845701180336367111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11915064563800786890911407 17872596845701180336367111)
      ·
        refine ⟨26808895268551770504550667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17872596845701180336367111 26808895268551770504550667)
        ·
          refine ⟨40213342902827655756826001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26808895268551770504550667 40213342902827655756826001)
          ·
            refine ⟨30160007177120741817619501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40213342902827655756826001 30160007177120741817619501)
            ·
              refine ⟨11310002691420278181607313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30160007177120741817619501 11310002691420278181607313)
              ·
                refine ⟨8482502018565208636205485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11310002691420278181607313 8482502018565208636205485)
                ·
                  refine ⟨3180938256961953238577057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8482502018565208636205485 3180938256961953238577057)
                  ·
                    refine ⟨2385703692721464928932793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3180938256961953238577057 2385703692721464928932793)
                    ·
                      refine ⟨1789277769541098696699595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385703692721464928932793 1789277769541098696699595)
                      ·
                        rfl

theorem cell23_3484606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_3484606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484606 prefixEnd_3484606 := by exact prefixLift 3484606
  have htrace : WordTrace (prefixWord ++ tailWord_3484606) baseStart_3484606 baseEnd_3484606 := by
    simpa [prefixWord, tailWord_3484606, baseEnd_3484606] using wordTrace_append hprefix tailTrace_3484606
  have hstable : (prefixWord ++ tailWord_3484606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484606).length < 2 ^ (prefixWord ++ tailWord_3484606).sum := by decide
  have hdescent : baseEnd_3484606 < baseStart_3484606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484623 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 1, 2, 2]
def baseStart_3484623 : Nat := 118140960795 + 3484623 * 2 ^ 59
def prefixEnd_3484623 : Nat := 4983230072969 + 3 ^ 40 * 3484623 * 2
def baseEnd_3484623 : Nat := 1789286498712225130187017

theorem tailTrace_3484623 : CollatzResearch.WordTrace tailWord_3484623 prefixEnd_3484623 1789286498712225130187017 := by
  unfold tailWord_3484623
  simp only [CollatzResearch.WordTrace]
  refine ⟨127094642054813472073090523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84729761369875648048727015 127094642054813472073090523)
  ·
    refine ⟨190641963082220208109635785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127094642054813472073090523 190641963082220208109635785)
    ·
      refine ⟨142981472311665156082226839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190641963082220208109635785 142981472311665156082226839)
      ·
        refine ⟨214472208467497734123340259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142981472311665156082226839 214472208467497734123340259)
        ·
          refine ⟨321708312701246601185010389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214472208467497734123340259 321708312701246601185010389)
          ·
            refine ⟨7540038578935467215273681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 321708312701246601185010389 7540038578935467215273681)
            ·
              refine ⟨5655028934201600411455261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7540038578935467215273681 5655028934201600411455261)
              ·
                refine ⟨2120635850325600154295723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5655028934201600411455261 2120635850325600154295723)
                ·
                  refine ⟨3180953775488400231443585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120635850325600154295723 3180953775488400231443585)
                  ·
                    refine ⟨2385715331616300173582689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3180953775488400231443585 2385715331616300173582689)
                    ·
                      refine ⟨1789286498712225130187017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385715331616300173582689 1789286498712225130187017)
                      ·
                        rfl

theorem cell23_3484623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 2, 2].length) (baseStart_3484623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484623 prefixEnd_3484623 := by exact prefixLift 3484623
  have htrace : WordTrace (prefixWord ++ tailWord_3484623) baseStart_3484623 baseEnd_3484623 := by
    simpa [prefixWord, tailWord_3484623, baseEnd_3484623] using wordTrace_append hprefix tailTrace_3484623
  have hstable : (prefixWord ++ tailWord_3484623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484623).length < 2 ^ (prefixWord ++ tailWord_3484623).sum := by decide
  have hdescent : baseEnd_3484623 < baseStart_3484623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484626 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3484626 : Nat := 118140960795 + 3484626 * 2 ^ 59
def prefixEnd_3484626 : Nat := 4983230072969 + 3 ^ 40 * 3484626 * 2
def baseEnd_3484626 : Nat := 1789288039154188618449503

theorem tailTrace_3484626 : CollatzResearch.WordTrace tailWord_3484626 prefixEnd_3484626 1789288039154188618449503 := by
  unfold tailWord_3484626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31773687868450650896362433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84729834315868402390299821 31773687868450650896362433)
  ·
    refine ⟨23830265901337988172271825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31773687868450650896362433 23830265901337988172271825)
    ·
      refine ⟨17872699426003491129203869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23830265901337988172271825 17872699426003491129203869)
      ·
        refine ⟨6702262284751309173451451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17872699426003491129203869 6702262284751309173451451)
        ·
          refine ⟨10053393427126963760177177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702262284751309173451451 10053393427126963760177177)
          ·
            refine ⟨7540045070345222820132883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10053393427126963760177177 7540045070345222820132883)
            ·
              refine ⟨11310067605517834230199325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540045070345222820132883 11310067605517834230199325)
              ·
                refine ⟨4241275352069187836324747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11310067605517834230199325 4241275352069187836324747)
                ·
                  refine ⟨6361913028103781754487121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241275352069187836324747 6361913028103781754487121)
                  ·
                    refine ⟨4771434771077836315865341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361913028103781754487121 4771434771077836315865341)
                    ·
                      refine ⟨1789288039154188618449503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4771434771077836315865341 1789288039154188618449503)
                      ·
                        rfl

theorem cell23_3484626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3484626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484626 prefixEnd_3484626 := by exact prefixLift 3484626
  have htrace : WordTrace (prefixWord ++ tailWord_3484626) baseStart_3484626 baseEnd_3484626 := by
    simpa [prefixWord, tailWord_3484626, baseEnd_3484626] using wordTrace_append hprefix tailTrace_3484626
  have hstable : (prefixWord ++ tailWord_3484626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484626).length < 2 ^ (prefixWord ++ tailWord_3484626).sum := by decide
  have hdescent : baseEnd_3484626 < baseStart_3484626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484674 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3484674 : Nat := 118140960795 + 3484674 * 2 ^ 59
def prefixEnd_3484674 : Nat := 4983230072969 + 3 ^ 40 * 3484674 * 2
def baseEnd_3484674 : Nat := 1789312686225604430649283

theorem tailTrace_3484674 : CollatzResearch.WordTrace tailWord_3484674 prefixEnd_3484674 1789312686225604430649283 := by
  unfold tailWord_3484674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31774125544407176945799269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84731001451752471855464717 31774125544407176945799269)
  ·
    refine ⟨5957648539576345677337363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31774125544407176945799269 5957648539576345677337363)
    ·
      refine ⟨8936472809364518516006045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5957648539576345677337363 8936472809364518516006045)
      ·
        refine ⟨3351177303511694443502267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8936472809364518516006045 3351177303511694443502267)
        ·
          refine ⟨5026765955267541665253401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351177303511694443502267 5026765955267541665253401)
          ·
            refine ⟨3770074466450656248940051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026765955267541665253401 3770074466450656248940051)
            ·
              refine ⟨5655111699675984373410077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770074466450656248940051 5655111699675984373410077)
              ·
                refine ⟨2120666887378494140028779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5655111699675984373410077 2120666887378494140028779)
                ·
                  refine ⟨3181000331067741210043169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120666887378494140028779 3181000331067741210043169)
                  ·
                    refine ⟨2385750248300805907532377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3181000331067741210043169 2385750248300805907532377)
                    ·
                      refine ⟨1789312686225604430649283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385750248300805907532377 1789312686225604430649283)
                      ·
                        rfl

theorem cell23_3484674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3484674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484674 prefixEnd_3484674 := by exact prefixLift 3484674
  have htrace : WordTrace (prefixWord ++ tailWord_3484674) baseStart_3484674 baseEnd_3484674 := by
    simpa [prefixWord, tailWord_3484674, baseEnd_3484674] using wordTrace_append hprefix tailTrace_3484674
  have hstable : (prefixWord ++ tailWord_3484674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484674).length < 2 ^ (prefixWord ++ tailWord_3484674).sum := by decide
  have hdescent : baseEnd_3484674 < baseStart_3484674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484679 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_3484679 : Nat := 118140960795 + 3484679 * 2 ^ 59
def prefixEnd_3484679 : Nat := 4983230072969 + 3 ^ 40 * 3484679 * 2
def baseEnd_3484679 : Nat := 1789315253628876911086759

theorem tailTrace_3484679 : CollatzResearch.WordTrace tailWord_3484679 prefixEnd_3484679 1789315253628876911086759 := by
  unfold tailWord_3484679
  simp only [CollatzResearch.WordTrace]
  refine ⟨127096684542610593637129091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84731123028407062424752727 127096684542610593637129091)
  ·
    refine ⟨190645026813915890455693637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127096684542610593637129091 190645026813915890455693637)
    ·
      refine ⟨35745942527609229460442557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190645026813915890455693637 35745942527609229460442557)
      ·
        refine ⟨13404728447853461047665959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35745942527609229460442557 13404728447853461047665959)
        ·
          refine ⟨20107092671780191571498939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13404728447853461047665959 20107092671780191571498939)
          ·
            refine ⟨30160639007670287357248409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20107092671780191571498939 30160639007670287357248409)
            ·
              refine ⟨22620479255752715517936307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30160639007670287357248409 22620479255752715517936307)
              ·
                refine ⟨33930718883629073276904461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22620479255752715517936307 33930718883629073276904461)
                ·
                  refine ⟨12724019581360902478839173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33930718883629073276904461 12724019581360902478839173)
                  ·
                    refine ⟨2385753671505169214782345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12724019581360902478839173 2385753671505169214782345)
                    ·
                      refine ⟨1789315253628876911086759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385753671505169214782345 1789315253628876911086759)
                      ·
                        rfl

theorem cell23_3484679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_3484679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484679 prefixEnd_3484679 := by exact prefixLift 3484679
  have htrace : WordTrace (prefixWord ++ tailWord_3484679) baseStart_3484679 baseEnd_3484679 := by
    simpa [prefixWord, tailWord_3484679, baseEnd_3484679] using wordTrace_append hprefix tailTrace_3484679
  have hstable : (prefixWord ++ tailWord_3484679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484679).length < 2 ^ (prefixWord ++ tailWord_3484679).sum := by decide
  have hdescent : baseEnd_3484679 < baseStart_3484679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484682 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3484682 : Nat := 118140960795 + 3484682 * 2 ^ 59
def prefixEnd_3484682 : Nat := 4983230072969 + 3 ^ 40 * 3484682 * 2
def baseEnd_3484682 : Nat := 1789316794070840399349245

theorem tailTrace_3484682 : CollatzResearch.WordTrace tailWord_3484682 prefixEnd_3484682 1789316794070840399349245 := by
  unfold tailWord_3484682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31774198490399931287372075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84731195974399816766325533 31774198490399931287372075)
  ·
    refine ⟨47661297735599896931058113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31774198490399931287372075 47661297735599896931058113)
    ·
      refine ⟨35745973301699922698293585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47661297735599896931058113 35745973301699922698293585)
      ·
        refine ⟨26809479976274942023720189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35745973301699922698293585 26809479976274942023720189)
        ·
          refine ⟨10053554991103103258895071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26809479976274942023720189 10053554991103103258895071)
          ·
            refine ⟨15080332486654654888342607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053554991103103258895071 15080332486654654888342607)
            ·
              refine ⟨22620498729981982332513911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15080332486654654888342607 22620498729981982332513911)
              ·
                refine ⟨33930748094972973498770867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22620498729981982332513911 33930748094972973498770867)
                ·
                  refine ⟨50896122142459460248156301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33930748094972973498770867 50896122142459460248156301)
                  ·
                    refine ⟨19086045803422297593058613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50896122142459460248156301 19086045803422297593058613)
                    ·
                      refine ⟨1789316794070840399349245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19086045803422297593058613 1789316794070840399349245)
                      ·
                        rfl

theorem cell23_3484682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3484682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484682 prefixEnd_3484682 := by exact prefixLift 3484682
  have htrace : WordTrace (prefixWord ++ tailWord_3484682) baseStart_3484682 baseEnd_3484682 := by
    simpa [prefixWord, tailWord_3484682, baseEnd_3484682] using wordTrace_append hprefix tailTrace_3484682
  have hstable : (prefixWord ++ tailWord_3484682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484682).length < 2 ^ (prefixWord ++ tailWord_3484682).sum := by decide
  have hdescent : baseEnd_3484682 < baseStart_3484682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484696 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 4, 2, 2]
def baseStart_3484696 : Nat := 118140960795 + 3484696 * 2 ^ 59
def prefixEnd_3484696 : Nat := 4983230072969 + 3 ^ 40 * 3484696 * 2
def baseEnd_3484696 : Nat := 1789323982800003344574181

theorem tailTrace_3484696 : CollatzResearch.WordTrace tailWord_3484696 prefixEnd_3484696 1789323982800003344574181 := by
  unfold tailWord_3484696
  simp only [CollatzResearch.WordTrace]
  refine ⟨63548652291774502770248971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84731536389032670360331961 63548652291774502770248971)
  ·
    refine ⟨95322978437661754155373457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63548652291774502770248971 95322978437661754155373457)
    ·
      refine ⟨71492233828246315616530093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95322978437661754155373457 71492233828246315616530093)
      ·
        refine ⟨26809587685592368356198785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71492233828246315616530093 26809587685592368356198785)
        ·
          refine ⟨20107190764194276267149089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26809587685592368356198785 20107190764194276267149089)
          ·
            refine ⟨15080393073145707200361817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20107190764194276267149089 15080393073145707200361817)
            ·
              refine ⟨11310294804859280400271363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15080393073145707200361817 11310294804859280400271363)
              ·
                refine ⟨16965442207288920600407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310294804859280400271363 16965442207288920600407045)
                ·
                  refine ⟨3181020413866672612576321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16965442207288920600407045 3181020413866672612576321)
                  ·
                    refine ⟨2385765310400004459432241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3181020413866672612576321 2385765310400004459432241)
                    ·
                      refine ⟨1789323982800003344574181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385765310400004459432241 1789323982800003344574181)
                      ·
                        rfl

theorem cell23_3484696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_3484696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484696 prefixEnd_3484696 := by exact prefixLift 3484696
  have htrace : WordTrace (prefixWord ++ tailWord_3484696) baseStart_3484696 baseEnd_3484696 := by
    simpa [prefixWord, tailWord_3484696, baseEnd_3484696] using wordTrace_append hprefix tailTrace_3484696
  have hstable : (prefixWord ++ tailWord_3484696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484696).length < 2 ^ (prefixWord ++ tailWord_3484696).sum := by decide
  have hdescent : baseEnd_3484696 < baseStart_3484696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484769 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_3484769 : Nat := 118140960795 + 3484769 * 2 ^ 59
def prefixEnd_3484769 : Nat := 4983230072969 + 3 ^ 40 * 3484769 * 2
def baseEnd_3484769 : Nat := 1789361466887781558961345

theorem tailTrace_3484769 : CollatzResearch.WordTrace tailWord_3484769 prefixEnd_3484769 1789361466887781558961345 := by
  unfold tailWord_3484769
  simp only [CollatzResearch.WordTrace]
  refine ⟨127099967112284539007905361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84733311408189692671936907 127099967112284539007905361)
  ·
    refine ⟨95324975334213404255929021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127099967112284539007905361 95324975334213404255929021)
    ·
      refine ⟨35746865750330026595973383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95324975334213404255929021 35746865750330026595973383)
      ·
        refine ⟨53620298625495039893960075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35746865750330026595973383 53620298625495039893960075)
        ·
          refine ⟨80430447938242559840940113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53620298625495039893960075 80430447938242559840940113)
          ·
            refine ⟨60322835953681919880705085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80430447938242559840940113 60322835953681919880705085)
            ·
              refine ⟨22621063482630719955264407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60322835953681919880705085 22621063482630719955264407)
              ·
                refine ⟨33931595223946079932896611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22621063482630719955264407 33931595223946079932896611)
                ·
                  refine ⟨50897392835919119899344917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33931595223946079932896611 50897392835919119899344917)
                  ·
                    refine ⟨2385815289183708745281793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50897392835919119899344917 2385815289183708745281793)
                    ·
                      refine ⟨1789361466887781558961345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385815289183708745281793 1789361466887781558961345)
                      ·
                        rfl

theorem cell23_3484769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_3484769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484769 prefixEnd_3484769 := by exact prefixLift 3484769
  have htrace : WordTrace (prefixWord ++ tailWord_3484769) baseStart_3484769 baseEnd_3484769 := by
    simpa [prefixWord, tailWord_3484769, baseEnd_3484769] using wordTrace_append hprefix tailTrace_3484769
  have hstable : (prefixWord ++ tailWord_3484769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484769).length < 2 ^ (prefixWord ++ tailWord_3484769).sum := by decide
  have hdescent : baseEnd_3484769 < baseStart_3484769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484809 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 6]
def baseStart_3484809 : Nat := 118140960795 + 3484809 * 2 ^ 59
def prefixEnd_3484809 : Nat := 4983230072969 + 3 ^ 40 * 3484809 * 2
def baseEnd_3484809 : Nat := 198820222901551266940129

theorem tailTrace_3484809 : CollatzResearch.WordTrace tailWord_3484809 prefixEnd_3484809 198820222901551266940129 := by
  unfold tailWord_3484809
  simp only [CollatzResearch.WordTrace]
  refine ⟨127101426032139625839361481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84734284021426417226240987 127101426032139625839361481)
  ·
    refine ⟨95326069524104719379521111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127101426032139625839361481 95326069524104719379521111)
    ·
      refine ⟨142989104286157079069281667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95326069524104719379521111 142989104286157079069281667)
      ·
        refine ⟨214483656429235618603922501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142989104286157079069281667 214483656429235618603922501)
        ·
          refine ⟨40215685580481678488235469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214483656429235618603922501 40215685580481678488235469)
          ·
            refine ⟨15080882092680629433088301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40215685580481678488235469 15080882092680629433088301)
            ·
              refine ⟨5655330784755236037408113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15080882092680629433088301 5655330784755236037408113)
              ·
                refine ⟨4241498088566427028056085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5655330784755236037408113 4241498088566427028056085)
                ·
                  refine ⟨198820222901551266940129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4241498088566427028056085 198820222901551266940129)
                  ·
                    rfl

theorem cell23_3484809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_3484809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484809 prefixEnd_3484809 := by exact prefixLift 3484809
  have htrace : WordTrace (prefixWord ++ tailWord_3484809) baseStart_3484809 baseEnd_3484809 := by
    simpa [prefixWord, tailWord_3484809, baseEnd_3484809] using wordTrace_append hprefix tailTrace_3484809
  have hstable : (prefixWord ++ tailWord_3484809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484809).length < 2 ^ (prefixWord ++ tailWord_3484809).sum := by decide
  have hdescent : baseEnd_3484809 < baseStart_3484809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484877 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 6]
def baseStart_3484877 : Nat := 118140960795 + 3484877 * 2 ^ 59
def prefixEnd_3484877 : Nat := 4983230072969 + 3 ^ 40 * 3484877 * 2
def baseEnd_3484877 : Nat := 198824102533163015156761

theorem tailTrace_3484877 : CollatzResearch.WordTrace tailWord_3484877 prefixEnd_3484877 198824102533163015156761 := by
  unfold tailWord_3484877
  simp only [CollatzResearch.WordTrace]
  refine ⟨127103906195893273452836885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84735937463928848968557923 127103906195893273452836885)
  ·
    refine ⟨5957995602932497193101729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127103906195893273452836885 5957995602932497193101729)
    ·
      refine ⟨4468496702199372894826297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5957995602932497193101729 4468496702199372894826297)
      ·
        refine ⟨3351372526649529671119723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4468496702199372894826297 3351372526649529671119723)
        ·
          refine ⟨5027058789974294506679585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351372526649529671119723 5027058789974294506679585)
          ·
            refine ⟨3770294092480720880009689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5027058789974294506679585 3770294092480720880009689)
            ·
              refine ⟨2827720569360540660007267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770294092480720880009689 2827720569360540660007267)
              ·
                refine ⟨4241580854040810990010901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827720569360540660007267 4241580854040810990010901)
                ·
                  refine ⟨198824102533163015156761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4241580854040810990010901 198824102533163015156761)
                  ·
                    rfl

theorem cell23_3484877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_3484877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484877 prefixEnd_3484877 := by exact prefixLift 3484877
  have htrace : WordTrace (prefixWord ++ tailWord_3484877) baseStart_3484877 baseEnd_3484877 := by
    simpa [prefixWord, tailWord_3484877, baseEnd_3484877] using wordTrace_append hprefix tailTrace_3484877
  have hstable : (prefixWord ++ tailWord_3484877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484877).length < 2 ^ (prefixWord ++ tailWord_3484877).sum := by decide
  have hdescent : baseEnd_3484877 < baseStart_3484877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484889 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_3484889 : Nat := 118140960795 + 3484889 * 2 ^ 59
def prefixEnd_3484889 : Nat := 4983230072969 + 3 ^ 40 * 3484889 * 2
def baseEnd_3484889 : Nat := 1789423084566321089460793

theorem tailTrace_3484889 : CollatzResearch.WordTrace tailWord_3484889 prefixEnd_3484889 1789423084566321089460793 := by
  unfold tailWord_3484889
  simp only [CollatzResearch.WordTrace]
  refine ⟨127104343871849799502273721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84736229247899866334849147 127104343871849799502273721)
  ·
    refine ⟨95328257903887349626705291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127104343871849799502273721 95328257903887349626705291)
    ·
      refine ⟨142992386855831024440057937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95328257903887349626705291 142992386855831024440057937)
      ·
        refine ⟨107244290141873268330043453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142992386855831024440057937 107244290141873268330043453)
        ·
          refine ⟨40216608803202475623766295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107244290141873268330043453 40216608803202475623766295)
          ·
            refine ⟨60324913204803713435649443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40216608803202475623766295 60324913204803713435649443)
            ·
              refine ⟨90487369807205570153474165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60324913204803713435649443 90487369807205570153474165)
              ·
                refine ⟨8483190919425522201888203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90487369807205570153474165 8483190919425522201888203)
                ·
                  refine ⟨12724786379138283302832305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8483190919425522201888203 12724786379138283302832305)
                  ·
                    refine ⟨9543589784353712477124229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12724786379138283302832305 9543589784353712477124229)
                    ·
                      refine ⟨1789423084566321089460793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9543589784353712477124229 1789423084566321089460793)
                      ·
                        rfl

theorem cell23_3484889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_3484889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484889 prefixEnd_3484889 := by exact prefixLift 3484889
  have htrace : WordTrace (prefixWord ++ tailWord_3484889) baseStart_3484889 baseEnd_3484889 := by
    simpa [prefixWord, tailWord_3484889, baseEnd_3484889] using wordTrace_append hprefix tailTrace_3484889
  have hstable : (prefixWord ++ tailWord_3484889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484889).length < 2 ^ (prefixWord ++ tailWord_3484889).sum := by decide
  have hdescent : baseEnd_3484889 < baseStart_3484889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484893 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3484893 : Nat := 118140960795 + 3484893 * 2 ^ 59
def prefixEnd_3484893 : Nat := 4983230072969 + 3 ^ 40 * 3484893 * 2
def baseEnd_3484893 : Nat := 1789425138488939073810775

theorem tailTrace_3484893 : CollatzResearch.WordTrace tailWord_3484893 prefixEnd_3484893 1789425138488939073810775 := by
  unfold tailWord_3484893
  simp only [CollatzResearch.WordTrace]
  refine ⟨127104489763835308185419333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84736326509223538790279555 127104489763835308185419333)
  ·
    refine ⟨23832091830719120284766125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127104489763835308185419333 23832091830719120284766125)
    ·
      refine ⟨8937034436519670106787297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23832091830719120284766125 8937034436519670106787297)
      ·
        refine ⟨6702775827389752580090473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8937034436519670106787297 6702775827389752580090473)
        ·
          refine ⟨5027081870542314435067855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702775827389752580090473 5027081870542314435067855)
          ·
            refine ⟨7540622805813471652601783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027081870542314435067855 7540622805813471652601783)
            ·
              refine ⟨11310934208720207478902675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540622805813471652601783 11310934208720207478902675)
              ·
                refine ⟨16966401313080311218354013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310934208720207478902675 16966401313080311218354013)
                ·
                  refine ⟨6362400492405116706882755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16966401313080311218354013 6362400492405116706882755)
                  ·
                    refine ⟨9543600738607675060324133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6362400492405116706882755 9543600738607675060324133)
                    ·
                      refine ⟨1789425138488939073810775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9543600738607675060324133 1789425138488939073810775)
                      ·
                        rfl

theorem cell23_3484893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3484893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484893 prefixEnd_3484893 := by exact prefixLift 3484893
  have htrace : WordTrace (prefixWord ++ tailWord_3484893) baseStart_3484893 baseEnd_3484893 := by
    simpa [prefixWord, tailWord_3484893, baseEnd_3484893] using wordTrace_append hprefix tailTrace_3484893
  have hstable : (prefixWord ++ tailWord_3484893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484893).length < 2 ^ (prefixWord ++ tailWord_3484893).sum := by decide
  have hdescent : baseEnd_3484893 < baseStart_3484893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484896 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_3484896 : Nat := 118140960795 + 3484896 * 2 ^ 59
def prefixEnd_3484896 : Nat := 4983230072969 + 3 ^ 40 * 3484896 * 2
def baseEnd_3484896 : Nat := 1789426678930902562073261

theorem tailTrace_3484896 : CollatzResearch.WordTrace tailWord_3484896 prefixEnd_3484896 1789426678930902562073261 := by
  unfold tailWord_3484896
  simp only [CollatzResearch.WordTrace]
  refine ⟨63552299591412219848889271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84736399455216293131852361 63552299591412219848889271)
  ·
    refine ⟨95328449387118329773333907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63552299591412219848889271 95328449387118329773333907)
    ·
      refine ⟨142992674080677494660000861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95328449387118329773333907 142992674080677494660000861)
      ·
        refine ⟨53622252780254060497500323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142992674080677494660000861 53622252780254060497500323)
        ·
          refine ⟨80433379170381090746250485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53622252780254060497500323 80433379170381090746250485)
          ·
            refine ⟨7540629297223227257460983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80433379170381090746250485 7540629297223227257460983)
            ·
              refine ⟨11310943945834840886191475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540629297223227257460983 11310943945834840886191475)
              ·
                refine ⟨16966415918752261329287213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310943945834840886191475 16966415918752261329287213)
                ·
                  refine ⟨6362405969532097998482705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16966415918752261329287213 6362405969532097998482705)
                  ·
                    refine ⟨4771804477149073498862029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6362405969532097998482705 4771804477149073498862029)
                    ·
                      refine ⟨1789426678930902562073261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4771804477149073498862029 1789426678930902562073261)
                      ·
                        rfl

theorem cell23_3484896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_3484896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484896 prefixEnd_3484896 := by exact prefixLift 3484896
  have htrace : WordTrace (prefixWord ++ tailWord_3484896) baseStart_3484896 baseEnd_3484896 := by
    simpa [prefixWord, tailWord_3484896, baseEnd_3484896] using wordTrace_append hprefix tailTrace_3484896
  have hstable : (prefixWord ++ tailWord_3484896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484896).length < 2 ^ (prefixWord ++ tailWord_3484896).sum := by decide
  have hdescent : baseEnd_3484896 < baseStart_3484896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484906 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_3484906 : Nat := 118140960795 + 3484906 * 2 ^ 59
def prefixEnd_3484906 : Nat := 4983230072969 + 3 ^ 40 * 3484906 * 2
def baseEnd_3484906 : Nat := 1789431813737447522948215

theorem tailTrace_3484906 : CollatzResearch.WordTrace tailWord_3484906 prefixEnd_3484906 1789431813737447522948215 := by
  unfold tailWord_3484906
  simp only [CollatzResearch.WordTrace]
  refine ⟨31776240978197052851410643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84736642608525474270428381 31776240978197052851410643)
  ·
    refine ⟨47664361467295579277115965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31776240978197052851410643 47664361467295579277115965)
    ·
      refine ⟨17874135550235842228918487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47664361467295579277115965 17874135550235842228918487)
      ·
        refine ⟨26811203325353763343377731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17874135550235842228918487 26811203325353763343377731)
        ·
          refine ⟨40216804988030645015066597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26811203325353763343377731 40216804988030645015066597)
          ·
            refine ⟨7540650935255745940324987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40216804988030645015066597 7540650935255745940324987)
            ·
              refine ⟨11310976402883618910487481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540650935255745940324987 11310976402883618910487481)
              ·
                refine ⟨8483232302162714182865611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11310976402883618910487481 8483232302162714182865611)
                ·
                  refine ⟨12724848453244071274298417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8483232302162714182865611 12724848453244071274298417)
                  ·
                    refine ⟨9543636339933053455723813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12724848453244071274298417 9543636339933053455723813)
                    ·
                      refine ⟨1789431813737447522948215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9543636339933053455723813 1789431813737447522948215)
                      ·
                        rfl

theorem cell23_3484906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_3484906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484906 prefixEnd_3484906 := by exact prefixLift 3484906
  have htrace : WordTrace (prefixWord ++ tailWord_3484906) baseStart_3484906 baseEnd_3484906 := by
    simpa [prefixWord, tailWord_3484906, baseEnd_3484906] using wordTrace_append hprefix tailTrace_3484906
  have hstable : (prefixWord ++ tailWord_3484906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484906).length < 2 ^ (prefixWord ++ tailWord_3484906).sum := by decide
  have hdescent : baseEnd_3484906 < baseStart_3484906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484927 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 1, 2, 2]
def baseStart_3484927 : Nat := 118140960795 + 3484927 * 2 ^ 59
def prefixEnd_3484927 : Nat := 4983230072969 + 3 ^ 40 * 3484927 * 2
def baseEnd_3484927 : Nat := 1789442596831191940785619

theorem tailTrace_3484927 : CollatzResearch.WordTrace tailWord_3484927 prefixEnd_3484927 1789442596831191940785619 := by
  unfold tailWord_3484927
  simp only [CollatzResearch.WordTrace]
  refine ⟨127105729845712131992157035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84737153230474754661438023 127105729845712131992157035)
  ·
    refine ⟨190658594768568197988235553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127105729845712131992157035 190658594768568197988235553)
    ·
      refine ⟨142993946076426148491176665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190658594768568197988235553 142993946076426148491176665)
      ·
        refine ⟨107245459557319611368382499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142993946076426148491176665 107245459557319611368382499)
        ·
          refine ⟨160868189335979417052573749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107245459557319611368382499 160868189335979417052573749)
          ·
            refine ⟨15081392750248070348678789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160868189335979417052573749 15081392750248070348678789)
            ·
              refine ⟨2827761140671513190377273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15081392750248070348678789 2827761140671513190377273)
              ·
                refine ⟨2120820855503634892782955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827761140671513190377273 2120820855503634892782955)
                ·
                  refine ⟨3181231283255452339174433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120820855503634892782955 3181231283255452339174433)
                  ·
                    refine ⟨2385923462441589254380825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3181231283255452339174433 2385923462441589254380825)
                    ·
                      refine ⟨1789442596831191940785619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2385923462441589254380825 1789442596831191940785619)
                      ·
                        rfl

theorem cell23_3484927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_3484927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484927 prefixEnd_3484927 := by exact prefixLift 3484927
  have htrace : WordTrace (prefixWord ++ tailWord_3484927) baseStart_3484927 baseEnd_3484927 := by
    simpa [prefixWord, tailWord_3484927, baseEnd_3484927] using wordTrace_append hprefix tailTrace_3484927
  have hstable : (prefixWord ++ tailWord_3484927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484927).length < 2 ^ (prefixWord ++ tailWord_3484927).sum := by decide
  have hdescent : baseEnd_3484927 < baseStart_3484927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484929 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3484929 : Nat := 118140960795 + 3484929 * 2 ^ 59
def prefixEnd_3484929 : Nat := 4983230072969 + 3 ^ 40 * 3484929 * 2
def baseEnd_3484929 : Nat := 596481207930833644320203

theorem tailTrace_3484929 : CollatzResearch.WordTrace tailWord_3484929 prefixEnd_3484929 596481207930833644320203 := by
  unfold tailWord_3484929
  simp only [CollatzResearch.WordTrace]
  refine ⟨127105802791704886333729841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84737201861136590889153227 127105802791704886333729841)
  ·
    refine ⟨95329352093778664750297381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127105802791704886333729841 95329352093778664750297381)
    ·
      refine ⟨17874253517583499640680759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95329352093778664750297381 17874253517583499640680759)
      ·
        refine ⟨26811380276375249461021139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17874253517583499640680759 26811380276375249461021139)
        ·
          refine ⟨40217070414562874191531709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26811380276375249461021139 40217070414562874191531709)
          ·
            refine ⟨15081401405461077821824391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40217070414562874191531709 15081401405461077821824391)
            ·
              refine ⟨22622102108191616732736587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15081401405461077821824391 22622102108191616732736587)
              ·
                refine ⟨33933153162287425099104881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22622102108191616732736587 33933153162287425099104881)
                ·
                  refine ⟨25449864871715568824328661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33933153162287425099104881 25449864871715568824328661)
                  ·
                    refine ⟨596481207930833644320203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25449864871715568824328661 596481207930833644320203)
                    ·
                      rfl

theorem cell23_3484929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3484929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484929 prefixEnd_3484929 := by exact prefixLift 3484929
  have htrace : WordTrace (prefixWord ++ tailWord_3484929) baseStart_3484929 baseEnd_3484929 := by
    simpa [prefixWord, tailWord_3484929, baseEnd_3484929] using wordTrace_append hprefix tailTrace_3484929
  have hstable : (prefixWord ++ tailWord_3484929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484929).length < 2 ^ (prefixWord ++ tailWord_3484929).sum := by decide
  have hdescent : baseEnd_3484929 < baseStart_3484929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484949 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_3484949 : Nat := 118140960795 + 3484949 * 2 ^ 59
def prefixEnd_3484949 : Nat := 4983230072969 + 3 ^ 40 * 3484949 * 2
def baseEnd_3484949 : Nat := 1789453893405590854710517

theorem tailTrace_3484949 : CollatzResearch.WordTrace tailWord_3484949 prefixEnd_3484949 1789453893405590854710517 := by
  unfold tailWord_3484949
  simp only [CollatzResearch.WordTrace]
  refine ⟨127106532251632429749457901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84737688167754953166305267 127106532251632429749457901)
  ·
    refine ⟨47664949594362161156046713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127106532251632429749457901 47664949594362161156046713)
    ·
      refine ⟨35748712195771620867035035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47664949594362161156046713 35748712195771620867035035)
      ·
        refine ⟨53623068293657431300552553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35748712195771620867035035 53623068293657431300552553)
        ·
          refine ⟨40217301220243073475414415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53623068293657431300552553 40217301220243073475414415)
          ·
            refine ⟨60325951830364610213121623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40217301220243073475414415 60325951830364610213121623)
            ·
              refine ⟨90488927745546915319682435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60325951830364610213121623 90488927745546915319682435)
              ·
                refine ⟨135733391618320372979523653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90488927745546915319682435 135733391618320372979523653)
                ·
                  refine ⟨25450010928435069933660685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135733391618320372979523653 25450010928435069933660685)
                  ·
                    refine ⟨9543754098163151225122757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25450010928435069933660685 9543754098163151225122757)
                    ·
                      refine ⟨1789453893405590854710517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9543754098163151225122757 1789453893405590854710517)
                      ·
                        rfl

theorem cell23_3484949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_3484949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3484949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3484949 prefixEnd_3484949 := by exact prefixLift 3484949
  have htrace : WordTrace (prefixWord ++ tailWord_3484949) baseStart_3484949 baseEnd_3484949 := by
    simpa [prefixWord, tailWord_3484949, baseEnd_3484949] using wordTrace_append hprefix tailTrace_3484949
  have hstable : (prefixWord ++ tailWord_3484949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484949).length < 2 ^ (prefixWord ++ tailWord_3484949).sum := by decide
  have hdescent : baseEnd_3484949 < baseStart_3484949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485036 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_3485036 : Nat := 118140960795 + 3485036 * 2 ^ 59
def prefixEnd_3485036 : Nat := 4983230072969 + 3 ^ 40 * 3485036 * 2
def baseEnd_3485036 : Nat := 596499522074177338107539

theorem tailTrace_3485036 : CollatzResearch.WordTrace tailWord_3485036 prefixEnd_3485036 596499522074177338107539 := by
  unfold tailWord_3485036
  simp only [CollatzResearch.WordTrace]
  refine ⟨63554852701158621803937481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84739803601544829071916641 63554852701158621803937481)
  ·
    refine ⟨47666139525868966352953111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63554852701158621803937481 47666139525868966352953111)
    ·
      refine ⟨71499209288803449529429667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47666139525868966352953111 71499209288803449529429667)
      ·
        refine ⟨107248813933205174294144501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71499209288803449529429667 107248813933205174294144501)
        ·
          refine ⟨10054576306237985090076047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107248813933205174294144501 10054576306237985090076047)
          ·
            refine ⟨15081864459356977635114071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054576306237985090076047 15081864459356977635114071)
            ·
              refine ⟨22622796689035466452671107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15081864459356977635114071 22622796689035466452671107)
              ·
                refine ⟨33934195033553199679006661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22622796689035466452671107 33934195033553199679006661)
                ·
                  refine ⟨6362661568791224939813749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33934195033553199679006661 6362661568791224939813749)
                  ·
                    refine ⟨596499522074177338107539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6362661568791224939813749 596499522074177338107539)
                    ·
                      rfl

theorem cell23_3485036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_3485036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485036 prefixEnd_3485036 := by exact prefixLift 3485036
  have htrace : WordTrace (prefixWord ++ tailWord_3485036) baseStart_3485036 baseEnd_3485036 := by
    simpa [prefixWord, tailWord_3485036, baseEnd_3485036] using wordTrace_append hprefix tailTrace_3485036
  have hstable : (prefixWord ++ tailWord_3485036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485036).length < 2 ^ (prefixWord ++ tailWord_3485036).sum := by decide
  have hdescent : baseEnd_3485036 < baseStart_3485036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485070 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3485070 : Nat := 118140960795 + 3485070 * 2 ^ 59
def prefixEnd_3485070 : Nat := 4983230072969 + 3 ^ 40 * 3485070 * 2
def baseEnd_3485070 : Nat := 596505341521594960432487

theorem tailTrace_3485070 : CollatzResearch.WordTrace tailWord_3485070 prefixEnd_3485070 596505341521594960432487 := by
  unfold tailWord_3485070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15888868185524258426826583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84740630322796044943075109 15888868185524258426826583)
  ·
    refine ⟨23833302278286387640239875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15888868185524258426826583 23833302278286387640239875)
    ·
      refine ⟨35749953417429581460359813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23833302278286387640239875 35749953417429581460359813)
      ·
        refine ⟨6703116265768046523817465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35749953417429581460359813 6703116265768046523817465)
        ·
          refine ⟨5027337199326034892863099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6703116265768046523817465 5027337199326034892863099)
          ·
            refine ⟨7541005798989052339294649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027337199326034892863099 7541005798989052339294649)
            ·
              refine ⟨5655754349241789254470987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7541005798989052339294649 5655754349241789254470987)
              ·
                refine ⟨8483631523862683881706481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655754349241789254470987 8483631523862683881706481)
                ·
                  refine ⟨6362723642897012911279861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8483631523862683881706481 6362723642897012911279861)
                  ·
                    refine ⟨596505341521594960432487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6362723642897012911279861 596505341521594960432487)
                    ·
                      rfl

theorem cell23_3485070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3485070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485070 prefixEnd_3485070 := by exact prefixLift 3485070
  have htrace : WordTrace (prefixWord ++ tailWord_3485070) baseStart_3485070 baseEnd_3485070 := by
    simpa [prefixWord, tailWord_3485070, baseEnd_3485070] using wordTrace_append hprefix tailTrace_3485070
  have hstable : (prefixWord ++ tailWord_3485070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485070).length < 2 ^ (prefixWord ++ tailWord_3485070).sum := by decide
  have hdescent : baseEnd_3485070 < baseStart_3485070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485123 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 3]
def baseStart_3485123 : Nat := 118140960795 + 3485123 * 2 ^ 59
def prefixEnd_3485123 : Nat := 4983230072969 + 3 ^ 40 * 3485123 * 2
def baseEnd_3485123 : Nat := 1789543239039473173934717

theorem tailTrace_3485123 : CollatzResearch.WordTrace tailWord_3485123 prefixEnd_3485123 1789543239039473173934717 := by
  unfold tailWord_3485123
  simp only [CollatzResearch.WordTrace]
  refine ⟨127112878553002057466292023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84741919035334704977528015 127112878553002057466292023)
  ·
    refine ⟨190669317829503086199438035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127112878553002057466292023 190669317829503086199438035)
    ·
      refine ⟨286003976744254629299157053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190669317829503086199438035 286003976744254629299157053)
      ·
        refine ⟨107251491279095485987183895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286003976744254629299157053 107251491279095485987183895)
        ·
          refine ⟨160877236918643228980775843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107251491279095485987183895 160877236918643228980775843)
          ·
            refine ⟨241315855377964843471163765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160877236918643228980775843 241315855377964843471163765)
            ·
              refine ⟨22623361441684204075421603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241315855377964843471163765 22623361441684204075421603)
              ·
                refine ⟨33935042162526306113132405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22623361441684204075421603 33935042162526306113132405)
                ·
                  refine ⟨3181410202736841198106163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33935042162526306113132405 3181410202736841198106163)
                  ·
                    refine ⟨4772115304105261797159245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3181410202736841198106163 4772115304105261797159245)
                    ·
                      refine ⟨1789543239039473173934717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4772115304105261797159245 1789543239039473173934717)
                      ·
                        rfl

theorem cell23_3485123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_3485123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485123 prefixEnd_3485123 := by exact prefixLift 3485123
  have htrace : WordTrace (prefixWord ++ tailWord_3485123) baseStart_3485123 baseEnd_3485123 := by
    simpa [prefixWord, tailWord_3485123, baseEnd_3485123] using wordTrace_append hprefix tailTrace_3485123
  have hstable : (prefixWord ++ tailWord_3485123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485123).length < 2 ^ (prefixWord ++ tailWord_3485123).sum := by decide
  have hdescent : baseEnd_3485123 < baseStart_3485123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485156 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_3485156 : Nat := 118140960795 + 3485156 * 2 ^ 59
def prefixEnd_3485156 : Nat := 4983230072969 + 3 ^ 40 * 3485156 * 2
def baseEnd_3485156 : Nat := 596520061300357181607355

theorem tailTrace_3485156 : CollatzResearch.WordTrace tailWord_3485156 prefixEnd_3485156 596520061300357181607355 := by
  unfold tailWord_3485156
  simp only [CollatzResearch.WordTrace]
  refine ⟨63557041080941252051121661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84742721441255002734828881 63557041080941252051121661)
  ·
    refine ⟨23833890405352969519170623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63557041080941252051121661 23833890405352969519170623)
    ·
      refine ⟨35750835608029454278755935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23833890405352969519170623 35750835608029454278755935)
      ·
        refine ⟨53626253412044181418133903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35750835608029454278755935 53626253412044181418133903)
        ·
          refine ⟨80439380118066272127200855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53626253412044181418133903 80439380118066272127200855)
          ·
            refine ⟨120659070177099408190801283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80439380118066272127200855 120659070177099408190801283)
            ·
              refine ⟨180988605265649112286201925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120659070177099408190801283 180988605265649112286201925)
              ·
                refine ⟨33935363487309208553662861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180988605265649112286201925 33935363487309208553662861)
                ·
                  refine ⟨12725761307740953207623573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33935363487309208553662861 12725761307740953207623573)
                  ·
                    refine ⟨596520061300357181607355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12725761307740953207623573 596520061300357181607355)
                    ·
                      rfl

theorem cell23_3485156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_3485156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485156 prefixEnd_3485156 := by exact prefixLift 3485156
  have htrace : WordTrace (prefixWord ++ tailWord_3485156) baseStart_3485156 baseEnd_3485156 := by
    simpa [prefixWord, tailWord_3485156, baseEnd_3485156] using wordTrace_append hprefix tailTrace_3485156
  have hstable : (prefixWord ++ tailWord_3485156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485156).length < 2 ^ (prefixWord ++ tailWord_3485156).sum := by decide
  have hdescent : baseEnd_3485156 < baseStart_3485156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485157 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3485157 : Nat := 118140960795 + 3485157 * 2 ^ 59
def prefixEnd_3485157 : Nat := 4983230072969 + 3 ^ 40 * 3485157 * 2
def baseEnd_3485157 : Nat := 1789560697381726040909561

theorem tailTrace_3485157 : CollatzResearch.WordTrace tailWord_3485157 prefixEnd_3485157 1789560697381726040909561 := by
  unfold tailWord_3485157
  simp only [CollatzResearch.WordTrace]
  refine ⟨127114118634878881273029725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84742745756585920848686483 127114118634878881273029725)
  ·
    refine ⟨47667794488079580477386147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127114118634878881273029725 47667794488079580477386147)
    ·
      refine ⟨71501691732119370716079221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47667794488079580477386147 71501691732119370716079221)
      ·
        refine ⟨6703283599886191004632427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71501691732119370716079221 6703283599886191004632427)
        ·
          refine ⟨10054925399829286506948641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703283599886191004632427 10054925399829286506948641)
          ·
            refine ⟨7541194049871964880211481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10054925399829286506948641 7541194049871964880211481)
            ·
              refine ⟨5655895537403973660158611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7541194049871964880211481 5655895537403973660158611)
              ·
                refine ⟨8483843306105960490237917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655895537403973660158611 8483843306105960490237917)
                ·
                  refine ⟨3181441239789735183839219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8483843306105960490237917 3181441239789735183839219)
                  ·
                    refine ⟨4772161859684602775758829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3181441239789735183839219 4772161859684602775758829)
                    ·
                      refine ⟨1789560697381726040909561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4772161859684602775758829 1789560697381726040909561)
                      ·
                        rfl

theorem cell23_3485157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3485157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485157 prefixEnd_3485157 := by exact prefixLift 3485157
  have htrace : WordTrace (prefixWord ++ tailWord_3485157) baseStart_3485157 baseEnd_3485157 := by
    simpa [prefixWord, tailWord_3485157, baseEnd_3485157] using wordTrace_append hprefix tailTrace_3485157
  have hstable : (prefixWord ++ tailWord_3485157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485157).length < 2 ^ (prefixWord ++ tailWord_3485157).sum := by decide
  have hdescent : baseEnd_3485157 < baseStart_3485157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485283 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3485283 : Nat := 118140960795 + 3485283 * 2 ^ 59
def prefixEnd_3485283 : Nat := 4983230072969 + 3 ^ 40 * 3485283 * 2
def baseEnd_3485283 : Nat := 1789625395944192547933981

theorem tailTrace_3485283 : CollatzResearch.WordTrace tailWord_3485283 prefixEnd_3485283 1789625395944192547933981 := by
  unfold tailWord_3485283
  simp only [CollatzResearch.WordTrace]
  refine ⟨127118714232422404792116503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84745809488281603194744335 127118714232422404792116503)
  ·
    refine ⟨190678071348633607188174755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127118714232422404792116503 190678071348633607188174755)
    ·
      refine ⟨286017107022950410782262133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190678071348633607188174755 286017107022950410782262133)
      ·
        refine ⟨26814103783401601010837075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 286017107022950410782262133 26814103783401601010837075)
        ·
          refine ⟨40221155675102401516255613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26814103783401601010837075 40221155675102401516255613)
          ·
            refine ⟨15082933378163400568595855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40221155675102401516255613 15082933378163400568595855)
            ·
              refine ⟨22624400067245100852893783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15082933378163400568595855 22624400067245100852893783)
              ·
                refine ⟨33936600100867651279340675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22624400067245100852893783 33936600100867651279340675)
                ·
                  refine ⟨50904900151301476919011013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33936600100867651279340675 50904900151301476919011013)
                  ·
                    refine ⟨9544668778369026922314565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50904900151301476919011013 9544668778369026922314565)
                    ·
                      refine ⟨1789625395944192547933981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9544668778369026922314565 1789625395944192547933981)
                      ·
                        rfl

theorem cell23_3485283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3485283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485283 prefixEnd_3485283 := by exact prefixLift 3485283
  have htrace : WordTrace (prefixWord ++ tailWord_3485283) baseStart_3485283 baseEnd_3485283 := by
    simpa [prefixWord, tailWord_3485283, baseEnd_3485283] using wordTrace_append hprefix tailTrace_3485283
  have hstable : (prefixWord ++ tailWord_3485283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485283).length < 2 ^ (prefixWord ++ tailWord_3485283).sum := by decide
  have hdescent : baseEnd_3485283 < baseStart_3485283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485303 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_3485303 : Nat := 118140960795 + 3485303 * 2 ^ 59
def prefixEnd_3485303 : Nat := 4983230072969 + 3 ^ 40 * 3485303 * 2
def baseEnd_3485303 : Nat := 1789635665557282469683889

theorem tailTrace_3485303 : CollatzResearch.WordTrace tailWord_3485303 prefixEnd_3485303 1789635665557282469683889 := by
  unfold tailWord_3485303
  simp only [CollatzResearch.WordTrace]
  refine ⟨127119443692349948207844563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84746295794899965471896375 127119443692349948207844563)
  ·
    refine ⟨190679165538524922311766845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127119443692349948207844563 190679165538524922311766845)
    ·
      refine ⟨71504687076946845866912567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190679165538524922311766845 71504687076946845866912567)
      ·
        refine ⟨107257030615420268800368851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71504687076946845866912567 107257030615420268800368851)
        ·
          refine ⟨160885545923130403200553277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107257030615420268800368851 160885545923130403200553277)
          ·
            refine ⟨60332079721173901200207479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160885545923130403200553277 60332079721173901200207479)
            ·
              refine ⟨90498119581760851800311219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60332079721173901200207479 90498119581760851800311219)
              ·
                refine ⟨135747179372641277700466829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90498119581760851800311219 135747179372641277700466829)
                ·
                  refine ⟨50905192264740479137675061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135747179372641277700466829 50905192264740479137675061)
                  ·
                    refine ⟨4772361774819419919157037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50905192264740479137675061 4772361774819419919157037)
                    ·
                      refine ⟨1789635665557282469683889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4772361774819419919157037 1789635665557282469683889)
                      ·
                        rfl

theorem cell23_3485303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_3485303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485303 prefixEnd_3485303 := by exact prefixLift 3485303
  have htrace : WordTrace (prefixWord ++ tailWord_3485303) baseStart_3485303 baseEnd_3485303 := by
    simpa [prefixWord, tailWord_3485303, baseEnd_3485303] using wordTrace_append hprefix tailTrace_3485303
  have hstable : (prefixWord ++ tailWord_3485303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485303).length < 2 ^ (prefixWord ++ tailWord_3485303).sum := by decide
  have hdescent : baseEnd_3485303 < baseStart_3485303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485323 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 4, 5]
def baseStart_3485323 : Nat := 118140960795 + 3485323 * 2 ^ 59
def prefixEnd_3485323 : Nat := 4983230072969 + 3 ^ 40 * 3485323 * 2
def baseEnd_3485323 : Nat := 596548645056790797144599

theorem tailTrace_3485323 : CollatzResearch.WordTrace tailWord_3485323 prefixEnd_3485323 596548645056790797144599 := by
  unfold tailWord_3485323
  simp only [CollatzResearch.WordTrace]
  refine ⟨127120173152277491623572623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84746782101518327749048415 127120173152277491623572623)
  ·
    refine ⟨190680259728416237435358935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127120173152277491623572623 190680259728416237435358935)
    ·
      refine ⟨286020389592624356153038403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190680259728416237435358935 286020389592624356153038403)
      ·
        refine ⟨429030584388936534229557605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286020389592624356153038403 429030584388936534229557605)
        ·
          refine ⟨80443234572925600168042051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429030584388936534229557605 80443234572925600168042051)
          ·
            refine ⟨120664851859388400252063077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80443234572925600168042051 120664851859388400252063077)
            ·
              refine ⟨22624659723635325047261827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120664851859388400252063077 22624659723635325047261827)
              ·
                refine ⟨33936989585452987570892741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22624659723635325047261827 33936989585452987570892741)
                ·
                  refine ⟨6363185547272435169542389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33936989585452987570892741 6363185547272435169542389)
                  ·
                    refine ⟨596548645056790797144599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6363185547272435169542389 596548645056790797144599)
                    ·
                      rfl

theorem cell23_3485323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 5].length) (baseStart_3485323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485323 prefixEnd_3485323 := by exact prefixLift 3485323
  have htrace : WordTrace (prefixWord ++ tailWord_3485323) baseStart_3485323 baseEnd_3485323 := by
    simpa [prefixWord, tailWord_3485323, baseEnd_3485323] using wordTrace_append hprefix tailTrace_3485323
  have hstable : (prefixWord ++ tailWord_3485323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485323).length < 2 ^ (prefixWord ++ tailWord_3485323).sum := by decide
  have hdescent : baseEnd_3485323 < baseStart_3485323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485333 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_3485333 : Nat := 118140960795 + 3485333 * 2 ^ 59
def prefixEnd_3485333 : Nat := 4983230072969 + 3 ^ 40 * 3485333 * 2
def baseEnd_3485333 : Nat := 1789651069976917352308751

theorem tailTrace_3485333 : CollatzResearch.WordTrace tailWord_3485333 prefixEnd_3485333 1789651069976917352308751 := by
  unfold tailWord_3485333
  simp only [CollatzResearch.WordTrace]
  refine ⟨127120537882241263331436653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84747025254827508887624435 127120537882241263331436653)
  ·
    refine ⟨47670201705840473749288745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127120537882241263331436653 47670201705840473749288745)
    ·
      refine ⟨35752651279380355311966559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47670201705840473749288745 35752651279380355311966559)
      ·
        refine ⟨53628976919070532967949839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35752651279380355311966559 53628976919070532967949839)
        ·
          refine ⟨80443465378605799451924759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53628976919070532967949839 80443465378605799451924759)
          ·
            refine ⟨120665198067908699177887139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80443465378605799451924759 120665198067908699177887139)
            ·
              refine ⟨180997797101863048766830709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120665198067908699177887139 180997797101863048766830709)
              ·
                refine ⟨16968543478299660821890379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180997797101863048766830709 16968543478299660821890379)
                ·
                  refine ⟨25452815217449491232835569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16968543478299660821890379 25452815217449491232835569)
                  ·
                    refine ⟨19089611413087118424626677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25452815217449491232835569 19089611413087118424626677)
                    ·
                      refine ⟨1789651069976917352308751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19089611413087118424626677 1789651069976917352308751)
                      ·
                        rfl

theorem cell23_3485333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_3485333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485333 prefixEnd_3485333 := by exact prefixLift 3485333
  have htrace : WordTrace (prefixWord ++ tailWord_3485333) baseStart_3485333 baseEnd_3485333 := by
    simpa [prefixWord, tailWord_3485333, baseEnd_3485333] using wordTrace_append hprefix tailTrace_3485333
  have hstable : (prefixWord ++ tailWord_3485333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485333).length < 2 ^ (prefixWord ++ tailWord_3485333).sum := by decide
  have hdescent : baseEnd_3485333 < baseStart_3485333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485360 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 6, 2]
def baseStart_3485360 : Nat := 118140960795 + 3485360 * 2 ^ 59
def prefixEnd_3485360 : Nat := 4983230072969 + 3 ^ 40 * 3485360 * 2
def baseEnd_3485360 : Nat := 1789664933954588746671127

theorem tailTrace_3485360 : CollatzResearch.WordTrace tailWord_3485360 prefixEnd_3485360 1789664933954588746671127 := by
  unfold tailWord_3485360
  simp only [CollatzResearch.WordTrace]
  refine ⟨63560761326571723471334767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84747681768762297961779689 63560761326571723471334767)
  ·
    refine ⟨95341141989857585207002151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63560761326571723471334767 95341141989857585207002151)
    ·
      refine ⟨143011712984786377810503227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95341141989857585207002151 143011712984786377810503227)
      ·
        refine ⟨214517569477179566715754841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143011712984786377810503227 214517569477179566715754841)
        ·
          refine ⟨160888177107884675036816131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214517569477179566715754841 160888177107884675036816131)
          ·
            refine ⟨241332265661827012555224197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160888177107884675036816131 241332265661827012555224197)
            ·
              refine ⟨45249799811592564854104537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241332265661827012555224197 45249799811592564854104537)
              ·
                refine ⟨33937349858694423640578403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45249799811592564854104537 33937349858694423640578403)
                ·
                  refine ⟨50906024788041635460867605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33937349858694423640578403 50906024788041635460867605)
                  ·
                    refine ⟨2386219911939451662228169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50906024788041635460867605 2386219911939451662228169)
                    ·
                      refine ⟨1789664933954588746671127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386219911939451662228169 1789664933954588746671127)
                      ·
                        rfl

theorem cell23_3485360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 6, 2].length) (baseStart_3485360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485360 prefixEnd_3485360 := by exact prefixLift 3485360
  have htrace : WordTrace (prefixWord ++ tailWord_3485360) baseStart_3485360 baseEnd_3485360 := by
    simpa [prefixWord, tailWord_3485360, baseEnd_3485360] using wordTrace_append hprefix tailTrace_3485360
  have hstable : (prefixWord ++ tailWord_3485360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485360).length < 2 ^ (prefixWord ++ tailWord_3485360).sum := by decide
  have hdescent : baseEnd_3485360 < baseStart_3485360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485378 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3485378 : Nat := 118140960795 + 3485378 * 2 ^ 59
def prefixEnd_3485378 : Nat := 4983230072969 + 3 ^ 40 * 3485378 * 2
def baseEnd_3485378 : Nat := 198852686289596630694005

theorem tailTrace_3485378 : CollatzResearch.WordTrace tailWord_3485378 prefixEnd_3485378 198852686289596630694005 := by
  unfold tailWord_3485378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31780544791769559004206197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84748119444718824011216525 31780544791769559004206197)
  ·
    refine ⟨2979426074228396156644331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31780544791769559004206197 2979426074228396156644331)
    ·
      refine ⟨4469139111342594234966497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979426074228396156644331 4469139111342594234966497)
      ·
        refine ⟨3351854333506945676224873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4469139111342594234966497 3351854333506945676224873)
        ·
          refine ⟨2513890750130209257168655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3351854333506945676224873 2513890750130209257168655)
          ·
            refine ⟨3770836125195313885752983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513890750130209257168655 3770836125195313885752983)
            ·
              refine ⟨5656254187792970828629475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770836125195313885752983 5656254187792970828629475)
              ·
                refine ⟨8484381281689456242944213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656254187792970828629475 8484381281689456242944213)
                ·
                  refine ⟨198852686289596630694005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8484381281689456242944213 198852686289596630694005)
                  ·
                    rfl

theorem cell23_3485378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3485378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485378 prefixEnd_3485378 := by exact prefixLift 3485378
  have htrace : WordTrace (prefixWord ++ tailWord_3485378) baseStart_3485378 baseEnd_3485378 := by
    simpa [prefixWord, tailWord_3485378, baseEnd_3485378] using wordTrace_append hprefix tailTrace_3485378
  have hstable : (prefixWord ++ tailWord_3485378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485378).length < 2 ^ (prefixWord ++ tailWord_3485378).sum := by decide
  have hdescent : baseEnd_3485378 < baseStart_3485378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485383 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 8]
def baseStart_3485383 : Nat := 118140960795 + 3485383 * 2 ^ 59
def prefixEnd_3485383 : Nat := 4983230072969 + 3 ^ 40 * 3485383 * 2
def baseEnd_3485383 : Nat := 198852971556626906298169

theorem tailTrace_3485383 : CollatzResearch.WordTrace tailWord_3485383 prefixEnd_3485383 198852971556626906298169 := by
  unfold tailWord_3485383
  simp only [CollatzResearch.WordTrace]
  refine ⟨127122361532060121870756803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84748241021373414580504535 127122361532060121870756803)
  ·
    refine ⟨190683542298090182806135205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127122361532060121870756803 190683542298090182806135205)
    ·
      refine ⟨35753164180891909276150351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190683542298090182806135205 35753164180891909276150351)
      ·
        refine ⟨53629746271337863914225527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35753164180891909276150351 53629746271337863914225527)
        ·
          refine ⟨80444619407006795871338291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53629746271337863914225527 80444619407006795871338291)
          ·
            refine ⟨120666929110510193807007437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80444619407006795871338291 120666929110510193807007437)
            ·
              refine ⟨45250098416441322677627789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120666929110510193807007437 45250098416441322677627789)
              ·
                refine ⟨16968786906165496004110421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45250098416441322677627789 16968786906165496004110421)
                ·
                  refine ⟨198852971556626906298169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16968786906165496004110421 198852971556626906298169)
                  ·
                    rfl

theorem cell23_3485383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 8].length) (baseStart_3485383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485383 prefixEnd_3485383 := by exact prefixLift 3485383
  have htrace : WordTrace (prefixWord ++ tailWord_3485383) baseStart_3485383 baseEnd_3485383 := by
    simpa [prefixWord, tailWord_3485383, baseEnd_3485383] using wordTrace_append hprefix tailTrace_3485383
  have hstable : (prefixWord ++ tailWord_3485383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485383).length < 2 ^ (prefixWord ++ tailWord_3485383).sum := by decide
  have hdescent : baseEnd_3485383 < baseStart_3485383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485387 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 1, 4]
def baseStart_3485387 : Nat := 118140960795 + 3485387 * 2 ^ 59
def prefixEnd_3485387 : Nat := 4983230072969 + 3 ^ 40 * 3485387 * 2
def baseEnd_3485387 : Nat := 596559599310753380344501

theorem tailTrace_3485387 : CollatzResearch.WordTrace tailWord_3485387 prefixEnd_3485387 596559599310753380344501 := by
  unfold tailWord_3485387
  simp only [CollatzResearch.WordTrace]
  refine ⟨127122507424045630553902415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84748338282697087035934943 127122507424045630553902415)
  ·
    refine ⟨190683761136068445830853623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127122507424045630553902415 190683761136068445830853623)
    ·
      refine ⟨286025641704102668746280435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190683761136068445830853623 286025641704102668746280435)
      ·
        refine ⟨429038462556154003119420653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286025641704102668746280435 429038462556154003119420653)
        ·
          refine ⟨160889423458557751169782745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429038462556154003119420653 160889423458557751169782745)
          ·
            refine ⟨120667067593918313377337059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160889423458557751169782745 120667067593918313377337059)
            ·
              refine ⟨181000601390877470066005589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120667067593918313377337059 181000601390877470066005589)
              ·
                refine ⟨2121100797549345352336003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 181000601390877470066005589 2121100797549345352336003)
                ·
                  refine ⟨3181651196324018028504005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121100797549345352336003 3181651196324018028504005)
                  ·
                    refine ⟨596559599310753380344501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3181651196324018028504005 596559599310753380344501)
                    ·
                      rfl

theorem cell23_3485387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 4].length) (baseStart_3485387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485387 prefixEnd_3485387 := by exact prefixLift 3485387
  have htrace : WordTrace (prefixWord ++ tailWord_3485387) baseStart_3485387 baseEnd_3485387 := by
    simpa [prefixWord, tailWord_3485387, baseEnd_3485387] using wordTrace_append hprefix tailTrace_3485387
  have hstable : (prefixWord ++ tailWord_3485387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485387).length < 2 ^ (prefixWord ++ tailWord_3485387).sum := by decide
  have hdescent : baseEnd_3485387 < baseStart_3485387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485400 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 6]
def baseStart_3485400 : Nat := 118140960795 + 3485400 * 2 ^ 59
def prefixEnd_3485400 : Nat := 4983230072969 + 3 ^ 40 * 3485400 * 2
def baseEnd_3485400 : Nat := 198853941464529843352327

theorem tailTrace_3485400 : CollatzResearch.WordTrace tailWord_3485400 prefixEnd_3485400 198853941464529843352327 := by
  unfold tailWord_3485400
  simp only [CollatzResearch.WordTrace]
  refine ⟨63561490786499266887062827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84748654381999022516083769 63561490786499266887062827)
  ·
    refine ⟨95342236179748900330594241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63561490786499266887062827 95342236179748900330594241)
    ·
      refine ⟨71506677134811675247945681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95342236179748900330594241 71506677134811675247945681)
      ·
        refine ⟨53630007851108756435959261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71506677134811675247945681 53630007851108756435959261)
        ·
          refine ⟨20111252944165783663484723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53630007851108756435959261 20111252944165783663484723)
          ·
            refine ⟨30166879416248675495227085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20111252944165783663484723 30166879416248675495227085)
            ·
              refine ⟨11312579781093253310710157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30166879416248675495227085 11312579781093253310710157)
              ·
                refine ⟨4242217417909969991516309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11312579781093253310710157 4242217417909969991516309)
                ·
                  refine ⟨198853941464529843352327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4242217417909969991516309 198853941464529843352327)
                  ·
                    rfl

theorem cell23_3485400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 6].length) (baseStart_3485400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485400 prefixEnd_3485400 := by exact prefixLift 3485400
  have htrace : WordTrace (prefixWord ++ tailWord_3485400) baseStart_3485400 baseEnd_3485400 := by
    simpa [prefixWord, tailWord_3485400, baseEnd_3485400] using wordTrace_append hprefix tailTrace_3485400
  have hstable : (prefixWord ++ tailWord_3485400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485400).length < 2 ^ (prefixWord ++ tailWord_3485400).sum := by decide
  have hdescent : baseEnd_3485400 < baseStart_3485400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485437 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_3485437 : Nat := 118140960795 + 3485437 * 2 ^ 59
def prefixEnd_3485437 : Nat := 4983230072969 + 3 ^ 40 * 3485437 * 2
def baseEnd_3485437 : Nat := 1789704471964984945408273

theorem tailTrace_3485437 : CollatzResearch.WordTrace tailWord_3485437 prefixEnd_3485437 1789704471964984945408273 := by
  unfold tailWord_3485437
  simp only [CollatzResearch.WordTrace]
  refine ⟨127124331073864489093222565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84749554049242992728815043 127124331073864489093222565)
  ·
    refine ⟨23835812076349591704979231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127124331073864489093222565 23835812076349591704979231)
    ·
      refine ⟨35753718114524387557468847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23835812076349591704979231 35753718114524387557468847)
      ·
        refine ⟨53630577171786581336203271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35753718114524387557468847 53630577171786581336203271)
        ·
          refine ⟨80445865757679872004304907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53630577171786581336203271 80445865757679872004304907)
          ·
            refine ⟨120668798636519808006457361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80445865757679872004304907 120668798636519808006457361)
            ·
              refine ⟨90501598977389856004843021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120668798636519808006457361 90501598977389856004843021)
              ·
                refine ⟨33938099616521196001816133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90501598977389856004843021 33938099616521196001816133)
                ·
                  refine ⟨6363393678097724250340525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33938099616521196001816133 6363393678097724250340525)
                  ·
                    refine ⟨2386272629286646593877697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6363393678097724250340525 2386272629286646593877697)
                    ·
                      refine ⟨1789704471964984945408273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386272629286646593877697 1789704471964984945408273)
                      ·
                        rfl

theorem cell23_3485437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_3485437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485437 prefixEnd_3485437 := by exact prefixLift 3485437
  have htrace : WordTrace (prefixWord ++ tailWord_3485437) baseStart_3485437 baseEnd_3485437 := by
    simpa [prefixWord, tailWord_3485437, baseEnd_3485437] using wordTrace_append hprefix tailTrace_3485437
  have hstable : (prefixWord ++ tailWord_3485437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485437).length < 2 ^ (prefixWord ++ tailWord_3485437).sum := by decide
  have hdescent : baseEnd_3485437 < baseStart_3485437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485484 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 4]
def baseStart_3485484 : Nat := 118140960795 + 3485484 * 2 ^ 59
def prefixEnd_3485484 : Nat := 4983230072969 + 3 ^ 40 * 3485484 * 2
def baseEnd_3485484 : Nat := 1789728605555746261520557

theorem tailTrace_3485484 : CollatzResearch.WordTrace tailWord_3485484 prefixEnd_3485484 1789728605555746261520557 := by
  unfold tailWord_3485484
  simp only [CollatzResearch.WordTrace]
  refine ⟨63563022652347108060091753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84750696869796144080122337 63563022652347108060091753)
  ·
    refine ⟨47672266989260331045068815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63563022652347108060091753 47672266989260331045068815)
    ·
      refine ⟨71508400483890496567603223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47672266989260331045068815 71508400483890496567603223)
      ·
        refine ⟨107262600725835744851404835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71508400483890496567603223 107262600725835744851404835)
        ·
          refine ⟨160893901088753617277107253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107262600725835744851404835 160893901088753617277107253)
          ·
            refine ⟨15083803227070651619728805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160893901088753617277107253 15083803227070651619728805)
            ·
              refine ⟨2828213105075747178699151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15083803227070651619728805 2828213105075747178699151)
              ·
                refine ⟨4242319657613620768048727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828213105075747178699151 4242319657613620768048727)
                ·
                  refine ⟨6363479486420431152073091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242319657613620768048727 6363479486420431152073091)
                  ·
                    refine ⟨9545219229630646728109637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6363479486420431152073091 9545219229630646728109637)
                    ·
                      refine ⟨1789728605555746261520557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9545219229630646728109637 1789728605555746261520557)
                      ·
                        rfl

theorem cell23_3485484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_3485484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485484 prefixEnd_3485484 := by exact prefixLift 3485484
  have htrace : WordTrace (prefixWord ++ tailWord_3485484) baseStart_3485484 baseEnd_3485484 := by
    simpa [prefixWord, tailWord_3485484, baseEnd_3485484] using wordTrace_append hprefix tailTrace_3485484
  have hstable : (prefixWord ++ tailWord_3485484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485484).length < 2 ^ (prefixWord ++ tailWord_3485484).sum := by decide
  have hdescent : baseEnd_3485484 < baseStart_3485484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485487 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 3]
def baseStart_3485487 : Nat := 118140960795 + 3485487 * 2 ^ 59
def prefixEnd_3485487 : Nat := 4983230072969 + 3 ^ 40 * 3485487 * 2
def baseEnd_3485487 : Nat := 1789730145997709749783043

theorem tailTrace_3485487 : CollatzResearch.WordTrace tailWord_3485487 prefixEnd_3485487 1789730145997709749783043 := by
  unfold tailWord_3485487
  simp only [CollatzResearch.WordTrace]
  refine ⟨127126154723683347632542715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84750769815788898421695143 127126154723683347632542715)
  ·
    refine ⟨190689232085525021448814073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127126154723683347632542715 190689232085525021448814073)
    ·
      refine ⟨143016924064143766086610555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190689232085525021448814073 143016924064143766086610555)
      ·
        refine ⟨214525386096215649129915833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143016924064143766086610555 214525386096215649129915833)
        ·
          refine ⟨160894039572161736847436875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214525386096215649129915833 160894039572161736847436875)
          ·
            refine ⟨241341059358242605271155313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160894039572161736847436875 241341059358242605271155313)
            ·
              refine ⟨181005794518681953953366485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241341059358242605271155313 181005794518681953953366485)
              ·
                refine ⟨4242323309031608295782027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181005794518681953953366485 4242323309031608295782027)
                ·
                  refine ⟨6363484963547412443673041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242323309031608295782027 6363484963547412443673041)
                  ·
                    refine ⟨4772613722660559332754781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6363484963547412443673041 4772613722660559332754781)
                    ·
                      refine ⟨1789730145997709749783043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4772613722660559332754781 1789730145997709749783043)
                      ·
                        rfl

theorem cell23_3485487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_3485487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485487 prefixEnd_3485487 := by exact prefixLift 3485487
  have htrace : WordTrace (prefixWord ++ tailWord_3485487) baseStart_3485487 baseEnd_3485487 := by
    simpa [prefixWord, tailWord_3485487, baseEnd_3485487] using wordTrace_append hprefix tailTrace_3485487
  have hstable : (prefixWord ++ tailWord_3485487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485487).length < 2 ^ (prefixWord ++ tailWord_3485487).sum := by decide
  have hdescent : baseEnd_3485487 < baseStart_3485487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485490 : List Nat := [3, 2, 1, 1, 3, 3, 10]
def baseStart_3485490 : Nat := 118140960795 + 3485490 * 2 ^ 59
def prefixEnd_3485490 : Nat := 4983230072969 + 3 ^ 40 * 3485490 * 2
def baseEnd_3485490 : Nat := 22095452919008311580809

theorem tailTrace_3485490 : CollatzResearch.WordTrace tailWord_3485490 prefixEnd_3485490 22095452919008311580809 := by
  unfold tailWord_3485490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31781566035668119786225481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84750842761781652763267949 31781566035668119786225481)
  ·
    refine ⟨23836174526751089839669111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31781566035668119786225481 23836174526751089839669111)
    ·
      refine ⟨35754261790126634759503667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23836174526751089839669111 35754261790126634759503667)
      ·
        refine ⟨53631392685189952139255501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35754261790126634759503667 53631392685189952139255501)
        ·
          refine ⟨20111772256946232052220813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53631392685189952139255501 20111772256946232052220813)
          ·
            refine ⟨7541914596354837019582805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20111772256946232052220813 7541914596354837019582805)
            ·
              refine ⟨22095452919008311580809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7541914596354837019582805 22095452919008311580809)
              ·
                rfl

theorem cell23_3485490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 10].length) (baseStart_3485490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485490 prefixEnd_3485490 := by exact prefixLift 3485490
  have htrace : WordTrace (prefixWord ++ tailWord_3485490) baseStart_3485490 baseEnd_3485490 := by
    simpa [prefixWord, tailWord_3485490, baseEnd_3485490] using wordTrace_append hprefix tailTrace_3485490
  have hstable : (prefixWord ++ tailWord_3485490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485490).length < 2 ^ (prefixWord ++ tailWord_3485490).sum := by decide
  have hdescent : baseEnd_3485490 < baseStart_3485490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485501 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3485501 : Nat := 118140960795 + 3485501 * 2 ^ 59
def prefixEnd_3485501 : Nat := 4983230072969 + 3 ^ 40 * 3485501 * 2
def baseEnd_3485501 : Nat := 1789737334726872695007979

theorem tailTrace_3485501 : CollatzResearch.WordTrace tailWord_3485501 prefixEnd_3485501 1789737334726872695007979 := by
  unfold tailWord_3485501
  simp only [CollatzResearch.WordTrace]
  refine ⟨127126665345632628023552357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84751110230421752015701571 127126665345632628023552357)
  ·
    refine ⟨23836249752306117754416067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127126665345632628023552357 23836249752306117754416067)
    ·
      refine ⟨35754374628459176631624101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23836249752306117754416067 35754374628459176631624101)
      ·
        refine ⟨6703945242836095618429519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35754374628459176631624101 6703945242836095618429519)
        ·
          refine ⟨10055917864254143427644279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703945242836095618429519 10055917864254143427644279)
          ·
            refine ⟨15083876796381215141466419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10055917864254143427644279 15083876796381215141466419)
            ·
              refine ⟨22625815194571822712199629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15083876796381215141466419 22625815194571822712199629)
              ·
                refine ⟨8484680697964433517074861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22625815194571822712199629 8484680697964433517074861)
                ·
                  refine ⟨3181755261736662568903073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8484680697964433517074861 3181755261736662568903073)
                  ·
                    refine ⟨2386316446302496926677305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3181755261736662568903073 2386316446302496926677305)
                    ·
                      refine ⟨1789737334726872695007979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386316446302496926677305 1789737334726872695007979)
                      ·
                        rfl

theorem cell23_3485501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3485501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485501 prefixEnd_3485501 := by exact prefixLift 3485501
  have htrace : WordTrace (prefixWord ++ tailWord_3485501) baseStart_3485501 baseEnd_3485501 := by
    simpa [prefixWord, tailWord_3485501, baseEnd_3485501] using wordTrace_append hprefix tailTrace_3485501
  have hstable : (prefixWord ++ tailWord_3485501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485501).length < 2 ^ (prefixWord ++ tailWord_3485501).sum := by decide
  have hdescent : baseEnd_3485501 < baseStart_3485501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485524 : List Nat := [2, 4, 1, 1, 3, 3, 2, 7]
def baseStart_3485524 : Nat := 118140960795 + 3485524 * 2 ^ 59
def prefixEnd_3485524 : Nat := 4983230072969 + 3 ^ 40 * 3485524 * 2
def baseEnd_3485524 : Nat := 66287005362293559445199

theorem tailTrace_3485524 : CollatzResearch.WordTrace tailWord_3485524 prefixEnd_3485524 66287005362293559445199 := by
  unfold tailWord_3485524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63563752112274651475819813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84751669483032868634426417 63563752112274651475819813)
  ·
    refine ⟨11918203521051497151716215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63563752112274651475819813 11918203521051497151716215)
    ·
      refine ⟨17877305281577245727574323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11918203521051497151716215 17877305281577245727574323)
      ·
        refine ⟨26815957922365868591361485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17877305281577245727574323 26815957922365868591361485)
        ·
          refine ⟨10055984220887200721760557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26815957922365868591361485 10055984220887200721760557)
          ·
            refine ⟨3770994082832700270660209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10055984220887200721760557 3770994082832700270660209)
            ·
              refine ⟨2828245562124525202995157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770994082832700270660209 2828245562124525202995157)
              ·
                refine ⟨66287005362293559445199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2828245562124525202995157 66287005362293559445199)
                ·
                  rfl

theorem cell23_3485524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 7].length) (baseStart_3485524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485524 prefixEnd_3485524 := by exact prefixLift 3485524
  have htrace : WordTrace (prefixWord ++ tailWord_3485524) baseStart_3485524 baseEnd_3485524 := by
    simpa [prefixWord, tailWord_3485524, baseEnd_3485524] using wordTrace_append hprefix tailTrace_3485524
  have hstable : (prefixWord ++ tailWord_3485524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485524).length < 2 ^ (prefixWord ++ tailWord_3485524).sum := by decide
  have hdescent : baseEnd_3485524 < baseStart_3485524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485530 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3485530 : Nat := 118140960795 + 3485530 * 2 ^ 59
def prefixEnd_3485530 : Nat := 4983230072969 + 3 ^ 40 * 3485530 * 2
def baseEnd_3485530 : Nat := 1789752225665853081545345

theorem tailTrace_3485530 : CollatzResearch.WordTrace tailWord_3485530 prefixEnd_3485530 1789752225665853081545345 := by
  unfold tailWord_3485530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31781930765631891494089511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84751815375018377317572029 31781930765631891494089511)
  ·
    refine ⟨47672896148447837241134267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31781930765631891494089511 47672896148447837241134267)
    ·
      refine ⟨71509344222671755861701401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47672896148447837241134267 71509344222671755861701401)
      ·
        refine ⟨53632008167003816896276051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71509344222671755861701401 53632008167003816896276051)
        ·
          refine ⟨80448012250505725344414077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53632008167003816896276051 80448012250505725344414077)
          ·
            refine ⟨30168004593939647004155279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80448012250505725344414077 30168004593939647004155279)
            ·
              refine ⟨45252006890909470506232919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30168004593939647004155279 45252006890909470506232919)
              ·
                refine ⟨67878010336364205759349379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45252006890909470506232919 67878010336364205759349379)
                ·
                  refine ⟨101817015504546308639024069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67878010336364205759349379 101817015504546308639024069)
                  ·
                    refine ⟨19090690407102432869817013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101817015504546308639024069 19090690407102432869817013)
                    ·
                      refine ⟨1789752225665853081545345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19090690407102432869817013 1789752225665853081545345)
                      ·
                        rfl

theorem cell23_3485530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3485530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485530 prefixEnd_3485530 := by exact prefixLift 3485530
  have htrace : WordTrace (prefixWord ++ tailWord_3485530) baseStart_3485530 baseEnd_3485530 := by
    simpa [prefixWord, tailWord_3485530, baseEnd_3485530] using wordTrace_append hprefix tailTrace_3485530
  have hstable : (prefixWord ++ tailWord_3485530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485530).length < 2 ^ (prefixWord ++ tailWord_3485530).sum := by decide
  have hdescent : baseEnd_3485530 < baseStart_3485530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485557 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3485557 : Nat := 118140960795 + 3485557 * 2 ^ 59
def prefixEnd_3485557 : Nat := 4983230072969 + 3 ^ 40 * 3485557 * 2
def baseEnd_3485557 : Nat := 1789766089643524475907721

theorem tailTrace_3485557 : CollatzResearch.WordTrace tailWord_3485557 prefixEnd_3485557 1789766089643524475907721 := by
  unfold tailWord_3485557
  simp only [CollatzResearch.WordTrace]
  refine ⟨127128707833429749587590925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84752471888953166391727283 127128707833429749587590925)
  ·
    refine ⟨47673265437536156095346597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127128707833429749587590925 47673265437536156095346597)
    ·
      refine ⟨8938737269538029267877487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47673265437536156095346597 8938737269538029267877487)
      ·
        refine ⟨13408105904307043901816231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8938737269538029267877487 13408105904307043901816231)
        ·
          refine ⟨20112158856460565852724347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13408105904307043901816231 20112158856460565852724347)
          ·
            refine ⟨30168238284690848779086521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20112158856460565852724347 30168238284690848779086521)
            ·
              refine ⟨22626178713518136584314891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30168238284690848779086521 22626178713518136584314891)
              ·
                refine ⟨33939268070277204876472337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22626178713518136584314891 33939268070277204876472337)
                ·
                  refine ⟨25454451052707903657354253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33939268070277204876472337 25454451052707903657354253)
                  ·
                    refine ⟨9545419144765463871507845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25454451052707903657354253 9545419144765463871507845)
                    ·
                      refine ⟨1789766089643524475907721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9545419144765463871507845 1789766089643524475907721)
                      ·
                        rfl

theorem cell23_3485557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3485557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485557 prefixEnd_3485557 := by exact prefixLift 3485557
  have htrace : WordTrace (prefixWord ++ tailWord_3485557) baseStart_3485557 baseEnd_3485557 := by
    simpa [prefixWord, tailWord_3485557, baseEnd_3485557] using wordTrace_append hprefix tailTrace_3485557
  have hstable : (prefixWord ++ tailWord_3485557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485557).length < 2 ^ (prefixWord ++ tailWord_3485557).sum := by decide
  have hdescent : baseEnd_3485557 < baseStart_3485557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485580 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 9]
def baseStart_3485580 : Nat := 118140960795 + 3485580 * 2 ^ 59
def prefixEnd_3485580 : Nat := 4983230072969 + 3 ^ 40 * 3485580 * 2
def baseEnd_3485580 : Nat := 198864211077619765102235

theorem tailTrace_3485580 : CollatzResearch.WordTrace tailWord_3485580 prefixEnd_3485580 198864211077619765102235 := by
  unfold tailWord_3485580
  simp only [CollatzResearch.WordTrace]
  refine ⟨63564773356173212257839097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84753031141564283010452129 63564773356173212257839097)
  ·
    refine ⟨47673580017129909193379323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63564773356173212257839097 47673580017129909193379323)
    ·
      refine ⟨71510370025694863790068985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47673580017129909193379323 71510370025694863790068985)
      ·
        refine ⟨53632777519271147842551739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71510370025694863790068985 53632777519271147842551739)
        ·
          refine ⟨80449166278906721763827609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53632777519271147842551739 80449166278906721763827609)
          ·
            refine ⟨60336874709180041322870707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80449166278906721763827609 60336874709180041322870707)
            ·
              refine ⟨90505312063770061984306061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60336874709180041322870707 90505312063770061984306061)
              ·
                refine ⟨33939492023913773244114773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90505312063770061984306061 33939492023913773244114773)
                ·
                  refine ⟨198864211077619765102235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33939492023913773244114773 198864211077619765102235)
                  ·
                    rfl

theorem cell23_3485580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_3485580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485580 prefixEnd_3485580 := by exact prefixLift 3485580
  have htrace : WordTrace (prefixWord ++ tailWord_3485580) baseStart_3485580 baseEnd_3485580 := by
    simpa [prefixWord, tailWord_3485580, baseEnd_3485580] using wordTrace_append hprefix tailTrace_3485580
  have hstable : (prefixWord ++ tailWord_3485580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485580).length < 2 ^ (prefixWord ++ tailWord_3485580).sum := by decide
  have hdescent : baseEnd_3485580 < baseStart_3485580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485644 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_3485644 : Nat := 118140960795 + 3485644 * 2 ^ 59
def prefixEnd_3485644 : Nat := 4983230072969 + 3 ^ 40 * 3485644 * 2
def baseEnd_3485644 : Nat := 596603587486821878506607

theorem tailTrace_3485644 : CollatzResearch.WordTrace tailWord_3485644 prefixEnd_3485644 596603587486821878506607 := by
  unfold tailWord_3485644
  simp only [CollatzResearch.WordTrace]
  refine ⟨63565940492057281723003993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84754587322743042297338657 63565940492057281723003993)
  ·
    refine ⟨47674455369042961292252995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63565940492057281723003993 47674455369042961292252995)
    ·
      refine ⟨71511683053564441938379493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47674455369042961292252995 71511683053564441938379493)
      ·
        refine ⟨13408440572543332863446155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71511683053564441938379493 13408440572543332863446155)
        ·
          refine ⟨20112660858814999295169233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13408440572543332863446155 20112660858814999295169233)
          ·
            refine ⟨15084495644111249471376925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20112660858814999295169233 15084495644111249471376925)
            ·
              refine ⟨5656685866541718551766347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15084495644111249471376925 5656685866541718551766347)
              ·
                refine ⟨8485028799812577827649521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656685866541718551766347 8485028799812577827649521)
                ·
                  refine ⟨6363771599859433370737141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485028799812577827649521 6363771599859433370737141)
                  ·
                    refine ⟨596603587486821878506607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6363771599859433370737141 596603587486821878506607)
                    ·
                      rfl

theorem cell23_3485644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_3485644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485644 prefixEnd_3485644 := by exact prefixLift 3485644
  have htrace : WordTrace (prefixWord ++ tailWord_3485644) baseStart_3485644 baseEnd_3485644 := by
    simpa [prefixWord, tailWord_3485644, baseEnd_3485644] using wordTrace_append hprefix tailTrace_3485644
  have hstable : (prefixWord ++ tailWord_3485644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485644).length < 2 ^ (prefixWord ++ tailWord_3485644).sum := by decide
  have hdescent : baseEnd_3485644 < baseStart_3485644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485647 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_3485647 : Nat := 118140960795 + 3485647 * 2 ^ 59
def prefixEnd_3485647 : Nat := 4983230072969 + 3 ^ 40 * 3485647 * 2
def baseEnd_3485647 : Nat := 1789812302902429123782307

theorem tailTrace_3485647 : CollatzResearch.WordTrace tailWord_3485647 prefixEnd_3485647 1789812302902429123782307 := by
  unfold tailWord_3485647
  simp only [CollatzResearch.WordTrace]
  refine ⟨127131990403103694958367195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84754660268735796638911463 127131990403103694958367195)
  ·
    refine ⟨190697985604655542437550793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127131990403103694958367195 190697985604655542437550793)
    ·
      refine ⟨143023489203491656828163095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190697985604655542437550793 143023489203491656828163095)
      ·
        refine ⟨214535233805237485242244643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143023489203491656828163095 214535233805237485242244643)
        ·
          refine ⟨321802850707856227863366965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214535233805237485242244643 321802850707856227863366965)
          ·
            refine ⟨30169017253861521362190653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321802850707856227863366965 30169017253861521362190653)
            ·
              refine ⟨11313381470198070510821495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30169017253861521362190653 11313381470198070510821495)
              ·
                refine ⟨16970072205297105766232243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11313381470198070510821495 16970072205297105766232243)
                ·
                  refine ⟨25455108307945658649348365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16970072205297105766232243 25455108307945658649348365)
                  ·
                    refine ⟨9545665615479621993505637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25455108307945658649348365 9545665615479621993505637)
                    ·
                      refine ⟨1789812302902429123782307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9545665615479621993505637 1789812302902429123782307)
                      ·
                        rfl

theorem cell23_3485647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_3485647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485647 prefixEnd_3485647 := by exact prefixLift 3485647
  have htrace : WordTrace (prefixWord ++ tailWord_3485647) baseStart_3485647 baseEnd_3485647 := by
    simpa [prefixWord, tailWord_3485647, baseEnd_3485647] using wordTrace_append hprefix tailTrace_3485647
  have hstable : (prefixWord ++ tailWord_3485647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485647).length < 2 ^ (prefixWord ++ tailWord_3485647).sum := by decide
  have hdescent : baseEnd_3485647 < baseStart_3485647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485725 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_3485725 : Nat := 118140960795 + 3485725 * 2 ^ 59
def prefixEnd_3485725 : Nat := 4983230072969 + 3 ^ 40 * 3485725 * 2
def baseEnd_3485725 : Nat := 596617451464493272868983

theorem tailTrace_3485725 : CollatzResearch.WordTrace tailWord_3485725 prefixEnd_3485725 596617451464493272868983 := by
  unfold tailWord_3485725
  simp only [CollatzResearch.WordTrace]
  refine ⟨127134835296821114279706629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84756556864547409519804419 127134835296821114279706629)
  ·
    refine ⟨23837781618153958927444993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127134835296821114279706629 23837781618153958927444993)
    ·
      refine ⟨17878336213615469195583745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23837781618153958927444993 17878336213615469195583745)
      ·
        refine ⟨13408752160211601896687809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17878336213615469195583745 13408752160211601896687809)
        ·
          refine ⟨10056564120158701422515857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13408752160211601896687809 10056564120158701422515857)
          ·
            refine ⟨7542423090119026066886893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10056564120158701422515857 7542423090119026066886893)
            ·
              refine ⟨2828408658794634775082585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7542423090119026066886893 2828408658794634775082585)
              ·
                refine ⟨2121306494095976081311939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828408658794634775082585 2121306494095976081311939)
                ·
                  refine ⟨3181959741143964121967909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121306494095976081311939 3181959741143964121967909)
                  ·
                    refine ⟨596617451464493272868983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3181959741143964121967909 596617451464493272868983)
                    ·
                      rfl

theorem cell23_3485725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_3485725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485725 prefixEnd_3485725 := by exact prefixLift 3485725
  have htrace : WordTrace (prefixWord ++ tailWord_3485725) baseStart_3485725 baseEnd_3485725 := by
    simpa [prefixWord, tailWord_3485725, baseEnd_3485725] using wordTrace_append hprefix tailTrace_3485725
  have hstable : (prefixWord ++ tailWord_3485725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485725).length < 2 ^ (prefixWord ++ tailWord_3485725).sum := by decide
  have hdescent : baseEnd_3485725 < baseStart_3485725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485738 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_3485738 : Nat := 118140960795 + 3485738 * 2 ^ 59
def prefixEnd_3485738 : Nat := 4983230072969 + 3 ^ 40 * 3485738 * 2
def baseEnd_3485738 : Nat := 198873225515776474193821

theorem tailTrace_3485738 : CollatzResearch.WordTrace tailWord_3485738 prefixEnd_3485738 198873225515776474193821 := by
  unfold tailWord_3485738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31783827361443504374982467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84756872963849344999953245 31783827361443504374982467)
  ·
    refine ⟨47675741042165256562473701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31783827361443504374982467 47675741042165256562473701)
    ·
      refine ⟨8939201445405985605463819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47675741042165256562473701 8939201445405985605463819)
      ·
        refine ⟨13408802168108978408195729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8939201445405985605463819 13408802168108978408195729)
        ·
          refine ⟨10056601626081733806146797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13408802168108978408195729 10056601626081733806146797)
          ·
            refine ⟨3771225609780650177305049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10056601626081733806146797 3771225609780650177305049)
            ·
              refine ⟨2828419207335487632978787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771225609780650177305049 2828419207335487632978787)
              ·
                refine ⟨4242628811003231449468181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828419207335487632978787 4242628811003231449468181)
                ·
                  refine ⟨198873225515776474193821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4242628811003231449468181 198873225515776474193821)
                  ·
                    rfl

theorem cell23_3485738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_3485738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485738 prefixEnd_3485738 := by exact prefixLift 3485738
  have htrace : WordTrace (prefixWord ++ tailWord_3485738) baseStart_3485738 baseEnd_3485738 := by
    simpa [prefixWord, tailWord_3485738, baseEnd_3485738] using wordTrace_append hprefix tailTrace_3485738
  have hstable : (prefixWord ++ tailWord_3485738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485738).length < 2 ^ (prefixWord ++ tailWord_3485738).sum := by decide
  have hdescent : baseEnd_3485738 < baseStart_3485738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485771 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 5, 2, 2]
def baseStart_3485771 : Nat := 118140960795 + 3485771 * 2 ^ 59
def prefixEnd_3485771 : Nat := 4983230072969 + 3 ^ 40 * 3485771 * 2
def baseEnd_3485771 : Nat := 1789875974503586638631737

theorem tailTrace_3485771 : CollatzResearch.WordTrace tailWord_3485771 prefixEnd_3485771 1789875974503586638631737 := by
  unfold tailWord_3485771
  simp only [CollatzResearch.WordTrace]
  refine ⟨127136513054654464135881167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84757675369769642757254111 127136513054654464135881167)
  ·
    refine ⟨190704769581981696203821751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127136513054654464135881167 190704769581981696203821751)
    ·
      refine ⟨286057154372972544305732627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190704769581981696203821751 286057154372972544305732627)
      ·
        refine ⟨429085731559458816458598941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286057154372972544305732627 429085731559458816458598941)
        ·
          refine ⟨160907149334797056171974603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429085731559458816458598941 160907149334797056171974603)
          ·
            refine ⟨241360724002195584257961905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160907149334797056171974603 241360724002195584257961905)
            ·
              refine ⟨181020543001646688193471429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241360724002195584257961905 181020543001646688193471429)
              ·
                refine ⟨33941351812808754036275893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181020543001646688193471429 33941351812808754036275893)
                ·
                  refine ⟨3182001732450820690900865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33941351812808754036275893 3182001732450820690900865)
                  ·
                    refine ⟨2386501299338115518175649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3182001732450820690900865 2386501299338115518175649)
                    ·
                      refine ⟨1789875974503586638631737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386501299338115518175649 1789875974503586638631737)
                      ·
                        rfl

theorem cell23_3485771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 2, 2].length) (baseStart_3485771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485771 prefixEnd_3485771 := by exact prefixLift 3485771
  have htrace : WordTrace (prefixWord ++ tailWord_3485771) baseStart_3485771 baseEnd_3485771 := by
    simpa [prefixWord, tailWord_3485771, baseEnd_3485771] using wordTrace_append hprefix tailTrace_3485771
  have hstable : (prefixWord ++ tailWord_3485771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485771).length < 2 ^ (prefixWord ++ tailWord_3485771).sum := by decide
  have hdescent : baseEnd_3485771 < baseStart_3485771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485781 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_3485781 : Nat := 118140960795 + 3485781 * 2 ^ 59
def prefixEnd_3485781 : Nat := 4983230072969 + 3 ^ 40 * 3485781 * 2
def baseEnd_3485781 : Nat := 596627036436710533168897

theorem tailTrace_3485781 : CollatzResearch.WordTrace tailWord_3485781 prefixEnd_3485781 596627036436710533168897 := by
  unfold tailWord_3485781
  simp only [CollatzResearch.WordTrace]
  refine ⟨127136877784618235843745197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84757918523078823895830131 127136877784618235843745197)
  ·
    refine ⟨47676329169231838441404449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127136877784618235843745197 47676329169231838441404449)
    ·
      refine ⟨35757246876923878831053337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47676329169231838441404449 35757246876923878831053337)
      ·
        refine ⟨26817935157692909123290003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35757246876923878831053337 26817935157692909123290003)
        ·
          refine ⟨40226902736539363684935005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26817935157692909123290003 40226902736539363684935005)
          ·
            refine ⟨15085088526202261381850627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40226902736539363684935005 15085088526202261381850627)
            ·
              refine ⟨22627632789303392072775941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15085088526202261381850627 22627632789303392072775941)
              ·
                refine ⟨4242681147994386013645489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22627632789303392072775941 4242681147994386013645489)
                ·
                  refine ⟨3182010860995789510234117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242681147994386013645489 3182010860995789510234117)
                  ·
                    refine ⟨596627036436710533168897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182010860995789510234117 596627036436710533168897)
                    ·
                      rfl

theorem cell23_3485781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_3485781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485781 prefixEnd_3485781 := by exact prefixLift 3485781
  have htrace : WordTrace (prefixWord ++ tailWord_3485781) baseStart_3485781 baseEnd_3485781 := by
    simpa [prefixWord, tailWord_3485781, baseEnd_3485781] using wordTrace_append hprefix tailTrace_3485781
  have hstable : (prefixWord ++ tailWord_3485781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485781).length < 2 ^ (prefixWord ++ tailWord_3485781).sum := by decide
  have hdescent : baseEnd_3485781 < baseStart_3485781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485821 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_3485821 : Nat := 118140960795 + 3485821 * 2 ^ 59
def prefixEnd_3485821 : Nat := 4983230072969 + 3 ^ 40 * 3485821 * 2
def baseEnd_3485821 : Nat := 1789901648536311443006507

theorem tailTrace_3485821 : CollatzResearch.WordTrace tailWord_3485821 prefixEnd_3485821 1789901648536311443006507 := by
  unfold tailWord_3485821
  simp only [CollatzResearch.WordTrace]
  refine ⟨127138336704473322675201317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84758891136315548450134211 127138336704473322675201317)
  ·
    refine ⟨23838438132088748001600247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127138336704473322675201317 23838438132088748001600247)
    ·
      refine ⟨35757657198133122002400371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23838438132088748001600247 35757657198133122002400371)
      ·
        refine ⟨53636485797199683003600557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35757657198133122002400371 53636485797199683003600557)
        ·
          refine ⟨20113682173949881126350209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53636485797199683003600557 20113682173949881126350209)
          ·
            refine ⟨15085261630462410844762657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113682173949881126350209 15085261630462410844762657)
            ·
              refine ⟨11313946222846808133571993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15085261630462410844762657 11313946222846808133571993)
              ·
                refine ⟨8485459667135106100178995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11313946222846808133571993 8485459667135106100178995)
                ·
                  refine ⟨12728189500702659150268493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8485459667135106100178995 12728189500702659150268493)
                  ·
                    refine ⟨4773071062763497181350685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12728189500702659150268493 4773071062763497181350685)
                    ·
                      refine ⟨1789901648536311443006507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773071062763497181350685 1789901648536311443006507)
                      ·
                        rfl

theorem cell23_3485821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_3485821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485821 prefixEnd_3485821 := by exact prefixLift 3485821
  have htrace : WordTrace (prefixWord ++ tailWord_3485821) baseStart_3485821 baseEnd_3485821 := by
    simpa [prefixWord, tailWord_3485821, baseEnd_3485821] using wordTrace_append hprefix tailTrace_3485821
  have hstable : (prefixWord ++ tailWord_3485821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485821).length < 2 ^ (prefixWord ++ tailWord_3485821).sum := by decide
  have hdescent : baseEnd_3485821 < baseStart_3485821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485912 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 2, 2, 2]
def baseStart_3485912 : Nat := 118140960795 + 3485912 * 2 ^ 59
def prefixEnd_3485912 : Nat := 4983230072969 + 3 ^ 40 * 3485912 * 2
def baseEnd_3485912 : Nat := 1789948375275870586968589

theorem tailTrace_3485912 : CollatzResearch.WordTrace tailWord_3485912 prefixEnd_3485912 1789948375275870586968589 := by
  unfold tailWord_3485912
  simp only [CollatzResearch.WordTrace]
  refine ⟨63570827873571822608381995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84761103831429096811175993 63570827873571822608381995)
  ·
    refine ⟨95356241810357733912572993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63570827873571822608381995 95356241810357733912572993)
    ·
      refine ⟨71517181357768300434429745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95356241810357733912572993 71517181357768300434429745)
      ·
        refine ⟨53637886018326225325822309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71517181357768300434429745 53637886018326225325822309)
        ·
          refine ⟨10057103628436167248591683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53637886018326225325822309 10057103628436167248591683)
          ·
            refine ⟨15085655442654250872887525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10057103628436167248591683 15085655442654250872887525)
            ·
              refine ⟨2828560395497672038666411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15085655442654250872887525 2828560395497672038666411)
              ·
                refine ⟨4242840593246508057999617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828560395497672038666411 4242840593246508057999617)
                ·
                  refine ⟨3182130444934881043499713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242840593246508057999617 3182130444934881043499713)
                  ·
                    refine ⟨2386597833701160782624785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3182130444934881043499713 2386597833701160782624785)
                    ·
                      refine ⟨1789948375275870586968589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386597833701160782624785 1789948375275870586968589)
                      ·
                        rfl

theorem cell23_3485912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_3485912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485912 prefixEnd_3485912 := by exact prefixLift 3485912
  have htrace : WordTrace (prefixWord ++ tailWord_3485912) baseStart_3485912 baseEnd_3485912 := by
    simpa [prefixWord, tailWord_3485912, baseEnd_3485912] using wordTrace_append hprefix tailTrace_3485912
  have hstable : (prefixWord ++ tailWord_3485912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485912).length < 2 ^ (prefixWord ++ tailWord_3485912).sum := by decide
  have hdescent : baseEnd_3485912 < baseStart_3485912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485914 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_3485914 : Nat := 118140960795 + 3485914 * 2 ^ 59
def prefixEnd_3485914 : Nat := 4983230072969 + 3 ^ 40 * 3485914 * 2
def baseEnd_3485914 : Nat := 596649800745726526381193

theorem tailTrace_3485914 : CollatzResearch.WordTrace tailWord_3485914 prefixEnd_3485914 596649800745726526381193 := by
  unfold tailWord_3485914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31785432173284099889584199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84761152462090933038891197 31785432173284099889584199)
  ·
    refine ⟨47678148259926149834376299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31785432173284099889584199 47678148259926149834376299)
    ·
      refine ⟨71517222389889224751564449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47678148259926149834376299 71517222389889224751564449)
      ·
        refine ⟨53637916792416918563673337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71517222389889224751564449 53637916792416918563673337)
        ·
          refine ⟨40228437594312688922755003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53637916792416918563673337 40228437594312688922755003)
          ·
            refine ⟨60342656391469033384132505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40228437594312688922755003 60342656391469033384132505)
            ·
              refine ⟨45256992293601775038099379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60342656391469033384132505 45256992293601775038099379)
              ·
                refine ⟨67885488440402662557149069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45256992293601775038099379 67885488440402662557149069)
                ·
                  refine ⟨25457058165150998458930901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67885488440402662557149069 25457058165150998458930901)
                  ·
                    refine ⟨596649800745726526381193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25457058165150998458930901 596649800745726526381193)
                    ·
                      rfl

theorem cell23_3485914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_3485914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485914 prefixEnd_3485914 := by exact prefixLift 3485914
  have htrace : WordTrace (prefixWord ++ tailWord_3485914) baseStart_3485914 baseEnd_3485914 := by
    simpa [prefixWord, tailWord_3485914, baseEnd_3485914] using wordTrace_append hprefix tailTrace_3485914
  have hstable : (prefixWord ++ tailWord_3485914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485914).length < 2 ^ (prefixWord ++ tailWord_3485914).sum := by decide
  have hdescent : baseEnd_3485914 < baseStart_3485914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485916 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3485916 : Nat := 118140960795 + 3485916 * 2 ^ 59
def prefixEnd_3485916 : Nat := 4983230072969 + 3 ^ 40 * 3485916 * 2
def baseEnd_3485916 : Nat := 1789950429198488571318571

theorem tailTrace_3485916 : CollatzResearch.WordTrace tailWord_3485916 prefixEnd_3485916 1789950429198488571318571 := by
  unfold tailWord_3485916
  simp only [CollatzResearch.WordTrace]
  refine ⟨63570900819564576949954801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84761201092752769266606401 63570900819564576949954801)
  ·
    refine ⟨47678175614673432712466101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63570900819564576949954801 47678175614673432712466101)
    ·
      refine ⟨4469828963875634316793697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47678175614673432712466101 4469828963875634316793697)
      ·
        refine ⟨3352371722906725737595273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4469828963875634316793697 3352371722906725737595273)
        ·
          refine ⟨2514278792180044303196455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352371722906725737595273 2514278792180044303196455)
          ·
            refine ⟨3771418188270066454794683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514278792180044303196455 3771418188270066454794683)
            ·
              refine ⟨5657127282405099682192025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771418188270066454794683 5657127282405099682192025)
              ·
                refine ⟨4242845461803824761644019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657127282405099682192025 4242845461803824761644019)
                ·
                  refine ⟨6364268192705737142466029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242845461803824761644019 6364268192705737142466029)
                  ·
                    refine ⟨2386600572264651428424761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6364268192705737142466029 2386600572264651428424761)
                    ·
                      refine ⟨1789950429198488571318571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386600572264651428424761 1789950429198488571318571)
                      ·
                        rfl

theorem cell23_3485916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3485916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485916 prefixEnd_3485916 := by exact prefixLift 3485916
  have htrace : WordTrace (prefixWord ++ tailWord_3485916) baseStart_3485916 baseEnd_3485916 := by
    simpa [prefixWord, tailWord_3485916, baseEnd_3485916] using wordTrace_append hprefix tailTrace_3485916
  have hstable : (prefixWord ++ tailWord_3485916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485916).length < 2 ^ (prefixWord ++ tailWord_3485916).sum := by decide
  have hdescent : baseEnd_3485916 < baseStart_3485916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485924 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_3485924 : Nat := 118140960795 + 3485924 * 2 ^ 59
def prefixEnd_3485924 : Nat := 4983230072969 + 3 ^ 40 * 3485924 * 2
def baseEnd_3485924 : Nat := 1789954537043724540018533

theorem tailTrace_3485924 : CollatzResearch.WordTrace tailWord_3485924 prefixEnd_3485924 1789954537043724540018533 := by
  unfold tailWord_3485924
  simp only [CollatzResearch.WordTrace]
  refine ⟨63571046711550085633100413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84761395615400114177467217 63571046711550085633100413)
  ·
    refine ⟨23839142516831282112412655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63571046711550085633100413 23839142516831282112412655)
    ·
      refine ⟨35758713775246923168618983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23839142516831282112412655 35758713775246923168618983)
      ·
        refine ⟨53638070662870384752928475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35758713775246923168618983 53638070662870384752928475)
        ·
          refine ⟨80457105994305577129392713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53638070662870384752928475 80457105994305577129392713)
          ·
            refine ⟨60342829495729182847044535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80457105994305577129392713 60342829495729182847044535)
            ·
              refine ⟨90514244243593774270566803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60342829495729182847044535 90514244243593774270566803)
              ·
                refine ⟨135771366365390661405850205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90514244243593774270566803 135771366365390661405850205)
                ·
                  refine ⟨50914262387021498027193827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135771366365390661405850205 50914262387021498027193827)
                  ·
                    refine ⟨76371393580532247040790741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50914262387021498027193827 76371393580532247040790741)
                    ·
                      refine ⟨1789954537043724540018533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76371393580532247040790741 1789954537043724540018533)
                      ·
                        rfl

theorem cell23_3485924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_3485924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485924 prefixEnd_3485924 := by exact prefixLift 3485924
  have htrace : WordTrace (prefixWord ++ tailWord_3485924) baseStart_3485924 baseEnd_3485924 := by
    simpa [prefixWord, tailWord_3485924, baseEnd_3485924] using wordTrace_append hprefix tailTrace_3485924
  have hstable : (prefixWord ++ tailWord_3485924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485924).length < 2 ^ (prefixWord ++ tailWord_3485924).sum := by decide
  have hdescent : baseEnd_3485924 < baseStart_3485924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485931 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 2, 5]
def baseStart_3485931 : Nat := 118140960795 + 3485931 * 2 ^ 59
def prefixEnd_3485931 : Nat := 4983230072969 + 3 ^ 40 * 3485931 * 2
def baseEnd_3485931 : Nat := 596652710469435337543667

theorem tailTrace_3485931 : CollatzResearch.WordTrace tailWord_3485931 prefixEnd_3485931 596652710469435337543667 := by
  unfold tailWord_3485931
  simp only [CollatzResearch.WordTrace]
  refine ⟨127142348734074811461705647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84761565822716540974470431 127142348734074811461705647)
  ·
    refine ⟨190713523101112217192558471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127142348734074811461705647 190713523101112217192558471)
    ·
      refine ⟨286070284651668325788837707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190713523101112217192558471 286070284651668325788837707)
      ·
        refine ⟨429105426977502488683256561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286070284651668325788837707 429105426977502488683256561)
        ·
          refine ⟨321829070233126866512442421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429105426977502488683256561 321829070233126866512442421)
          ·
            refine ⟨30171475334355643735541477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321829070233126866512442421 30171475334355643735541477)
            ·
              refine ⟨5657151625191683200414027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30171475334355643735541477 5657151625191683200414027)
              ·
                refine ⟨8485727437787524800621041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657151625191683200414027 8485727437787524800621041)
                ·
                  refine ⟨6364295578340643600465781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485727437787524800621041 6364295578340643600465781)
                  ·
                    refine ⟨596652710469435337543667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6364295578340643600465781 596652710469435337543667)
                    ·
                      rfl

theorem cell23_3485931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 5].length) (baseStart_3485931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485931 prefixEnd_3485931 := by exact prefixLift 3485931
  have htrace : WordTrace (prefixWord ++ tailWord_3485931) baseStart_3485931 baseEnd_3485931 := by
    simpa [prefixWord, tailWord_3485931, baseEnd_3485931] using wordTrace_append hprefix tailTrace_3485931
  have hstable : (prefixWord ++ tailWord_3485931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485931).length < 2 ^ (prefixWord ++ tailWord_3485931).sum := by decide
  have hdescent : baseEnd_3485931 < baseStart_3485931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485951 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_3485951 : Nat := 118140960795 + 3485951 * 2 ^ 59
def prefixEnd_3485951 : Nat := 4983230072969 + 3 ^ 40 * 3485951 * 2
def baseEnd_3485951 : Nat := 1789968401021395934380909

theorem tailTrace_3485951 : CollatzResearch.WordTrace tailWord_3485951 prefixEnd_3485951 1789968401021395934380909 := by
  unfold tailWord_3485951
  simp only [CollatzResearch.WordTrace]
  refine ⟨127143078194002354877433707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84762052129334903251622471 127143078194002354877433707)
  ·
    refine ⟨190714617291003532316150561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127143078194002354877433707 190714617291003532316150561)
    ·
      refine ⟨143035962968252649237112921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190714617291003532316150561 143035962968252649237112921)
      ·
        refine ⟨107276972226189486927834691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143035962968252649237112921 107276972226189486927834691)
        ·
          refine ⟨160915458339284230391752037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107276972226189486927834691 160915458339284230391752037)
          ·
            refine ⟨30171648438615793198453507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160915458339284230391752037 30171648438615793198453507)
            ·
              refine ⟨45257472657923689797680261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30171648438615793198453507 45257472657923689797680261)
              ·
                refine ⟨8485776123360691837065049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45257472657923689797680261 8485776123360691837065049)
                ·
                  refine ⟨6364332092520518877798787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485776123360691837065049 6364332092520518877798787)
                  ·
                    refine ⟨9546498138780778316698181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6364332092520518877798787 9546498138780778316698181)
                    ·
                      refine ⟨1789968401021395934380909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9546498138780778316698181 1789968401021395934380909)
                      ·
                        rfl

theorem cell23_3485951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_3485951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485951 prefixEnd_3485951 := by exact prefixLift 3485951
  have htrace : WordTrace (prefixWord ++ tailWord_3485951) baseStart_3485951 baseEnd_3485951 := by
    simpa [prefixWord, tailWord_3485951, baseEnd_3485951] using wordTrace_append hprefix tailTrace_3485951
  have hstable : (prefixWord ++ tailWord_3485951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485951).length < 2 ^ (prefixWord ++ tailWord_3485951).sum := by decide
  have hdescent : baseEnd_3485951 < baseStart_3485951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485971 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 3]
def baseStart_3485971 : Nat := 118140960795 + 3485971 * 2 ^ 59
def prefixEnd_3485971 : Nat := 4983230072969 + 3 ^ 40 * 3485971 * 2
def baseEnd_3485971 : Nat := 1789978670634485856130817

theorem tailTrace_3485971 : CollatzResearch.WordTrace tailWord_3485971 prefixEnd_3485971 1789978670634485856130817 := by
  unfold tailWord_3485971
  simp only [CollatzResearch.WordTrace]
  refine ⟨127143807653929898293161767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84762538435953265528774511 127143807653929898293161767)
  ·
    refine ⟨190715711480894847439742651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127143807653929898293161767 190715711480894847439742651)
    ·
      refine ⟨286073567221342271159613977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190715711480894847439742651 286073567221342271159613977)
      ·
        refine ⟨214555175416006703369710483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286073567221342271159613977 214555175416006703369710483)
        ·
          refine ⟨321832763124010055054565725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214555175416006703369710483 321832763124010055054565725)
          ·
            refine ⟨120687286171503770645462147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321832763124010055054565725 120687286171503770645462147)
            ·
              refine ⟨181030929257255655968193221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120687286171503770645462147 181030929257255655968193221)
              ·
                refine ⟨33943299235735435494036229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181030929257255655968193221 33943299235735435494036229)
                ·
                  refine ⟨6364368606700394155131793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33943299235735435494036229 6364368606700394155131793)
                  ·
                    refine ⟨4773276455025295616348845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6364368606700394155131793 4773276455025295616348845)
                    ·
                      refine ⟨1789978670634485856130817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773276455025295616348845 1789978670634485856130817)
                      ·
                        rfl

theorem cell23_3485971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_3485971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485971 prefixEnd_3485971 := by exact prefixLift 3485971
  have htrace : WordTrace (prefixWord ++ tailWord_3485971) baseStart_3485971 baseEnd_3485971 := by
    simpa [prefixWord, tailWord_3485971, baseEnd_3485971] using wordTrace_append hprefix tailTrace_3485971
  have hstable : (prefixWord ++ tailWord_3485971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485971).length < 2 ^ (prefixWord ++ tailWord_3485971).sum := by decide
  have hdescent : baseEnd_3485971 < baseStart_3485971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485982 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3485982 : Nat := 118140960795 + 3485982 * 2 ^ 59
def prefixEnd_3485982 : Nat := 4983230072969 + 3 ^ 40 * 3485982 * 2
def baseEnd_3485982 : Nat := 596661439640561771031089

theorem tailTrace_3485982 : CollatzResearch.WordTrace tailWord_3485982 prefixEnd_3485982 596661439640561771031089 := by
  unfold tailWord_3485982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893026107111255896476525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84762805904593364781208133 15893026107111255896476525)
  ·
    refine ⟨5959884790166720961178697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15893026107111255896476525 5959884790166720961178697)
    ·
      refine ⟨4469913592625040720884023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5959884790166720961178697 4469913592625040720884023)
      ·
        refine ⟨6704870388937561081326035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469913592625040720884023 6704870388937561081326035)
        ·
          refine ⟨10057305583406341621989053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704870388937561081326035 10057305583406341621989053)
          ·
            refine ⟨3771489593777378108245895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10057305583406341621989053 3771489593777378108245895)
            ·
              refine ⟨5657234390666067162368843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771489593777378108245895 5657234390666067162368843)
              ·
                refine ⟨8485851585999100743553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657234390666067162368843 8485851585999100743553265)
                ·
                  refine ⟨6364388689499325557664949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485851585999100743553265 6364388689499325557664949)
                  ·
                    refine ⟨596661439640561771031089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6364388689499325557664949 596661439640561771031089)
                    ·
                      rfl

theorem cell23_3485982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3485982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485982 prefixEnd_3485982 := by exact prefixLift 3485982
  have htrace : WordTrace (prefixWord ++ tailWord_3485982) baseStart_3485982 baseEnd_3485982 := by
    simpa [prefixWord, tailWord_3485982, baseEnd_3485982] using wordTrace_append hprefix tailTrace_3485982
  have hstable : (prefixWord ++ tailWord_3485982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485982).length < 2 ^ (prefixWord ++ tailWord_3485982).sum := by decide
  have hdescent : baseEnd_3485982 < baseStart_3485982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485988 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_3485988 : Nat := 118140960795 + 3485988 * 2 ^ 59
def prefixEnd_3485988 : Nat := 4983230072969 + 3 ^ 40 * 3485988 * 2
def baseEnd_3485988 : Nat := 1789987399805612289618239

theorem tailTrace_3485988 : CollatzResearch.WordTrace tailWord_3485988 prefixEnd_3485988 1789987399805612289618239 := by
  unfold tailWord_3485988
  simp only [CollatzResearch.WordTrace]
  refine ⟨63572213847434155098265309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84762951796578873464353745 63572213847434155098265309)
  ·
    refine ⟨23839580192787808161849491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63572213847434155098265309 23839580192787808161849491)
    ·
      refine ⟨35759370289181712242774237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23839580192787808161849491 35759370289181712242774237)
      ·
        refine ⟨13409763858443142091040339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35759370289181712242774237 13409763858443142091040339)
        ·
          refine ⟨20114645787664713136560509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409763858443142091040339 20114645787664713136560509)
          ·
            refine ⟨7542992170374267426210191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20114645787664713136560509 7542992170374267426210191)
            ·
              refine ⟨11314488255561401139315287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7542992170374267426210191 11314488255561401139315287)
              ·
                refine ⟨16971732383342101708972931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314488255561401139315287 16971732383342101708972931)
                ·
                  refine ⟨25457598575013152563459397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16971732383342101708972931 25457598575013152563459397)
                  ·
                    refine ⟨4773299732814966105648637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25457598575013152563459397 4773299732814966105648637)
                    ·
                      refine ⟨1789987399805612289618239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773299732814966105648637 1789987399805612289618239)
                      ·
                        rfl

theorem cell23_3485988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_3485988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3485988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3485988 prefixEnd_3485988 := by exact prefixLift 3485988
  have htrace : WordTrace (prefixWord ++ tailWord_3485988) baseStart_3485988 baseEnd_3485988 := by
    simpa [prefixWord, tailWord_3485988, baseEnd_3485988] using wordTrace_append hprefix tailTrace_3485988
  have hstable : (prefixWord ++ tailWord_3485988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485988).length < 2 ^ (prefixWord ++ tailWord_3485988).sum := by decide
  have hdescent : baseEnd_3485988 < baseStart_3485988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486028 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 3, 5, 2]
def baseStart_3486028 : Nat := 118140960795 + 3486028 * 2 ^ 59
def prefixEnd_3486028 : Nat := 4983230072969 + 3 ^ 40 * 3486028 * 2
def baseEnd_3486028 : Nat := 1790007939031792133118055

theorem tailTrace_3486028 : CollatzResearch.WordTrace tailWord_3486028 prefixEnd_3486028 1790007939031792133118055 := by
  unfold tailWord_3486028
  simp only [CollatzResearch.WordTrace]
  refine ⟨63572943307361698513993369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84763924409815598018657825 63572943307361698513993369)
  ·
    refine ⟨47679707480521273885495027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63572943307361698513993369 47679707480521273885495027)
    ·
      refine ⟨71519561220781910828242541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47679707480521273885495027 71519561220781910828242541)
      ·
        refine ⟨26819835457793216560590953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71519561220781910828242541 26819835457793216560590953)
        ·
          refine ⟨20114876593344912420443215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26819835457793216560590953 20114876593344912420443215)
          ·
            refine ⟨30172314890017368630664823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20114876593344912420443215 30172314890017368630664823)
            ·
              refine ⟨45258472335026052945997235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30172314890017368630664823 45258472335026052945997235)
              ·
                refine ⟨67887708502539079418995853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45258472335026052945997235 67887708502539079418995853)
                ·
                  refine ⟨25457890688452154782123445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67887708502539079418995853 25457890688452154782123445)
                  ·
                    refine ⟨2386677252042389510824073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25457890688452154782123445 2386677252042389510824073)
                    ·
                      refine ⟨1790007939031792133118055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386677252042389510824073 1790007939031792133118055)
                      ·
                        rfl

theorem cell23_3486028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_3486028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486028 prefixEnd_3486028 := by exact prefixLift 3486028
  have htrace : WordTrace (prefixWord ++ tailWord_3486028) baseStart_3486028 baseEnd_3486028 := by
    simpa [prefixWord, tailWord_3486028, baseEnd_3486028] using wordTrace_append hprefix tailTrace_3486028
  have hstable : (prefixWord ++ tailWord_3486028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486028).length < 2 ^ (prefixWord ++ tailWord_3486028).sum := by decide
  have hdescent : baseEnd_3486028 < baseStart_3486028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486051 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 3, 6]
def baseStart_3486051 : Nat := 118140960795 + 3486051 * 2 ^ 59
def prefixEnd_3486051 : Nat := 4983230072969 + 3 ^ 40 * 3486051 * 2
def baseEnd_3486051 : Nat := 596673249695615181043483

theorem tailTrace_3486051 : CollatzResearch.WordTrace tailWord_3486051 prefixEnd_3486051 596673249695615181043483 := by
  unfold tailWord_3486051
  simp only [CollatzResearch.WordTrace]
  refine ⟨127146725493640071956074007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84764483662426714637382671 127146725493640071956074007)
  ·
    refine ⟨190720088240460107934111011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127146725493640071956074007 190720088240460107934111011)
    ·
      refine ⟨286080132360690161901166517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190720088240460107934111011 286080132360690161901166517)
      ·
        refine ⟨26820012408814702678234361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 286080132360690161901166517 26820012408814702678234361)
        ·
          refine ⟨20115009306611027008675771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26820012408814702678234361 20115009306611027008675771)
          ·
            refine ⟨30172513959916540513013657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115009306611027008675771 30172513959916540513013657)
            ·
              refine ⟨22629385469937405384760243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30172513959916540513013657 22629385469937405384760243)
              ·
                refine ⟨33944078204906108077140365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22629385469937405384760243 33944078204906108077140365)
                ·
                  refine ⟨12729029326839790528927637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33944078204906108077140365 12729029326839790528927637)
                  ·
                    refine ⟨596673249695615181043483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12729029326839790528927637 596673249695615181043483)
                    ·
                      rfl

theorem cell23_3486051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 6].length) (baseStart_3486051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486051 prefixEnd_3486051 := by exact prefixLift 3486051
  have htrace : WordTrace (prefixWord ++ tailWord_3486051) baseStart_3486051 baseEnd_3486051 := by
    simpa [prefixWord, tailWord_3486051, baseEnd_3486051] using wordTrace_append hprefix tailTrace_3486051
  have hstable : (prefixWord ++ tailWord_3486051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486051).length < 2 ^ (prefixWord ++ tailWord_3486051).sum := by decide
  have hdescent : baseEnd_3486051 < baseStart_3486051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486071 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_3486071 : Nat := 118140960795 + 3486071 * 2 ^ 59
def prefixEnd_3486071 : Nat := 4983230072969 + 3 ^ 40 * 3486071 * 2
def baseEnd_3486071 : Nat := 1790030018699935464880357

theorem tailTrace_3486071 : CollatzResearch.WordTrace tailWord_3486071 prefixEnd_3486071 1790030018699935464880357 := by
  unfold tailWord_3486071
  simp only [CollatzResearch.WordTrace]
  refine ⟨127147454953567615371802067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84764969969045076914534711 127147454953567615371802067)
  ·
    refine ⟨190721182430351423057703101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127147454953567615371802067 190721182430351423057703101)
    ·
      refine ⟨71520443411381783646638663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190721182430351423057703101 71520443411381783646638663)
      ·
        refine ⟨107280665117072675469957995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71520443411381783646638663 107280665117072675469957995)
        ·
          refine ⟨160920997675609013204936993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107280665117072675469957995 160920997675609013204936993)
          ·
            refine ⟨120690748256706759903702745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160920997675609013204936993 120690748256706759903702745)
            ·
              refine ⟨90518061192530069927777059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120690748256706759903702745 90518061192530069927777059)
              ·
                refine ⟨135777091788795104891665589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90518061192530069927777059 135777091788795104891665589)
                ·
                  refine ⟨12729102355199541083593649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135777091788795104891665589 12729102355199541083593649)
                  ·
                    refine ⟨9546826766399655812695237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12729102355199541083593649 9546826766399655812695237)
                    ·
                      refine ⟨1790030018699935464880357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9546826766399655812695237 1790030018699935464880357)
                      ·
                        rfl

theorem cell23_3486071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_3486071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486071 prefixEnd_3486071 := by exact prefixLift 3486071
  have htrace : WordTrace (prefixWord ++ tailWord_3486071) baseStart_3486071 baseEnd_3486071 := by
    simpa [prefixWord, tailWord_3486071, baseEnd_3486071] using wordTrace_append hprefix tailTrace_3486071
  have hstable : (prefixWord ++ tailWord_3486071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486071).length < 2 ^ (prefixWord ++ tailWord_3486071).sum := by decide
  have hdescent : baseEnd_3486071 < baseStart_3486071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486088 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3486088 : Nat := 118140960795 + 3486088 * 2 ^ 59
def prefixEnd_3486088 : Nat := 4983230072969 + 3 ^ 40 * 3486088 * 2
def baseEnd_3486088 : Nat := 1790038747871061898367779

theorem tailTrace_3486088 : CollatzResearch.WordTrace tailWord_3486088 prefixEnd_3486088 1790038747871061898367779 := by
  unfold tailWord_3486088
  simp only [CollatzResearch.WordTrace]
  refine ⟨63574037497253013637585459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84765383329670684850113945 63574037497253013637585459)
  ·
    refine ⟨95361056245879520456378189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63574037497253013637585459 95361056245879520456378189)
    ·
      refine ⟨35760396092204820171141821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95361056245879520456378189 35760396092204820171141821)
      ·
        refine ⟨13410148534576807564178183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35760396092204820171141821 13410148534576807564178183)
        ·
          refine ⟨20115222801865211346267275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410148534576807564178183 20115222801865211346267275)
          ·
            refine ⟨30172834202797817019400913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115222801865211346267275 30172834202797817019400913)
            ·
              refine ⟨22629625652098362764550685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30172834202797817019400913 22629625652098362764550685)
              ·
                refine ⟨8486109619536886036706507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22629625652098362764550685 8486109619536886036706507)
                ·
                  refine ⟨12729164429305329055059761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8486109619536886036706507 12729164429305329055059761)
                  ·
                    refine ⟨9546873321978996791294821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12729164429305329055059761 9546873321978996791294821)
                    ·
                      refine ⟨1790038747871061898367779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9546873321978996791294821 1790038747871061898367779)
                      ·
                        rfl

theorem cell23_3486088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3486088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486088 prefixEnd_3486088 := by exact prefixLift 3486088
  have htrace : WordTrace (prefixWord ++ tailWord_3486088) baseStart_3486088 baseEnd_3486088 := by
    simpa [prefixWord, tailWord_3486088, baseEnd_3486088] using wordTrace_append hprefix tailTrace_3486088
  have hstable : (prefixWord ++ tailWord_3486088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486088).length < 2 ^ (prefixWord ++ tailWord_3486088).sum := by decide
  have hdescent : baseEnd_3486088 < baseStart_3486088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486112 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 1, 2, 3]
def baseStart_3486112 : Nat := 118140960795 + 3486112 * 2 ^ 59
def prefixEnd_3486112 : Nat := 4983230072969 + 3 ^ 40 * 3486112 * 2
def baseEnd_3486112 : Nat := 1790051071406769804467669

theorem tailTrace_3486112 : CollatzResearch.WordTrace tailWord_3486112 prefixEnd_3486112 1790051071406769804467669 := by
  unfold tailWord_3486112
  simp only [CollatzResearch.WordTrace]
  refine ⟨63574475173209539687022295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84765966897612719582696393 63574475173209539687022295)
  ·
    refine ⟨95361712759814309530533443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63574475173209539687022295 95361712759814309530533443)
    ·
      refine ⟨143042569139721464295800165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95361712759814309530533443 143042569139721464295800165)
      ·
        refine ⟨26820481713697774555462531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143042569139721464295800165 26820481713697774555462531)
        ·
          refine ⟨40230722570546661833193797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26820481713697774555462531 40230722570546661833193797)
          ·
            refine ⟨7543260481977499093723837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40230722570546661833193797 7543260481977499093723837)
            ·
              refine ⟨2828722680741562160146439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7543260481977499093723837 2828722680741562160146439)
              ·
                refine ⟨4243084021112343240219659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828722680741562160146439 4243084021112343240219659)
                ·
                  refine ⟨6364626031668514860329489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243084021112343240219659 6364626031668514860329489)
                  ·
                    refine ⟨4773469523751386145247117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6364626031668514860329489 4773469523751386145247117)
                    ·
                      refine ⟨1790051071406769804467669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773469523751386145247117 1790051071406769804467669)
                      ·
                        rfl

theorem cell23_3486112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_3486112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486112 prefixEnd_3486112 := by exact prefixLift 3486112
  have htrace : WordTrace (prefixWord ++ tailWord_3486112) baseStart_3486112 baseEnd_3486112 := by
    simpa [prefixWord, tailWord_3486112, baseEnd_3486112] using wordTrace_append hprefix tailTrace_3486112
  have hstable : (prefixWord ++ tailWord_3486112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486112).length < 2 ^ (prefixWord ++ tailWord_3486112).sum := by decide
  have hdescent : baseEnd_3486112 < baseStart_3486112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486121 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_3486121 : Nat := 118140960795 + 3486121 * 2 ^ 59
def prefixEnd_3486121 : Nat := 4983230072969 + 3 ^ 40 * 3486121 * 2
def baseEnd_3486121 : Nat := 1790055692732660269255127

theorem tailTrace_3486121 : CollatzResearch.WordTrace tailWord_3486121 prefixEnd_3486121 1790055692732660269255127 := by
  unfold tailWord_3486121
  simp only [CollatzResearch.WordTrace]
  refine ⟨127149278603386473911122217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84766185735590982607414811 127149278603386473911122217)
  ·
    refine ⟨95361958952539855433341663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127149278603386473911122217 95361958952539855433341663)
    ·
      refine ⟨143042938428809783150012495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95361958952539855433341663 143042938428809783150012495)
      ·
        refine ⟨214564407643214674725018743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143042938428809783150012495 214564407643214674725018743)
        ·
          refine ⟨321846611464822012087528115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214564407643214674725018743 321846611464822012087528115)
          ·
            refine ⟨482769917197233018131292173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321846611464822012087528115 482769917197233018131292173)
            ·
              refine ⟨181038718948962381799234565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482769917197233018131292173 181038718948962381799234565)
              ·
                refine ⟨33944759802930446587356481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181038718948962381799234565 33944759802930446587356481)
                ·
                  refine ⟨25458569852197834940517361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33944759802930446587356481 25458569852197834940517361)
                  ·
                    refine ⟨19093927389148376205388021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25458569852197834940517361 19093927389148376205388021)
                    ·
                      refine ⟨1790055692732660269255127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19093927389148376205388021 1790055692732660269255127)
                      ·
                        rfl

theorem cell23_3486121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_3486121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486121 prefixEnd_3486121 := by exact prefixLift 3486121
  have htrace : WordTrace (prefixWord ++ tailWord_3486121) baseStart_3486121 baseEnd_3486121 := by
    simpa [prefixWord, tailWord_3486121, baseEnd_3486121] using wordTrace_append hprefix tailTrace_3486121
  have hstable : (prefixWord ++ tailWord_3486121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486121).length < 2 ^ (prefixWord ++ tailWord_3486121).sum := by decide
  have hdescent : baseEnd_3486121 < baseStart_3486121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486135 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 3, 3, 2]
def baseStart_3486135 : Nat := 118140960795 + 3486135 * 2 ^ 59
def prefixEnd_3486135 : Nat := 4983230072969 + 3 ^ 40 * 3486135 * 2
def baseEnd_3486135 : Nat := 1790062881461823214480063

theorem tailTrace_3486135 : CollatzResearch.WordTrace tailWord_3486135 prefixEnd_3486135 1790062881461823214480063 := by
  unfold tailWord_3486135
  simp only [CollatzResearch.WordTrace]
  refine ⟨127149789225335754302131859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84766526150223836201421239 127149789225335754302131859)
  ·
    refine ⟨190724683838003631453197789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127149789225335754302131859 190724683838003631453197789)
    ·
      refine ⟨71521756439251361794949171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190724683838003631453197789 71521756439251361794949171)
      ·
        refine ⟨107282634658877042692423757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71521756439251361794949171 107282634658877042692423757)
        ·
          refine ⟨40230987997078891009658909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107282634658877042692423757 40230987997078891009658909)
          ·
            refine ⟨15086620498904584128622091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40230987997078891009658909 15086620498904584128622091)
            ·
              refine ⟨22629930748356876192933137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15086620498904584128622091 22629930748356876192933137)
              ·
                refine ⟨16972448061267657144699853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22629930748356876192933137 16972448061267657144699853)
                ·
                  refine ⟨6364668022975371429262445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16972448061267657144699853 6364668022975371429262445)
                  ·
                    refine ⟨2386750508615764285973417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6364668022975371429262445 2386750508615764285973417)
                    ·
                      refine ⟨1790062881461823214480063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386750508615764285973417 1790062881461823214480063)
                      ·
                        rfl

theorem cell23_3486135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_3486135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486135 prefixEnd_3486135 := by exact prefixLift 3486135
  have htrace : WordTrace (prefixWord ++ tailWord_3486135) baseStart_3486135 baseEnd_3486135 := by
    simpa [prefixWord, tailWord_3486135, baseEnd_3486135] using wordTrace_append hprefix tailTrace_3486135
  have hstable : (prefixWord ++ tailWord_3486135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486135).length < 2 ^ (prefixWord ++ tailWord_3486135).sum := by decide
  have hdescent : baseEnd_3486135 < baseStart_3486135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486142 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_3486142 : Nat := 118140960795 + 3486142 * 2 ^ 59
def prefixEnd_3486142 : Nat := 4983230072969 + 3 ^ 40 * 3486142 * 2
def baseEnd_3486142 : Nat := 1790066475826404687092531

theorem tailTrace_3486142 : CollatzResearch.WordTrace tailWord_3486142 prefixEnd_3486142 1790066475826404687092531 := by
  unfold tailWord_3486142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893755567038799312204585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84766696357540262998424453 15893755567038799312204585)
  ·
    refine ⟨11920316675279099484153439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15893755567038799312204585 11920316675279099484153439)
    ·
      refine ⟨17880475012918649226230159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11920316675279099484153439 17880475012918649226230159)
      ·
        refine ⟨26820712519377973839345239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17880475012918649226230159 26820712519377973839345239)
        ·
          refine ⟨40231068779066960759017859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26820712519377973839345239 40231068779066960759017859)
          ·
            refine ⟨60346603168600441138526789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40231068779066960759017859 60346603168600441138526789)
            ·
              refine ⟨11314988094112582713473773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60346603168600441138526789 11314988094112582713473773)
              ·
                refine ⟨4243120535292218517552665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11314988094112582713473773 4243120535292218517552665)
                ·
                  refine ⟨3182340401469163888164499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4243120535292218517552665 3182340401469163888164499)
                  ·
                    refine ⟨4773510602203745832246749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182340401469163888164499 4773510602203745832246749)
                    ·
                      refine ⟨1790066475826404687092531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773510602203745832246749 1790066475826404687092531)
                      ·
                        rfl

theorem cell23_3486142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_3486142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486142 prefixEnd_3486142 := by exact prefixLift 3486142
  have htrace : WordTrace (prefixWord ++ tailWord_3486142) baseStart_3486142 baseEnd_3486142 := by
    simpa [prefixWord, tailWord_3486142, baseEnd_3486142] using wordTrace_append hprefix tailTrace_3486142
  have hstable : (prefixWord ++ tailWord_3486142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486142).length < 2 ^ (prefixWord ++ tailWord_3486142).sum := by decide
  have hdescent : baseEnd_3486142 < baseStart_3486142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486188 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 7]
def baseStart_3486188 : Nat := 118140960795 + 3486188 * 2 ^ 59
def prefixEnd_3486188 : Nat := 4983230072969 + 3 ^ 40 * 3486188 * 2
def baseEnd_3486188 : Nat := 198898899548501278568591

theorem tailTrace_3486188 : CollatzResearch.WordTrace tailWord_3486188 prefixEnd_3486188 198898899548501278568591 := by
  unfold tailWord_3486188
  simp only [CollatzResearch.WordTrace]
  refine ⟨63575861147071872176905609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84767814862762496235874145 63575861147071872176905609)
  ·
    refine ⟨47681895860303904132679207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63575861147071872176905609 47681895860303904132679207)
    ·
      refine ⟨71522843790455856199018811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47681895860303904132679207 71522843790455856199018811)
      ·
        refine ⟨107284265685683784298528217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71522843790455856199018811 107284265685683784298528217)
        ·
          refine ⟨80463199264262838223896163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107284265685683784298528217 80463199264262838223896163)
          ·
            refine ⟨120694798896394257335844245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80463199264262838223896163 120694798896394257335844245)
            ·
              refine ⟨5657568698268480812617699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120694798896394257335844245 5657568698268480812617699)
              ·
                refine ⟨8486353047402721218926549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657568698268480812617699 8486353047402721218926549)
                ·
                  refine ⟨198898899548501278568591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8486353047402721218926549 198898899548501278568591)
                  ·
                    rfl

theorem cell23_3486188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_3486188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486188 prefixEnd_3486188 := by exact prefixLift 3486188
  have htrace : WordTrace (prefixWord ++ tailWord_3486188) baseStart_3486188 baseEnd_3486188 := by
    simpa [prefixWord, tailWord_3486188, baseEnd_3486188] using wordTrace_append hprefix tailTrace_3486188
  have hstable : (prefixWord ++ tailWord_3486188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486188).length < 2 ^ (prefixWord ++ tailWord_3486188).sum := by decide
  have hdescent : baseEnd_3486188 < baseStart_3486188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486218 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_3486218 : Nat := 118140960795 + 3486218 * 2 ^ 59
def prefixEnd_3486218 : Nat := 4983230072969 + 3 ^ 40 * 3486218 * 2
def baseEnd_3486218 : Nat := 596701833452048796580727

theorem tailTrace_3486218 : CollatzResearch.WordTrace tailWord_3486218 prefixEnd_3486218 596701833452048796580727 := by
  unfold tailWord_3486218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31788204121008764869350827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84768544322690039651602205 31788204121008764869350827)
  ·
    refine ⟨47682306181513147304026241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31788204121008764869350827 47682306181513147304026241)
    ·
      refine ⟨35761729636134860478019681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47682306181513147304026241 35761729636134860478019681)
      ·
        refine ⟨26821297227101145358514761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35761729636134860478019681 26821297227101145358514761)
        ·
          refine ⟨20115972920325859018886071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26821297227101145358514761 20115972920325859018886071)
          ·
            refine ⟨30173959380488788528329107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115972920325859018886071 30173959380488788528329107)
            ·
              refine ⟨45260939070733182792493661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30173959380488788528329107 45260939070733182792493661)
              ·
                refine ⟨16972852151524943547185123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45260939070733182792493661 16972852151524943547185123)
                ·
                  refine ⟨25459278227287415320777685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16972852151524943547185123 25459278227287415320777685)
                  ·
                    refine ⟨596701833452048796580727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25459278227287415320777685 596701833452048796580727)
                    ·
                      rfl

theorem cell23_3486218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_3486218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486218 prefixEnd_3486218 := by exact prefixLift 3486218
  have htrace : WordTrace (prefixWord ++ tailWord_3486218) baseStart_3486218 baseEnd_3486218 := by
    simpa [prefixWord, tailWord_3486218, baseEnd_3486218] using wordTrace_append hprefix tailTrace_3486218
  have hstable : (prefixWord ++ tailWord_3486218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486218).length < 2 ^ (prefixWord ++ tailWord_3486218).sum := by decide
  have hdescent : baseEnd_3486218 < baseStart_3486218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486222 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_3486222 : Nat := 118140960795 + 3486222 * 2 ^ 59
def prefixEnd_3486222 : Nat := 4983230072969 + 3 ^ 40 * 3486222 * 2
def baseEnd_3486222 : Nat := 198900839364307152676907

theorem tailTrace_3486222 : CollatzResearch.WordTrace tailWord_3486222 prefixEnd_3486222 198900839364307152676907 := by
  unfold tailWord_3486222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15894120297002571020068615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84768641584013712107032613 15894120297002571020068615)
  ·
    refine ⟨23841180445503856530102923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15894120297002571020068615 23841180445503856530102923)
    ·
      refine ⟨35761770668255784795154385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23841180445503856530102923 35761770668255784795154385)
      ·
        refine ⟨26821328001191838596365789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35761770668255784795154385 26821328001191838596365789)
        ·
          refine ⟨10057998000446939473637171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26821328001191838596365789 10057998000446939473637171)
          ·
            refine ⟨15086997000670409210455757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10057998000446939473637171 15086997000670409210455757)
            ·
              refine ⟨5657623875251403453920909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15086997000670409210455757 5657623875251403453920909)
              ·
                refine ⟨2121608953219276295220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5657623875251403453920909 2121608953219276295220341)
                ·
                  refine ⟨198900839364307152676907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2121608953219276295220341 198900839364307152676907)
                  ·
                    rfl

theorem cell23_3486222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_3486222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486222 prefixEnd_3486222 := by exact prefixLift 3486222
  have htrace : WordTrace (prefixWord ++ tailWord_3486222) baseStart_3486222 baseEnd_3486222 := by
    simpa [prefixWord, tailWord_3486222, baseEnd_3486222] using wordTrace_append hprefix tailTrace_3486222
  have hstable : (prefixWord ++ tailWord_3486222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486222).length < 2 ^ (prefixWord ++ tailWord_3486222).sum := by decide
  have hdescent : baseEnd_3486222 < baseStart_3486222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486265 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 5, 4]
def baseStart_3486265 : Nat := 118140960795 + 3486265 * 2 ^ 59
def prefixEnd_3486265 : Nat := 4983230072969 + 3 ^ 40 * 3486265 * 2
def baseEnd_3486265 : Nat := 596709877982302568618155

theorem tailTrace_3486265 : CollatzResearch.WordTrace tailWord_3486265 prefixEnd_3486265 596709877982302568618155 := by
  unfold tailWord_3486265
  simp only [CollatzResearch.WordTrace]
  refine ⟨127154530714864786504364249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84769687143243191002909499 127154530714864786504364249)
  ·
    refine ⟨95365898036148589878273187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127154530714864786504364249 95365898036148589878273187)
    ·
      refine ⟨143048847054222884817409781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95365898036148589878273187 143048847054222884817409781)
      ·
        refine ⟨13410829411333395451632167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143048847054222884817409781 13410829411333395451632167)
        ·
          refine ⟨20116244117000093177448251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410829411333395451632167 20116244117000093177448251)
          ·
            refine ⟨30174366175500139766172377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20116244117000093177448251 30174366175500139766172377)
            ·
              refine ⟨22630774631625104824629283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30174366175500139766172377 22630774631625104824629283)
              ·
                refine ⟨33946161947437657236943925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22630774631625104824629283 33946161947437657236943925)
                ·
                  refine ⟨3182452682572280365963493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33946161947437657236943925 3182452682572280365963493)
                  ·
                    refine ⟨596709877982302568618155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182452682572280365963493 596709877982302568618155)
                    ·
                      rfl

theorem cell23_3486265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_3486265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486265 prefixEnd_3486265 := by exact prefixLift 3486265
  have htrace : WordTrace (prefixWord ++ tailWord_3486265) baseStart_3486265 baseEnd_3486265 := by
    simpa [prefixWord, tailWord_3486265, baseEnd_3486265] using wordTrace_append hprefix tailTrace_3486265
  have hstable : (prefixWord ++ tailWord_3486265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486265).length < 2 ^ (prefixWord ++ tailWord_3486265).sum := by decide
  have hdescent : baseEnd_3486265 < baseStart_3486265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486292 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_3486292 : Nat := 118140960795 + 3486292 * 2 ^ 59
def prefixEnd_3486292 : Nat := 4983230072969 + 3 ^ 40 * 3486292 * 2
def baseEnd_3486292 : Nat := 1790143497924579100216841

theorem tailTrace_3486292 : CollatzResearch.WordTrace tailWord_3486292 prefixEnd_3486292 1790143497924579100216841 := by
  unfold tailWord_3486292
  simp only [CollatzResearch.WordTrace]
  refine ⟨63577757742883485057798565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84770343657177980077064753 63577757742883485057798565)
  ·
    refine ⟨11920829576790653448337231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63577757742883485057798565 11920829576790653448337231)
    ·
      refine ⟨17881244365185980172505847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11920829576790653448337231 17881244365185980172505847)
      ·
        refine ⟨26821866547778970258758771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17881244365185980172505847 26821866547778970258758771)
        ·
          refine ⟨40232799821668455388138157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26821866547778970258758771 40232799821668455388138157)
          ·
            refine ⟨15087299933125670770551809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40232799821668455388138157 15087299933125670770551809)
            ·
              refine ⟨11315474949844253077913857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15087299933125670770551809 11315474949844253077913857)
              ·
                refine ⟨8486606212383189808435393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11315474949844253077913857 8486606212383189808435393)
                ·
                  refine ⟨6364954659287392356326545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8486606212383189808435393 6364954659287392356326545)
                  ·
                    refine ⟨4773715994465544267244909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6364954659287392356326545 4773715994465544267244909)
                    ·
                      refine ⟨1790143497924579100216841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773715994465544267244909 1790143497924579100216841)
                      ·
                        rfl

theorem cell23_3486292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_3486292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486292 prefixEnd_3486292 := by exact prefixLift 3486292
  have htrace : WordTrace (prefixWord ++ tailWord_3486292) baseStart_3486292 baseEnd_3486292 := by
    simpa [prefixWord, tailWord_3486292, baseEnd_3486292] using wordTrace_append hprefix tailTrace_3486292
  have hstable : (prefixWord ++ tailWord_3486292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486292).length < 2 ^ (prefixWord ++ tailWord_3486292).sum := by decide
  have hdescent : baseEnd_3486292 < baseStart_3486292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486295 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 6]
def baseStart_3486295 : Nat := 118140960795 + 3486295 * 2 ^ 59
def prefixEnd_3486295 : Nat := 4983230072969 + 3 ^ 40 * 3486295 * 2
def baseEnd_3486295 : Nat := 198905004262949176497703

theorem tailTrace_3486295 : CollatzResearch.WordTrace tailWord_3486295 prefixEnd_3486295 198905004262949176497703 := by
  unfold tailWord_3486295
  simp only [CollatzResearch.WordTrace]
  refine ⟨127155624904756101627956339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84770416603170734418637559 127155624904756101627956339)
  ·
    refine ⟨190733437357134152441934509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127155624904756101627956339 190733437357134152441934509)
    ·
      refine ⟨71525039008925307165725441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190733437357134152441934509 71525039008925307165725441)
      ·
        refine ⟨53643779256693980374294081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71525039008925307165725441 53643779256693980374294081)
        ·
          refine ⟨40232834442520485280720561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53643779256693980374294081 40232834442520485280720561)
          ·
            refine ⟨30174625831890363960540421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40232834442520485280720561 30174625831890363960540421)
            ·
              refine ⟨5657742343479443242601329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30174625831890363960540421 5657742343479443242601329)
              ·
                refine ⟨4243306757609582431950997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657742343479443242601329 4243306757609582431950997)
                ·
                  refine ⟨198905004262949176497703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243306757609582431950997 198905004262949176497703)
                  ·
                    rfl

theorem cell23_3486295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 6].length) (baseStart_3486295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486295 prefixEnd_3486295 := by exact prefixLift 3486295
  have htrace : WordTrace (prefixWord ++ tailWord_3486295) baseStart_3486295 baseEnd_3486295 := by
    simpa [prefixWord, tailWord_3486295, baseEnd_3486295] using wordTrace_append hprefix tailTrace_3486295
  have hstable : (prefixWord ++ tailWord_3486295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486295).length < 2 ^ (prefixWord ++ tailWord_3486295).sum := by decide
  have hdescent : baseEnd_3486295 < baseStart_3486295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486306 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3486306 : Nat := 118140960795 + 3486306 * 2 ^ 59
def prefixEnd_3486306 : Nat := 4983230072969 + 3 ^ 40 * 3486306 * 2
def baseEnd_3486306 : Nat := 1790150686653742045441777

theorem tailTrace_3486306 : CollatzResearch.WordTrace tailWord_3486306 prefixEnd_3486306 1790150686653742045441777 := by
  unfold tailWord_3486306
  simp only [CollatzResearch.WordTrace]
  refine ⟨31789006526929062626651693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84770684071810833671071181 31789006526929062626651693)
  ·
    refine ⟨11920877447598398484994385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31789006526929062626651693 11920877447598398484994385)
    ·
      refine ⟨8940658085698798863745789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11920877447598398484994385 8940658085698798863745789)
      ·
        refine ⟨3352746782137049573904671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8940658085698798863745789 3352746782137049573904671)
        ·
          refine ⟨5029120173205574360857007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352746782137049573904671 5029120173205574360857007)
          ·
            refine ⟨7543680259808361541285511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029120173205574360857007 7543680259808361541285511)
            ·
              refine ⟨11315520389712542311928267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7543680259808361541285511 11315520389712542311928267)
              ·
                refine ⟨16973280584568813467892401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11315520389712542311928267 16973280584568813467892401)
                ·
                  refine ⟨12729960438426610100919301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16973280584568813467892401 12729960438426610100919301)
                  ·
                    refine ⟨2386867582204989393922369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12729960438426610100919301 2386867582204989393922369)
                    ·
                      refine ⟨1790150686653742045441777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386867582204989393922369 1790150686653742045441777)
                      ·
                        rfl

theorem cell23_3486306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3486306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486306 prefixEnd_3486306 := by exact prefixLift 3486306
  have htrace : WordTrace (prefixWord ++ tailWord_3486306) baseStart_3486306 baseEnd_3486306 := by
    simpa [prefixWord, tailWord_3486306, baseEnd_3486306] using wordTrace_append hprefix tailTrace_3486306
  have hstable : (prefixWord ++ tailWord_3486306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486306).length < 2 ^ (prefixWord ++ tailWord_3486306).sum := by decide
  have hdescent : baseEnd_3486306 < baseStart_3486306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486326 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3486326 : Nat := 118140960795 + 3486326 * 2 ^ 59
def prefixEnd_3486326 : Nat := 4983230072969 + 3 ^ 40 * 3486326 * 2
def baseEnd_3486326 : Nat := 1790160956266831967191685

theorem tailTrace_3486326 : CollatzResearch.WordTrace tailWord_3486326 prefixEnd_3486326 1790160956266831967191685 := by
  unfold tailWord_3486326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947297222977737120145927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84771170378429195948223221 7947297222977737120145927)
  ·
    refine ⟨11920945834466605680218891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7947297222977737120145927 11920945834466605680218891)
    ·
      refine ⟨17881418751699908520328337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11920945834466605680218891 17881418751699908520328337)
      ·
        refine ⟨13411064063774931390246253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17881418751699908520328337 13411064063774931390246253)
        ·
          refine ⟨5029149023915599271342345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13411064063774931390246253 5029149023915599271342345)
          ·
            refine ⟨3771861767936699453506759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029149023915599271342345 3771861767936699453506759)
            ·
              refine ⟨5657792651905049180260139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771861767936699453506759 5657792651905049180260139)
              ·
                refine ⟨8486688977857573770390209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657792651905049180260139 8486688977857573770390209)
                ·
                  refine ⟨6365016733393180327792657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8486688977857573770390209 6365016733393180327792657)
                  ·
                    refine ⟨4773762550044885245844493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6365016733393180327792657 4773762550044885245844493)
                    ·
                      refine ⟨1790160956266831967191685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773762550044885245844493 1790160956266831967191685)
                      ·
                        rfl

theorem cell23_3486326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3486326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486326 prefixEnd_3486326 := by exact prefixLift 3486326
  have htrace : WordTrace (prefixWord ++ tailWord_3486326) baseStart_3486326 baseEnd_3486326 := by
    simpa [prefixWord, tailWord_3486326, baseEnd_3486326] using wordTrace_append hprefix tailTrace_3486326
  have hstable : (prefixWord ++ tailWord_3486326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486326).length < 2 ^ (prefixWord ++ tailWord_3486326).sum := by decide
  have hdescent : baseEnd_3486326 < baseStart_3486326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486339 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 1, 1, 3]
def baseStart_3486339 : Nat := 118140960795 + 3486339 * 2 ^ 59
def prefixEnd_3486339 : Nat := 4983230072969 + 3 ^ 40 * 3486339 * 2
def baseEnd_3486339 : Nat := 1790167631515340416329125

theorem tailTrace_3486339 : CollatzResearch.WordTrace tailWord_3486339 prefixEnd_3486339 1790167631515340416329125 := by
  unfold tailWord_3486339
  simp only [CollatzResearch.WordTrace]
  refine ⟨127157229716596697142558071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84771486477731131428372047 127157229716596697142558071)
  ·
    refine ⟨190735844574895045713837107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127157229716596697142558071 190735844574895045713837107)
    ·
      refine ⟨286103766862342568570755661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190735844574895045713837107 286103766862342568570755661)
      ·
        refine ⟨107288912573378463214033373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286103766862342568570755661 107288912573378463214033373)
        ·
          refine ⟨40233342215016923705262515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107288912573378463214033373 40233342215016923705262515)
          ·
            refine ⟨60350013322525385557893773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40233342215016923705262515 60350013322525385557893773)
            ·
              refine ⟨22631254995947019584210165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60350013322525385557893773 22631254995947019584210165)
              ·
                refine ⟨2121680155870033086019703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22631254995947019584210165 2121680155870033086019703)
                ·
                  refine ⟨3182520233805049629029555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121680155870033086019703 3182520233805049629029555)
                  ·
                    refine ⟨4773780350707574443544333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182520233805049629029555 4773780350707574443544333)
                    ·
                      refine ⟨1790167631515340416329125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773780350707574443544333 1790167631515340416329125)
                      ·
                        rfl

theorem cell23_3486339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_3486339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486339 prefixEnd_3486339 := by exact prefixLift 3486339
  have htrace : WordTrace (prefixWord ++ tailWord_3486339) baseStart_3486339 baseEnd_3486339 := by
    simpa [prefixWord, tailWord_3486339, baseEnd_3486339] using wordTrace_append hprefix tailTrace_3486339
  have hstable : (prefixWord ++ tailWord_3486339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486339).length < 2 ^ (prefixWord ++ tailWord_3486339).sum := by decide
  have hdescent : baseEnd_3486339 < baseStart_3486339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486355 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 4, 4]
def baseStart_3486355 : Nat := 118140960795 + 3486355 * 2 ^ 59
def prefixEnd_3486355 : Nat := 4983230072969 + 3 ^ 40 * 3486355 * 2
def baseEnd_3486355 : Nat := 596725282401937451243017

theorem tailTrace_3486355 : CollatzResearch.WordTrace tailWord_3486355 prefixEnd_3486355 596725282401937451243017 := by
  unfold tailWord_3486355
  simp only [CollatzResearch.WordTrace]
  refine ⟨127157813284538731875140519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84771875523025821250093679 127157813284538731875140519)
  ·
    refine ⟨190736719926808097812710779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127157813284538731875140519 190736719926808097812710779)
    ·
      refine ⟨286105079890212146719066169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190736719926808097812710779 286105079890212146719066169)
      ·
        refine ⟨214578809917659110039299627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286105079890212146719066169 214578809917659110039299627)
        ·
          refine ⟨321868214876488665058949441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214578809917659110039299627 321868214876488665058949441)
          ·
            refine ⟨241401161157366498794212081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321868214876488665058949441 241401161157366498794212081)
            ·
              refine ⟨181050870868024874095659061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241401161157366498794212081 181050870868024874095659061)
              ·
                refine ⟨16973519143877331946468037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181050870868024874095659061 16973519143877331946468037)
                ·
                  refine ⟨3182534839476999739962757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16973519143877331946468037 3182534839476999739962757)
                  ·
                    refine ⟨596725282401937451243017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182534839476999739962757 596725282401937451243017)
                    ·
                      rfl

theorem cell23_3486355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 4].length) (baseStart_3486355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486355 prefixEnd_3486355 := by exact prefixLift 3486355
  have htrace : WordTrace (prefixWord ++ tailWord_3486355) baseStart_3486355 baseEnd_3486355 := by
    simpa [prefixWord, tailWord_3486355, baseEnd_3486355] using wordTrace_append hprefix tailTrace_3486355
  have hstable : (prefixWord ++ tailWord_3486355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486355).length < 2 ^ (prefixWord ++ tailWord_3486355).sum := by decide
  have hdescent : baseEnd_3486355 < baseStart_3486355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486356 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3486356 : Nat := 118140960795 + 3486356 * 2 ^ 59
def prefixEnd_3486356 : Nat := 4983230072969 + 3 ^ 40 * 3486356 * 2
def baseEnd_3486356 : Nat := 1790176360686466849816547

theorem tailTrace_3486356 : CollatzResearch.WordTrace tailWord_3486356 prefixEnd_3486356 1790176360686466849816547 := by
  unfold tailWord_3486356
  simp only [CollatzResearch.WordTrace]
  refine ⟨63578924878767554522963461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84771899838356739363951281 63578924878767554522963461)
  ·
    refine ⟨11921048414768916473055649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63578924878767554522963461 11921048414768916473055649)
    ·
      refine ⟨8940786311076687354791737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11921048414768916473055649 8940786311076687354791737)
      ·
        refine ⟨6705589733307515516093803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8940786311076687354791737 6705589733307515516093803)
        ·
          refine ⟨10058384599961273274140705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6705589733307515516093803 10058384599961273274140705)
          ·
            refine ⟨7543788449970954955605529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10058384599961273274140705 7543788449970954955605529)
            ·
              refine ⟨5657841337478216216704147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7543788449970954955605529 5657841337478216216704147)
              ·
                refine ⟨8486762006217324325056221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657841337478216216704147 8486762006217324325056221)
                ·
                  refine ⟨3182535752331496621896083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8486762006217324325056221 3182535752331496621896083)
                  ·
                    refine ⟨4773803628497244932844125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182535752331496621896083 4773803628497244932844125)
                    ·
                      refine ⟨1790176360686466849816547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773803628497244932844125 1790176360686466849816547)
                      ·
                        rfl

theorem cell23_3486356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3486356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486356 prefixEnd_3486356 := by exact prefixLift 3486356
  have htrace : WordTrace (prefixWord ++ tailWord_3486356) baseStart_3486356 baseEnd_3486356 := by
    simpa [prefixWord, tailWord_3486356, baseEnd_3486356] using wordTrace_append hprefix tailTrace_3486356
  have hstable : (prefixWord ++ tailWord_3486356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486356).length < 2 ^ (prefixWord ++ tailWord_3486356).sum := by decide
  have hdescent : baseEnd_3486356 < baseStart_3486356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486365 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3486365 : Nat := 118140960795 + 3486365 * 2 ^ 59
def prefixEnd_3486365 : Nat := 4983230072969 + 3 ^ 40 * 3486365 * 2
def baseEnd_3486365 : Nat := 1790180982012357314604005

theorem tailTrace_3486365 : CollatzResearch.WordTrace tailWord_3486365 prefixEnd_3486365 1790180982012357314604005 := by
  unfold tailWord_3486365
  simp only [CollatzResearch.WordTrace]
  refine ⟨127158178014502503583004549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84772118676335002388669699 127158178014502503583004549)
  ·
    refine ⟨23842158377719219421813353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127158178014502503583004549 23842158377719219421813353)
    ·
      refine ⟨17881618783289414566360015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23842158377719219421813353 17881618783289414566360015)
      ·
        refine ⟨26822428174934121849540023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17881618783289414566360015 26822428174934121849540023)
        ·
          refine ⟨40233642262401182774310035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26822428174934121849540023 40233642262401182774310035)
          ·
            refine ⟨60350463393601774161465053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40233642262401182774310035 60350463393601774161465053)
            ·
              refine ⟨22631423772600665310549395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60350463393601774161465053 22631423772600665310549395)
              ·
                refine ⟨33947135658900997965824093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22631423772600665310549395 33947135658900997965824093)
                ·
                  refine ⟨12730175872087874237184035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33947135658900997965824093 12730175872087874237184035)
                  ·
                    refine ⟨19095263808131811355776053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12730175872087874237184035 19095263808131811355776053)
                    ·
                      refine ⟨1790180982012357314604005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19095263808131811355776053 1790180982012357314604005)
                      ·
                        rfl

theorem cell23_3486365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3486365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486365 prefixEnd_3486365 := by exact prefixLift 3486365
  have htrace : WordTrace (prefixWord ++ tailWord_3486365) baseStart_3486365 baseEnd_3486365 := by
    simpa [prefixWord, tailWord_3486365, baseEnd_3486365] using wordTrace_append hprefix tailTrace_3486365
  have hstable : (prefixWord ++ tailWord_3486365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486365).length < 2 ^ (prefixWord ++ tailWord_3486365).sum := by decide
  have hdescent : baseEnd_3486365 < baseStart_3486365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486456 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 1, 3, 2]
def baseStart_3486456 : Nat := 118140960795 + 3486456 * 2 ^ 59
def prefixEnd_3486456 : Nat := 4983230072969 + 3 ^ 40 * 3486456 * 2
def baseEnd_3486456 : Nat := 1790227708751916458566087

theorem tailTrace_3486456 : CollatzResearch.WordTrace tailWord_3486456 prefixEnd_3486456 1790227708751916458566087 := by
  unfold tailWord_3486456
  simp only [CollatzResearch.WordTrace]
  refine ⟨63580748528586413062283611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84774331371448550749711481 63580748528586413062283611)
  ·
    refine ⟨95371122792879619593425417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63580748528586413062283611 95371122792879619593425417)
    ·
      refine ⟨71528342094659714695069063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95371122792879619593425417 71528342094659714695069063)
      ·
        refine ⟨107292513141989572042603595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71528342094659714695069063 107292513141989572042603595)
        ·
          refine ⟨160938769712984358063905393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107292513141989572042603595 160938769712984358063905393)
          ·
            refine ⟨120704077284738268547929045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160938769712984358063905393 120704077284738268547929045)
            ·
              refine ⟨2829001811361053169092087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 120704077284738268547929045 2829001811361053169092087)
              ·
                refine ⟨4243502717041579753638131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829001811361053169092087 4243502717041579753638131)
                ·
                  refine ⟨6365254075562369630457197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243502717041579753638131 6365254075562369630457197)
                  ·
                    refine ⟨2386970278335888611421449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6365254075562369630457197 2386970278335888611421449)
                    ·
                      refine ⟨1790227708751916458566087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386970278335888611421449 1790227708751916458566087)
                      ·
                        rfl

theorem cell23_3486456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_3486456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486456 prefixEnd_3486456 := by exact prefixLift 3486456
  have htrace : WordTrace (prefixWord ++ tailWord_3486456) baseStart_3486456 baseEnd_3486456 := by
    simpa [prefixWord, tailWord_3486456, baseEnd_3486456] using wordTrace_append hprefix tailTrace_3486456
  have hstable : (prefixWord ++ tailWord_3486456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486456).length < 2 ^ (prefixWord ++ tailWord_3486456).sum := by decide
  have hdescent : baseEnd_3486456 < baseStart_3486456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486465 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3486465 : Nat := 118140960795 + 3486465 * 2 ^ 59
def prefixEnd_3486465 : Nat := 4983230072969 + 3 ^ 40 * 3486465 * 2
def baseEnd_3486465 : Nat := 1790232330077806923353545

theorem tailTrace_3486465 : CollatzResearch.WordTrace tailWord_3486465 prefixEnd_3486465 1790232330077806923353545 := by
  unfold tailWord_3486465
  simp only [CollatzResearch.WordTrace]
  refine ⟨127161825314140220661644849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84774550209426813774429899 127161825314140220661644849)
  ·
    refine ⟨95371368985605165496233637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127161825314140220661644849 95371368985605165496233637)
    ·
      refine ⟨17882131684800968530543807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95371368985605165496233637 17882131684800968530543807)
      ·
        refine ⟨26823197527201452795815711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17882131684800968530543807 26823197527201452795815711)
        ·
          refine ⟨40234796290802179193723567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26823197527201452795815711 40234796290802179193723567)
          ·
            refine ⟨60352194436203268790585351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40234796290802179193723567 60352194436203268790585351)
            ·
              refine ⟨90528291654304903185878027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60352194436203268790585351 90528291654304903185878027)
              ·
                refine ⟨135792437481457354778817041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90528291654304903185878027 135792437481457354778817041)
                ·
                  refine ⟨101844328111093016084112781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135792437481457354778817041 101844328111093016084112781)
                  ·
                    refine ⟨38191623041659881031542293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101844328111093016084112781 38191623041659881031542293)
                    ·
                      refine ⟨1790232330077806923353545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38191623041659881031542293 1790232330077806923353545)
                      ·
                        rfl

theorem cell23_3486465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3486465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486465 prefixEnd_3486465 := by exact prefixLift 3486465
  have htrace : WordTrace (prefixWord ++ tailWord_3486465) baseStart_3486465 baseEnd_3486465 := by
    simpa [prefixWord, tailWord_3486465, baseEnd_3486465] using wordTrace_append hprefix tailTrace_3486465
  have hstable : (prefixWord ++ tailWord_3486465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486465).length < 2 ^ (prefixWord ++ tailWord_3486465).sum := by decide
  have hdescent : baseEnd_3486465 < baseStart_3486465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486469 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 4, 2, 2]
def baseStart_3486469 : Nat := 118140960795 + 3486469 * 2 ^ 59
def prefixEnd_3486469 : Nat := 4983230072969 + 3 ^ 40 * 3486469 * 2
def baseEnd_3486469 : Nat := 1790234384000424907703527

theorem tailTrace_3486469 : CollatzResearch.WordTrace tailWord_3486469 prefixEnd_3486469 1790234384000424907703527 := by
  unfold tailWord_3486469
  simp only [CollatzResearch.WordTrace]
  refine ⟨127161971206125729344790461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84774647470750486229860307 127161971206125729344790461)
  ·
    refine ⟨47685739202297148504296423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127161971206125729344790461 47685739202297148504296423)
    ·
      refine ⟨71528608803445722756444635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47685739202297148504296423 71528608803445722756444635)
      ·
        refine ⟨107292913205168584134666953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71528608803445722756444635 107292913205168584134666953)
        ·
          refine ⟨80469684903876438101000215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107292913205168584134666953 80469684903876438101000215)
          ·
            refine ⟨120704527355814657151500323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80469684903876438101000215 120704527355814657151500323)
            ·
              refine ⟨181056791033721985727250485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120704527355814657151500323 181056791033721985727250485)
              ·
                refine ⟨16974074159411436161929733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181056791033721985727250485 16974074159411436161929733)
                ·
                  refine ⟨3182638904889644280361825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16974074159411436161929733 3182638904889644280361825)
                  ·
                    refine ⟨2386979178667233210271369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3182638904889644280361825 2386979178667233210271369)
                    ·
                      refine ⟨1790234384000424907703527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2386979178667233210271369 1790234384000424907703527)
                      ·
                        rfl

theorem cell23_3486469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_3486469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486469 prefixEnd_3486469 := by exact prefixLift 3486469
  have htrace : WordTrace (prefixWord ++ tailWord_3486469) baseStart_3486469 baseEnd_3486469 := by
    simpa [prefixWord, tailWord_3486469, baseEnd_3486469] using wordTrace_append hprefix tailTrace_3486469
  have hstable : (prefixWord ++ tailWord_3486469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486469).length < 2 ^ (prefixWord ++ tailWord_3486469).sum := by decide
  have hdescent : baseEnd_3486469 < baseStart_3486469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486472 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3486472 : Nat := 118140960795 + 3486472 * 2 ^ 59
def prefixEnd_3486472 : Nat := 4983230072969 + 3 ^ 40 * 3486472 * 2
def baseEnd_3486472 : Nat := 1790235924442388395966013

theorem tailTrace_3486472 : CollatzResearch.WordTrace tailWord_3486472 prefixEnd_3486472 1790235924442388395966013 := by
  unfold tailWord_3486472
  simp only [CollatzResearch.WordTrace]
  refine ⟨63581040312557430428574835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84774720416743240571433113 63581040312557430428574835)
  ·
    refine ⟨95371560468836145642862253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63581040312557430428574835 95371560468836145642862253)
    ·
      refine ⟨35764335175813554616073345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95371560468836145642862253 35764335175813554616073345)
      ·
        refine ⟨26823251381860165962055009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35764335175813554616073345 26823251381860165962055009)
        ·
          refine ⟨20117438536395124471541257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26823251381860165962055009 20117438536395124471541257)
          ·
            refine ⟨15088078902296343353655943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20117438536395124471541257 15088078902296343353655943)
            ·
              refine ⟨22632118353444515030483915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15088078902296343353655943 22632118353444515030483915)
              ·
                refine ⟨33948177530166772545725873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22632118353444515030483915 33948177530166772545725873)
                ·
                  refine ⟨25461133147625079409294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33948177530166772545725873 25461133147625079409294405)
                  ·
                    refine ⟨4773962465179702389242701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25461133147625079409294405 4773962465179702389242701)
                    ·
                      refine ⟨1790235924442388395966013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4773962465179702389242701 1790235924442388395966013)
                      ·
                        rfl

theorem cell23_3486472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3486472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486472 prefixEnd_3486472 := by exact prefixLift 3486472
  have htrace : WordTrace (prefixWord ++ tailWord_3486472) baseStart_3486472 baseEnd_3486472 := by
    simpa [prefixWord, tailWord_3486472, baseEnd_3486472] using wordTrace_append hprefix tailTrace_3486472
  have hstable : (prefixWord ++ tailWord_3486472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486472).length < 2 ^ (prefixWord ++ tailWord_3486472).sum := by decide
  have hdescent : baseEnd_3486472 < baseStart_3486472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486475 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 7]
def baseStart_3486475 : Nat := 118140960795 + 3486475 * 2 ^ 59
def prefixEnd_3486475 : Nat := 4983230072969 + 3 ^ 40 * 3486475 * 2
def baseEnd_3486475 : Nat := 198915273876039098247611

theorem tailTrace_3486475 : CollatzResearch.WordTrace tailWord_3486475 prefixEnd_3486475 198915273876039098247611 := by
  unfold tailWord_3486475
  simp only [CollatzResearch.WordTrace]
  refine ⟨127162190044103992369508879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84774793362735994913005919 127162190044103992369508879)
  ·
    refine ⟨190743285066155988554263319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127162190044103992369508879 190743285066155988554263319)
    ·
      refine ⟨286114927599233982831394979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190743285066155988554263319 286114927599233982831394979)
      ·
        refine ⟨429172391398850974247092469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286114927599233982831394979 429172391398850974247092469)
        ·
          refine ⟨40234911693642278835664919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 429172391398850974247092469 40234911693642278835664919)
          ·
            refine ⟨60352367540463418253497379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40234911693642278835664919 60352367540463418253497379)
            ·
              refine ⟨90528551310695127380246069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60352367540463418253497379 90528551310695127380246069)
              ·
                refine ⟨8487051685377668191898069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90528551310695127380246069 8487051685377668191898069)
                ·
                  refine ⟨198915273876039098247611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8487051685377668191898069 198915273876039098247611)
                  ·
                    rfl

theorem cell23_3486475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 7].length) (baseStart_3486475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486475 prefixEnd_3486475 := by exact prefixLift 3486475
  have htrace : WordTrace (prefixWord ++ tailWord_3486475) baseStart_3486475 baseEnd_3486475 := by
    simpa [prefixWord, tailWord_3486475, baseEnd_3486475] using wordTrace_append hprefix tailTrace_3486475
  have hstable : (prefixWord ++ tailWord_3486475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486475).length < 2 ^ (prefixWord ++ tailWord_3486475).sum := by decide
  have hdescent : baseEnd_3486475 < baseStart_3486475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486492 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 7]
def baseStart_3486492 : Nat := 118140960795 + 3486492 * 2 ^ 59
def prefixEnd_3486492 : Nat := 4983230072969 + 3 ^ 40 * 3486492 * 2
def baseEnd_3486492 : Nat := 198916243783942035301769

theorem tailTrace_3486492 : CollatzResearch.WordTrace tailWord_3486492 prefixEnd_3486492 198916243783942035301769 := by
  unfold tailWord_3486492
  simp only [CollatzResearch.WordTrace]
  refine ⟨63581405042521202136438865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84775206723361602848585153 63581405042521202136438865)
  ·
    refine ⟨47686053781890901602329149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63581405042521202136438865 47686053781890901602329149)
    ·
      refine ⟨17882270168209088100873431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47686053781890901602329149 17882270168209088100873431)
      ·
        refine ⟨26823405252313632151310147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17882270168209088100873431 26823405252313632151310147)
        ·
          refine ⟨40235107878470448226965221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26823405252313632151310147 40235107878470448226965221)
          ·
            refine ⟨7544082727213209042555979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40235107878470448226965221 7544082727213209042555979)
            ·
              refine ⟨11316124090819813563833969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544082727213209042555979 11316124090819813563833969)
              ·
                refine ⟨8487093068114860172875477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11316124090819813563833969 8487093068114860172875477)
                ·
                  refine ⟨198916243783942035301769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8487093068114860172875477 198916243783942035301769)
                  ·
                    rfl

theorem cell23_3486492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_3486492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486492 prefixEnd_3486492 := by exact prefixLift 3486492
  have htrace : WordTrace (prefixWord ++ tailWord_3486492) baseStart_3486492 baseEnd_3486492 := by
    simpa [prefixWord, tailWord_3486492, baseEnd_3486492] using wordTrace_append hprefix tailTrace_3486492
  have hstable : (prefixWord ++ tailWord_3486492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486492).length < 2 ^ (prefixWord ++ tailWord_3486492).sum := by decide
  have hdescent : baseEnd_3486492 < baseStart_3486492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486505 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_3486505 : Nat := 118140960795 + 3486505 * 2 ^ 59
def prefixEnd_3486505 : Nat := 4983230072969 + 3 ^ 40 * 3486505 * 2
def baseEnd_3486505 : Nat := 596750956434662255617787

theorem tailTrace_3486505 : CollatzResearch.WordTrace tailWord_3486505 prefixEnd_3486505 596750956434662255617787 := by
  unfold tailWord_3486505
  simp only [CollatzResearch.WordTrace]
  refine ⟨127163284233995307493100969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84775522822663538328733979 127163284233995307493100969)
  ·
    refine ⟨95372463175496480619825727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127163284233995307493100969 95372463175496480619825727)
    ·
      refine ⟨143058694763244720929738591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95372463175496480619825727 143058694763244720929738591)
      ·
        refine ⟨214588042144867081394607887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143058694763244720929738591 214588042144867081394607887)
        ·
          refine ⟨321882063217300622091911831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214588042144867081394607887 321882063217300622091911831)
          ·
            refine ⟨482823094825950933137867747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321882063217300622091911831 482823094825950933137867747)
            ·
              refine ⟨724234642238926399706801621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482823094825950933137867747 724234642238926399706801621)
              ·
                refine ⟨16974249427474837493128163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 724234642238926399706801621 16974249427474837493128163)
                ·
                  refine ⟨25461374141212256239692245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16974249427474837493128163 25461374141212256239692245)
                  ·
                    refine ⟨596750956434662255617787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25461374141212256239692245 596750956434662255617787)
                    ·
                      rfl

theorem cell23_3486505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_3486505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486505 prefixEnd_3486505 := by exact prefixLift 3486505
  have htrace : WordTrace (prefixWord ++ tailWord_3486505) baseStart_3486505 baseEnd_3486505 := by
    simpa [prefixWord, tailWord_3486505, baseEnd_3486505] using wordTrace_append hprefix tailTrace_3486505
  have hstable : (prefixWord ++ tailWord_3486505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486505).length < 2 ^ (prefixWord ++ tailWord_3486505).sum := by decide
  have hdescent : baseEnd_3486505 < baseStart_3486505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486592 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_3486592 : Nat := 118140960795 + 3486592 * 2 ^ 59
def prefixEnd_3486592 : Nat := 4983230072969 + 3 ^ 40 * 3486592 * 2
def baseEnd_3486592 : Nat := 1790297542120927926465461

theorem tailTrace_3486592 : CollatzResearch.WordTrace tailWord_3486592 prefixEnd_3486592 1790297542120927926465461 := by
  unfold tailWord_3486592
  simp only [CollatzResearch.WordTrace]
  refine ⟨63583228692340060675759015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84777638256453414234345353 63583228692340060675759015)
  ·
    refine ⟨95374843038510091013638523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63583228692340060675759015 95374843038510091013638523)
    ·
      refine ⟨143062264557765136520457785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95374843038510091013638523 143062264557765136520457785)
      ·
        refine ⟨107296698418323852390343339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143062264557765136520457785 107296698418323852390343339)
        ·
          refine ⟨160945047627485778585515009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107296698418323852390343339 160945047627485778585515009)
          ·
            refine ⟨120708785720614333939136257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160945047627485778585515009 120708785720614333939136257)
            ·
              refine ⟨90531589290460750454352193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120708785720614333939136257 90531589290460750454352193)
              ·
                refine ⟨67898691967845562840764145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90531589290460750454352193 67898691967845562840764145)
                ·
                  refine ⟨50924018975884172130573109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67898691967845562840764145 50924018975884172130573109)
                  ·
                    refine ⟨4774126778989141137241229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50924018975884172130573109 4774126778989141137241229)
                    ·
                      refine ⟨1790297542120927926465461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4774126778989141137241229 1790297542120927926465461)
                      ·
                        rfl

theorem cell23_3486592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_3486592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486592 prefixEnd_3486592 := by exact prefixLift 3486592
  have htrace : WordTrace (prefixWord ++ tailWord_3486592) baseStart_3486592 baseEnd_3486592 := by
    simpa [prefixWord, tailWord_3486592, baseEnd_3486592] using wordTrace_append hprefix tailTrace_3486592
  have hstable : (prefixWord ++ tailWord_3486592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486592).length < 2 ^ (prefixWord ++ tailWord_3486592).sum := by decide
  have hdescent : baseEnd_3486592 < baseStart_3486592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486599 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 6]
def baseStart_3486599 : Nat := 118140960795 + 3486599 * 2 ^ 59
def prefixEnd_3486599 : Nat := 4983230072969 + 3 ^ 40 * 3486599 * 2
def baseEnd_3486599 : Nat := 198922348498389933230881

theorem tailTrace_3486599 : CollatzResearch.WordTrace tailWord_3486599 prefixEnd_3486599 198922348498389933230881 := by
  unfold tailWord_3486599
  simp only [CollatzResearch.WordTrace]
  refine ⟨127166712695654761547022851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84777808463769841031348567 127166712695654761547022851)
  ·
    refine ⟨190750069043482142320534277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127166712695654761547022851 190750069043482142320534277)
    ·
      refine ⟨35765637945652901685100177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190750069043482142320534277 35765637945652901685100177)
      ·
        refine ⟨26824228459239676263825133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35765637945652901685100177 26824228459239676263825133)
        ·
          refine ⟨10059085672214878598934425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26824228459239676263825133 10059085672214878598934425)
          ·
            refine ⟨7544314254161158949200819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10059085672214878598934425 7544314254161158949200819)
            ·
              refine ⟨11316471381241738423801229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544314254161158949200819 11316471381241738423801229)
              ·
                refine ⟨4243676767965651908925461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11316471381241738423801229 4243676767965651908925461)
                ·
                  refine ⟨198922348498389933230881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243676767965651908925461 198922348498389933230881)
                  ·
                    rfl

theorem cell23_3486599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 6].length) (baseStart_3486599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486599 prefixEnd_3486599 := by exact prefixLift 3486599
  have htrace : WordTrace (prefixWord ++ tailWord_3486599) baseStart_3486599 baseEnd_3486599 := by
    simpa [prefixWord, tailWord_3486599, baseEnd_3486599] using wordTrace_append hprefix tailTrace_3486599
  have hstable : (prefixWord ++ tailWord_3486599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486599).length < 2 ^ (prefixWord ++ tailWord_3486599).sum := by decide
  have hdescent : baseEnd_3486599 < baseStart_3486599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486609 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_3486609 : Nat := 118140960795 + 3486609 * 2 ^ 59
def prefixEnd_3486609 : Nat := 4983230072969 + 3 ^ 40 * 3486609 * 2
def baseEnd_3486609 : Nat := 1790306271292054359952883

theorem tailTrace_3486609 : CollatzResearch.WordTrace tailWord_3486609 prefixEnd_3486609 1790306271292054359952883 := by
  unfold tailWord_3486609
  simp only [CollatzResearch.WordTrace]
  refine ⟨127167077425618533254886881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84778051617079022169924587 127167077425618533254886881)
  ·
    refine ⟨95375308069213899941165161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127167077425618533254886881 95375308069213899941165161)
    ·
      refine ⟨71531481051910424955873871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95375308069213899941165161 71531481051910424955873871)
      ·
        refine ⟨107297221577865637433810807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71531481051910424955873871 107297221577865637433810807)
        ·
          refine ⟨160945832366798456150716211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107297221577865637433810807 160945832366798456150716211)
          ·
            refine ⟨241418748550197684226074317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160945832366798456150716211 241418748550197684226074317)
            ·
              refine ⟨90532030706324131584777869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241418748550197684226074317 90532030706324131584777869)
              ·
                refine ⟨33949511514871549344291701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90532030706324131584777869 33949511514871549344291701)
                ·
                  refine ⟨3182766704519207751027347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33949511514871549344291701 3182766704519207751027347)
                  ·
                    refine ⟨4774150056778811626541021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182766704519207751027347 4774150056778811626541021)
                    ·
                      refine ⟨1790306271292054359952883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4774150056778811626541021 1790306271292054359952883)
                      ·
                        rfl

theorem cell23_3486609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_3486609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486609 prefixEnd_3486609 := by exact prefixLift 3486609
  have htrace : WordTrace (prefixWord ++ tailWord_3486609) baseStart_3486609 baseEnd_3486609 := by
    simpa [prefixWord, tailWord_3486609, baseEnd_3486609] using wordTrace_append hprefix tailTrace_3486609
  have hstable : (prefixWord ++ tailWord_3486609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486609).length < 2 ^ (prefixWord ++ tailWord_3486609).sum := by decide
  have hdescent : baseEnd_3486609 < baseStart_3486609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486649 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3486649 : Nat := 118140960795 + 3486649 * 2 ^ 59
def prefixEnd_3486649 : Nat := 4983230072969 + 3 ^ 40 * 3486649 * 2
def baseEnd_3486649 : Nat := 1790326810518234203452699

theorem tailTrace_3486649 : CollatzResearch.WordTrace tailWord_3486649 prefixEnd_3486649 1790326810518234203452699 := by
  unfold tailWord_3486649
  simp only [CollatzResearch.WordTrace]
  refine ⟨127168536345473620086343001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84779024230315746724228667 127168536345473620086343001)
  ·
    refine ⟨95376402259105215064757251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127168536345473620086343001 95376402259105215064757251)
    ·
      refine ⟨143064603388657822597135877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95376402259105215064757251 143064603388657822597135877)
      ·
        refine ⟨26824613135373341736962977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143064603388657822597135877 26824613135373341736962977)
        ·
          refine ⟨20118459851530006302722233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26824613135373341736962977 20118459851530006302722233)
          ·
            refine ⟨15088844888647504727041675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20118459851530006302722233 15088844888647504727041675)
            ·
              refine ⟨22633267332971257090562513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15088844888647504727041675 22633267332971257090562513)
              ·
                refine ⟨16974950499728442817921885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22633267332971257090562513 16974950499728442817921885)
                ·
                  refine ⟨6365606437398166056720707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16974950499728442817921885 6365606437398166056720707)
                  ·
                    refine ⟨9548409656097249085081061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6365606437398166056720707 9548409656097249085081061)
                    ·
                      refine ⟨1790326810518234203452699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9548409656097249085081061 1790326810518234203452699)
                      ·
                        rfl

theorem cell23_3486649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3486649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486649 prefixEnd_3486649 := by exact prefixLift 3486649
  have htrace : WordTrace (prefixWord ++ tailWord_3486649) baseStart_3486649 baseEnd_3486649 := by
    simpa [prefixWord, tailWord_3486649, baseEnd_3486649] using wordTrace_append hprefix tailTrace_3486649
  have hstable : (prefixWord ++ tailWord_3486649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486649).length < 2 ^ (prefixWord ++ tailWord_3486649).sum := by decide
  have hdescent : baseEnd_3486649 < baseStart_3486649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486660 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3486660 : Nat := 118140960795 + 3486660 * 2 ^ 59
def prefixEnd_3486660 : Nat := 4983230072969 + 3 ^ 40 * 3486660 * 2
def baseEnd_3486660 : Nat := 1790332458805433660415149

theorem tailTrace_3486660 : CollatzResearch.WordTrace tailWord_3486660 prefixEnd_3486660 1790332458805433660415149 := by
  unfold tailWord_3486660
  simp only [CollatzResearch.WordTrace]
  refine ⟨63584468774216884482496717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84779291698955845976662289 63584468774216884482496717)
  ·
    refine ⟨23844175790331331680936269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63584468774216884482496717 23844175790331331680936269)
    ·
      refine ⟨8941565921374249380351101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23844175790331331680936269 8941565921374249380351101)
      ·
        refine ⟨3353087220515343517631663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8941565921374249380351101 3353087220515343517631663)
        ·
          refine ⟨5029630830773015276447495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353087220515343517631663 5029630830773015276447495)
          ·
            refine ⟨7544446246159522914671243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029630830773015276447495 7544446246159522914671243)
            ·
              refine ⟨11316669369239284372006865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544446246159522914671243 11316669369239284372006865)
              ·
                refine ⟨8487502026929463279005149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11316669369239284372006865 8487502026929463279005149)
                ·
                  refine ⟨3182813260098548729626931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8487502026929463279005149 3182813260098548729626931)
                  ·
                    refine ⟨4774219890147823094440397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182813260098548729626931 4774219890147823094440397)
                    ·
                      refine ⟨1790332458805433660415149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4774219890147823094440397 1790332458805433660415149)
                      ·
                        rfl

theorem cell23_3486660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3486660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486660 prefixEnd_3486660 := by exact prefixLift 3486660
  have htrace : WordTrace (prefixWord ++ tailWord_3486660) baseStart_3486660 baseEnd_3486660 := by
    simpa [prefixWord, tailWord_3486660, baseEnd_3486660] using wordTrace_append hprefix tailTrace_3486660
  have hstable : (prefixWord ++ tailWord_3486660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486660).length < 2 ^ (prefixWord ++ tailWord_3486660).sum := by decide
  have hdescent : baseEnd_3486660 < baseStart_3486660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486693 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_3486693 : Nat := 118140960795 + 3486693 * 2 ^ 59
def prefixEnd_3486693 : Nat := 4983230072969 + 3 ^ 40 * 3486693 * 2
def baseEnd_3486693 : Nat := 596783134555677343767499

theorem tailTrace_3486693 : CollatzResearch.WordTrace tailWord_3486693 prefixEnd_3486693 596783134555677343767499 := by
  unfold tailWord_3486693
  simp only [CollatzResearch.WordTrace]
  refine ⟨127170141157314215600944733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84780094104876143733963155 127170141157314215600944733)
  ·
    refine ⟨47688802933992830850354275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127170141157314215600944733 47688802933992830850354275)
    ·
      refine ⟨71533204400989246275531413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47688802933992830850354275 71533204400989246275531413)
      ·
        refine ⟨3353118956296370919165535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71533204400989246275531413 3353118956296370919165535)
        ·
          refine ⟨5029678434444556378748303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353118956296370919165535 5029678434444556378748303)
          ·
            refine ⟨7544517651666834568122455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029678434444556378748303 7544517651666834568122455)
            ·
              refine ⟨11316776477500251852183683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544517651666834568122455 11316776477500251852183683)
              ·
                refine ⟨16975164716250377778275525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11316776477500251852183683 16975164716250377778275525)
                ·
                  refine ⟨3182843384296945833426661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16975164716250377778275525 3182843384296945833426661)
                  ·
                    refine ⟨596783134555677343767499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182843384296945833426661 596783134555677343767499)
                    ·
                      rfl

theorem cell23_3486693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_3486693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486693 prefixEnd_3486693 := by exact prefixLift 3486693
  have htrace : WordTrace (prefixWord ++ tailWord_3486693) baseStart_3486693 baseEnd_3486693 := by
    simpa [prefixWord, tailWord_3486693, baseEnd_3486693] using wordTrace_append hprefix tailTrace_3486693
  have hstable : (prefixWord ++ tailWord_3486693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486693).length < 2 ^ (prefixWord ++ tailWord_3486693).sum := by decide
  have hdescent : baseEnd_3486693 < baseStart_3486693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486710 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_3486710 : Nat := 118140960795 + 3486710 * 2 ^ 59
def prefixEnd_3486710 : Nat := 4983230072969 + 3 ^ 40 * 3486710 * 2
def baseEnd_3486710 : Nat := 596786044279386154929973

theorem tailTrace_3486710 : CollatzResearch.WordTrace tailWord_3486710 prefixEnd_3486710 596786044279386154929973 := by
  unfold tailWord_3486710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948172574890789219019599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84780507465501751669542389 7948172574890789219019599)
  ·
    refine ⟨11922258862336183828529399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7948172574890789219019599 11922258862336183828529399)
    ·
      refine ⟨17883388293504275742794099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11922258862336183828529399 17883388293504275742794099)
      ·
        refine ⟨26825082440256413614191149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17883388293504275742794099 26825082440256413614191149)
        ·
          refine ⟨10059405915096155105321681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26825082440256413614191149 10059405915096155105321681)
          ·
            refine ⟨7544554436322116328991261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10059405915096155105321681 7544554436322116328991261)
            ·
              refine ⟨2829207913620793623371723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7544554436322116328991261 2829207913620793623371723)
              ·
                refine ⟨4243811870431190435057585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829207913620793623371723 4243811870431190435057585)
                ·
                  refine ⟨3182858902823392826293189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4243811870431190435057585 3182858902823392826293189)
                  ·
                    refine ⟨596786044279386154929973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182858902823392826293189 596786044279386154929973)
                    ·
                      rfl

theorem cell23_3486710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_3486710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486710 prefixEnd_3486710 := by exact prefixLift 3486710
  have htrace : WordTrace (prefixWord ++ tailWord_3486710) baseStart_3486710 baseEnd_3486710 := by
    simpa [prefixWord, tailWord_3486710, baseEnd_3486710] using wordTrace_append hprefix tailTrace_3486710
  have hstable : (prefixWord ++ tailWord_3486710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486710).length < 2 ^ (prefixWord ++ tailWord_3486710).sum := by decide
  have hdescent : baseEnd_3486710 < baseStart_3486710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486716 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_3486716 : Nat := 118140960795 + 3486716 * 2 ^ 59
def prefixEnd_3486716 : Nat := 4983230072969 + 3 ^ 40 * 3486716 * 2
def baseEnd_3486716 : Nat := 1790361213722085441314891

theorem tailTrace_3486716 : CollatzResearch.WordTrace tailWord_3486716 prefixEnd_3486716 1790361213722085441314891 := by
  unfold tailWord_3486716
  simp only [CollatzResearch.WordTrace]
  refine ⟨63585490018115445264516001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84780653357487260352688001 63585490018115445264516001)
  ·
    refine ⟨47689117513586583948387001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63585490018115445264516001 47689117513586583948387001)
    ·
      refine ⟨35766838135189937961290251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47689117513586583948387001 35766838135189937961290251)
      ·
        refine ⟨53650257202784906941935377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35766838135189937961290251 53650257202784906941935377)
        ·
          refine ⟨40237692902088680206451533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53650257202784906941935377 40237692902088680206451533)
          ·
            refine ⟨15089134838283255077419325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40237692902088680206451533 15089134838283255077419325)
            ·
              refine ⟨5658425564356220654032247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15089134838283255077419325 5658425564356220654032247)
              ·
                refine ⟨8487638346534330981048371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658425564356220654032247 8487638346534330981048371)
                ·
                  refine ⟨12731457519801496471572557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8487638346534330981048371 12731457519801496471572557)
                  ·
                    refine ⟨4774296569925561176839709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12731457519801496471572557 4774296569925561176839709)
                    ·
                      refine ⟨1790361213722085441314891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4774296569925561176839709 1790361213722085441314891)
                      ·
                        rfl

theorem cell23_3486716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_3486716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486716 prefixEnd_3486716 := by exact prefixLift 3486716
  have htrace : WordTrace (prefixWord ++ tailWord_3486716) baseStart_3486716 baseEnd_3486716 := by
    simpa [prefixWord, tailWord_3486716, baseEnd_3486716] using wordTrace_append hprefix tailTrace_3486716
  have hstable : (prefixWord ++ tailWord_3486716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486716).length < 2 ^ (prefixWord ++ tailWord_3486716).sum := by decide
  have hdescent : baseEnd_3486716 < baseStart_3486716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486769 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3486769 : Nat := 118140960795 + 3486769 * 2 ^ 59
def prefixEnd_3486769 : Nat := 4983230072969 + 3 ^ 40 * 3486769 * 2
def baseEnd_3486769 : Nat := 1790388428196773733952147

theorem tailTrace_3486769 : CollatzResearch.WordTrace tailWord_3486769 prefixEnd_3486769 1790388428196773733952147 := by
  unfold tailWord_3486769
  simp only [CollatzResearch.WordTrace]
  refine ⟨127172913105038880580711361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84781942070025920387140907 127172913105038880580711361)
  ·
    refine ⟨95379684828779160435533521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127172913105038880580711361 95379684828779160435533521)
    ·
      refine ⟨71534763621584370326650141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95379684828779160435533521 71534763621584370326650141)
      ·
        refine ⟨26825536358094138872493803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71534763621584370326650141 26825536358094138872493803)
        ·
          refine ⟨40238304537141208308740705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26825536358094138872493803 40238304537141208308740705)
          ·
            refine ⟨30178728402855906231555529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40238304537141208308740705 30178728402855906231555529)
            ·
              refine ⟨22634046302141929673666647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30178728402855906231555529 22634046302141929673666647)
              ·
                refine ⟨33951069453212894510499971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22634046302141929673666647 33951069453212894510499971)
                ·
                  refine ⟨50926604179819341765749957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33951069453212894510499971 50926604179819341765749957)
                  ·
                    refine ⟨9548738283716126581078117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50926604179819341765749957 9548738283716126581078117)
                    ·
                      refine ⟨1790388428196773733952147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9548738283716126581078117 1790388428196773733952147)
                      ·
                        rfl

theorem cell23_3486769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3486769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486769 prefixEnd_3486769 := by exact prefixLift 3486769
  have htrace : WordTrace (prefixWord ++ tailWord_3486769) baseStart_3486769 baseEnd_3486769 := by
    simpa [prefixWord, tailWord_3486769, baseEnd_3486769] using wordTrace_append hprefix tailTrace_3486769
  have hstable : (prefixWord ++ tailWord_3486769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486769).length < 2 ^ (prefixWord ++ tailWord_3486769).sum := by decide
  have hdescent : baseEnd_3486769 < baseStart_3486769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486790 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3486790 : Nat := 118140960795 + 3486790 * 2 ^ 59
def prefixEnd_3486790 : Nat := 4983230072969 + 3 ^ 40 * 3486790 * 2
def baseEnd_3486790 : Nat := 1790399211290518151789551

theorem tailTrace_3486790 : CollatzResearch.WordTrace tailWord_3486790 prefixEnd_3486790 1790399211290518151789551 := by
  unfold tailWord_3486790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974177469936337536475807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84782452691975200778150549 3974177469936337536475807)
  ·
    refine ⟨5961266204904506304713711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3974177469936337536475807 5961266204904506304713711)
    ·
      refine ⟨8941899307356759457070567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5961266204904506304713711 8941899307356759457070567)
      ·
        refine ⟨13412848961035139185605851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8941899307356759457070567 13412848961035139185605851)
        ·
          refine ⟨20119273441552708778408777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412848961035139185605851 20119273441552708778408777)
          ·
            refine ⟨15089455081164531583806583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20119273441552708778408777 15089455081164531583806583)
            ·
              refine ⟨22634182621746797375709875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15089455081164531583806583 22634182621746797375709875)
              ·
                refine ⟨33951273932620196063564813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22634182621746797375709875 33951273932620196063564813)
                ·
                  refine ⟨12731727724732573523836805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33951273932620196063564813 12731727724732573523836805)
                  ·
                    refine ⟨2387198948387357535719401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12731727724732573523836805 2387198948387357535719401)
                    ·
                      refine ⟨1790399211290518151789551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387198948387357535719401 1790399211290518151789551)
                      ·
                        rfl

theorem cell23_3486790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3486790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486790 prefixEnd_3486790 := by exact prefixLift 3486790
  have htrace : WordTrace (prefixWord ++ tailWord_3486790) baseStart_3486790 baseEnd_3486790 := by
    simpa [prefixWord, tailWord_3486790, baseEnd_3486790] using wordTrace_append hprefix tailTrace_3486790
  have hstable : (prefixWord ++ tailWord_3486790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486790).length < 2 ^ (prefixWord ++ tailWord_3486790).sum := by decide
  have hdescent : baseEnd_3486790 < baseStart_3486790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486796 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 5]
def baseStart_3486796 : Nat := 118140960795 + 3486796 * 2 ^ 59
def prefixEnd_3486796 : Nat := 4983230072969 + 3 ^ 40 * 3486796 * 2
def baseEnd_3486796 : Nat := 198933588019382792034947

theorem tailTrace_3486796 : CollatzResearch.WordTrace tailWord_3486796 prefixEnd_3486796 198933588019382792034947 := by
  unfold tailWord_3486796
  simp only [CollatzResearch.WordTrace]
  refine ⟨63586948937970532095972121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84782598583960709461296161 63586948937970532095972121)
  ·
    refine ⟨47690211703477899071979091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63586948937970532095972121 47690211703477899071979091)
    ·
      refine ⟨71535317555216848607968637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47690211703477899071979091 71535317555216848607968637)
      ·
        refine ⟨26825744083206318227988239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71535317555216848607968637 26825744083206318227988239)
        ·
          refine ⟨40238616124809477341982359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26825744083206318227988239 40238616124809477341982359)
          ·
            refine ⟨60357924187214216012973539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40238616124809477341982359 60357924187214216012973539)
            ·
              refine ⟨90536886280821324019460309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60357924187214216012973539 90536886280821324019460309)
              ·
                refine ⟨2121958272206749781706101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90536886280821324019460309 2121958272206749781706101)
                ·
                  refine ⟨198933588019382792034947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2121958272206749781706101 198933588019382792034947)
                  ·
                    rfl

theorem cell23_3486796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_3486796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486796 prefixEnd_3486796 := by exact prefixLift 3486796
  have htrace : WordTrace (prefixWord ++ tailWord_3486796) baseStart_3486796 baseEnd_3486796 := by
    simpa [prefixWord, tailWord_3486796, baseEnd_3486796] using wordTrace_append hprefix tailTrace_3486796
  have hstable : (prefixWord ++ tailWord_3486796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486796).length < 2 ^ (prefixWord ++ tailWord_3486796).sum := by decide
  have hdescent : baseEnd_3486796 < baseStart_3486796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486809 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_3486809 : Nat := 118140960795 + 3486809 * 2 ^ 59
def prefixEnd_3486809 : Nat := 4983230072969 + 3 ^ 40 * 3486809 * 2
def baseEnd_3486809 : Nat := 596802989140984525817321

theorem tailTrace_3486809 : CollatzResearch.WordTrace tailWord_3486809 prefixEnd_3486809 596802989140984525817321 := by
  unfold tailWord_3486809
  simp only [CollatzResearch.WordTrace]
  refine ⟨127174372024893967412167481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84782914683262644941444987 127174372024893967412167481)
  ·
    refine ⟨95380779018670475559125611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127174372024893967412167481 95380779018670475559125611)
    ·
      refine ⟨143071168528005713338688417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95380779018670475559125611 143071168528005713338688417)
      ·
        refine ⟨107303376396004285004016313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143071168528005713338688417 107303376396004285004016313)
        ·
          refine ⟨80477532297003213753012235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107303376396004285004016313 80477532297003213753012235)
          ·
            refine ⟨120716298445504820629518353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80477532297003213753012235 120716298445504820629518353)
            ·
              refine ⟨90537223834128615472138765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120716298445504820629518353 90537223834128615472138765)
              ·
                refine ⟨33951458937798230802052037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90537223834128615472138765 33951458937798230802052037)
                ·
                  refine ⟨6365898550837168275384757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33951458937798230802052037 6365898550837168275384757)
                  ·
                    refine ⟨596802989140984525817321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6365898550837168275384757 596802989140984525817321)
                    ·
                      rfl

theorem cell23_3486809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_3486809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486809 prefixEnd_3486809 := by exact prefixLift 3486809
  have htrace : WordTrace (prefixWord ++ tailWord_3486809) baseStart_3486809 baseEnd_3486809 := by
    simpa [prefixWord, tailWord_3486809, baseEnd_3486809] using wordTrace_append hprefix tailTrace_3486809
  have hstable : (prefixWord ++ tailWord_3486809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486809).length < 2 ^ (prefixWord ++ tailWord_3486809).sum := by decide
  have hdescent : baseEnd_3486809 < baseStart_3486809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486816 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 7, 2]
def baseStart_3486816 : Nat := 118140960795 + 3486816 * 2 ^ 59
def prefixEnd_3486816 : Nat := 4983230072969 + 3 ^ 40 * 3486816 * 2
def baseEnd_3486816 : Nat := 1790412561787535050064431

theorem tailTrace_3486816 : CollatzResearch.WordTrace tailWord_3486816 prefixEnd_3486816 1790412561787535050064431 := by
  unfold tailWord_3486816
  simp only [CollatzResearch.WordTrace]
  refine ⟨63587313667934303803836151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84783084890579071738448201 63587313667934303803836151)
  ·
    refine ⟨95380970501901455705754227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63587313667934303803836151 95380970501901455705754227)
    ·
      refine ⟨143071455752852183558631341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95380970501901455705754227 143071455752852183558631341)
      ·
        refine ⟨53651795907319568834486753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143071455752852183558631341 53651795907319568834486753)
        ·
          refine ⟨40238846930489676625865065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53651795907319568834486753 40238846930489676625865065)
          ·
            refine ⟨30179135197867257469398799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40238846930489676625865065 30179135197867257469398799)
            ·
              refine ⟨45268702796800886204098199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30179135197867257469398799 45268702796800886204098199)
              ·
                refine ⟨67903054195201329306147299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45268702796800886204098199 67903054195201329306147299)
                ·
                  refine ⟨101854581292801993959220949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67903054195201329306147299 101854581292801993959220949)
                  ·
                    refine ⟨2387216749050046733419241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101854581292801993959220949 2387216749050046733419241)
                    ·
                      refine ⟨1790412561787535050064431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387216749050046733419241 1790412561787535050064431)
                      ·
                        rfl

theorem cell23_3486816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_3486816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486816 prefixEnd_3486816 := by exact prefixLift 3486816
  have htrace : WordTrace (prefixWord ++ tailWord_3486816) baseStart_3486816 baseEnd_3486816 := by
    simpa [prefixWord, tailWord_3486816, baseEnd_3486816] using wordTrace_append hprefix tailTrace_3486816
  have hstable : (prefixWord ++ tailWord_3486816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486816).length < 2 ^ (prefixWord ++ tailWord_3486816).sum := by decide
  have hdescent : baseEnd_3486816 < baseStart_3486816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486859 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4]
def baseStart_3486859 : Nat := 118140960795 + 3486859 * 2 ^ 59
def prefixEnd_3486859 : Nat := 4983230072969 + 3 ^ 40 * 3486859 * 2
def baseEnd_3486859 : Nat := 1790434641455678381826733

theorem tailTrace_3486859 : CollatzResearch.WordTrace tailWord_3486859 prefixEnd_3486859 1790434641455678381826733 := by
  unfold tailWord_3486859
  simp only [CollatzResearch.WordTrace]
  refine ⟨127176195674712825951487631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84784130449808550634325087 127176195674712825951487631)
  ·
    refine ⟨190764293512069238927231447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127176195674712825951487631 190764293512069238927231447)
    ·
      refine ⟨286146440268103858390847171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190764293512069238927231447 286146440268103858390847171)
      ·
        refine ⟨429219660402155787586270757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286146440268103858390847171 429219660402155787586270757)
        ·
          refine ⟨80478686325404210172425767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429219660402155787586270757 80478686325404210172425767)
          ·
            refine ⟨120718029488106315258638651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80478686325404210172425767 120718029488106315258638651)
            ·
              refine ⟨181077044232159472887957977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120718029488106315258638651 181077044232159472887957977)
              ·
                refine ⟨135807783174119604665968483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181077044232159472887957977 135807783174119604665968483)
                ·
                  refine ⟨203711674761179406998952725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135807783174119604665968483 203711674761179406998952725)
                  ·
                    refine ⟨9548984754430284703075909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 203711674761179406998952725 9548984754430284703075909)
                    ·
                      refine ⟨1790434641455678381826733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9548984754430284703075909 1790434641455678381826733)
                      ·
                        rfl

theorem cell23_3486859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_3486859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486859 prefixEnd_3486859 := by exact prefixLift 3486859
  have htrace : WordTrace (prefixWord ++ tailWord_3486859) baseStart_3486859 baseEnd_3486859 := by
    simpa [prefixWord, tailWord_3486859, baseEnd_3486859] using wordTrace_append hprefix tailTrace_3486859
  have hstable : (prefixWord ++ tailWord_3486859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486859).length < 2 ^ (prefixWord ++ tailWord_3486859).sum := by decide
  have hdescent : baseEnd_3486859 < baseStart_3486859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486890 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3486890 : Nat := 118140960795 + 3486890 * 2 ^ 59
def prefixEnd_3486890 : Nat := 4983230072969 + 3 ^ 40 * 3486890 * 2
def baseEnd_3486890 : Nat := 596816853118655920179697

theorem tailTrace_3486890 : CollatzResearch.WordTrace tailWord_3486890 prefixEnd_3486890 596816853118655920179697 := by
  unfold tailWord_3486890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31794331584400129561466531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84784884225067012163910749 31794331584400129561466531)
  ·
    refine ⟨47691497376600194342199797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31794331584400129561466531 47691497376600194342199797)
    ·
      refine ⟨4471077879056268219581231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47691497376600194342199797 4471077879056268219581231)
      ·
        refine ⟨6706616818584402329371847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471077879056268219581231 6706616818584402329371847)
        ·
          refine ⟨10059925227876603494057771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706616818584402329371847 10059925227876603494057771)
          ·
            refine ⟨15089887841814905241086657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10059925227876603494057771 15089887841814905241086657)
            ·
              refine ⟨11317415881361178930814993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15089887841814905241086657 11317415881361178930814993)
              ·
                refine ⟨8488061911020884198111245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11317415881361178930814993 8488061911020884198111245)
                ·
                  refine ⟨3183023216632831574291717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8488061911020884198111245 3183023216632831574291717)
                  ·
                    refine ⟨596816853118655920179697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183023216632831574291717 596816853118655920179697)
                    ·
                      rfl

theorem cell23_3486890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3486890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486890 prefixEnd_3486890 := by exact prefixLift 3486890
  have htrace : WordTrace (prefixWord ++ tailWord_3486890) baseStart_3486890 baseEnd_3486890 := by
    simpa [prefixWord, tailWord_3486890, baseEnd_3486890] using wordTrace_append hprefix tailTrace_3486890
  have hstable : (prefixWord ++ tailWord_3486890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486890).length < 2 ^ (prefixWord ++ tailWord_3486890).sum := by decide
  have hdescent : baseEnd_3486890 < baseStart_3486890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486957 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3486957 : Nat := 118140960795 + 3486957 * 2 ^ 59
def prefixEnd_3486957 : Nat := 4983230072969 + 3 ^ 40 * 3486957 * 2
def baseEnd_3486957 : Nat := 1790484962559818998401283

theorem tailTrace_3486957 : CollatzResearch.WordTrace tailWord_3486957 prefixEnd_3486957 1790484962559818998401283 := by
  unfold tailWord_3486957
  simp only [CollatzResearch.WordTrace]
  refine ⟨127179770028357788688555125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84786513352238525792370083 127179770028357788688555125)
  ·
    refine ⟨11923103440158542689552043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127179770028357788688555125 11923103440158542689552043)
    ·
      refine ⟨17884655160237814034328065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923103440158542689552043 17884655160237814034328065)
      ·
        refine ⟨13413491370178360525746049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17884655160237814034328065 13413491370178360525746049)
        ·
          refine ⟨10060118527633770394309537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13413491370178360525746049 10060118527633770394309537)
          ·
            refine ⟨7545088895725327795732153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10060118527633770394309537 7545088895725327795732153)
            ·
              refine ⟨5658816671793995846799115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7545088895725327795732153 5658816671793995846799115)
              ·
                refine ⟨8488225007690993770198673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658816671793995846799115 8488225007690993770198673)
                ·
                  refine ⟨6366168755768245327649005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8488225007690993770198673 6366168755768245327649005)
                  ·
                    refine ⟨2387313283413091997868377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6366168755768245327649005 2387313283413091997868377)
                    ·
                      refine ⟨1790484962559818998401283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387313283413091997868377 1790484962559818998401283)
                      ·
                        rfl

theorem cell23_3486957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3486957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486957 prefixEnd_3486957 := by exact prefixLift 3486957
  have htrace : WordTrace (prefixWord ++ tailWord_3486957) baseStart_3486957 baseEnd_3486957 := by
    simpa [prefixWord, tailWord_3486957, baseEnd_3486957] using wordTrace_append hprefix tailTrace_3486957
  have hstable : (prefixWord ++ tailWord_3486957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486957).length < 2 ^ (prefixWord ++ tailWord_3486957).sum := by decide
  have hdescent : baseEnd_3486957 < baseStart_3486957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486970 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4]
def baseStart_3486970 : Nat := 118140960795 + 3486970 * 2 ^ 59
def prefixEnd_3486970 : Nat := 4983230072969 + 3 ^ 40 * 3486970 * 2
def baseEnd_3486970 : Nat := 1790491637808327447538723

theorem tailTrace_3486970 : CollatzResearch.WordTrace tailWord_3486970 prefixEnd_3486970 1790491637808327447538723 := by
  unfold tailWord_3486970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795061044327672977194591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84786829451540461272518909 31795061044327672977194591)
  ·
    refine ⟨47692591566491509465791887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31795061044327672977194591 47692591566491509465791887)
    ·
      refine ⟨71538887349737264198687831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47692591566491509465791887 71538887349737264198687831)
      ·
        refine ⟨107308331024605896298031747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71538887349737264198687831 107308331024605896298031747)
        ·
          refine ⟨160962496536908844447047621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107308331024605896298031747 160962496536908844447047621)
          ·
            refine ⟨30180468100670408333821429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160962496536908844447047621 30180468100670408333821429)
            ·
              refine ⟨2829418884437850781295759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30180468100670408333821429 2829418884437850781295759)
              ·
                refine ⟨4244128326656776171943639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829418884437850781295759 4244128326656776171943639)
                ·
                  refine ⟨6366192489985164257915459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244128326656776171943639 6366192489985164257915459)
                  ·
                    refine ⟨9549288734977746386873189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6366192489985164257915459 9549288734977746386873189)
                    ·
                      refine ⟨1790491637808327447538723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9549288734977746386873189 1790491637808327447538723)
                      ·
                        rfl

theorem cell23_3486970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_3486970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486970 prefixEnd_3486970 := by exact prefixLift 3486970
  have htrace : WordTrace (prefixWord ++ tailWord_3486970) baseStart_3486970 baseEnd_3486970 := by
    simpa [prefixWord, tailWord_3486970, baseEnd_3486970] using wordTrace_append hprefix tailTrace_3486970
  have hstable : (prefixWord ++ tailWord_3486970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486970).length < 2 ^ (prefixWord ++ tailWord_3486970).sum := by decide
  have hdescent : baseEnd_3486970 < baseStart_3486970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486980 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_3486980 : Nat := 118140960795 + 3486980 * 2 ^ 59
def prefixEnd_3486980 : Nat := 4983230072969 + 3 ^ 40 * 3486980 * 2
def baseEnd_3486980 : Nat := 596832257538290802804559

theorem tailTrace_3486980 : CollatzResearch.WordTrace tailWord_3486980 prefixEnd_3486980 596832257538290802804559 := by
  unfold tailWord_3486980
  simp only [CollatzResearch.WordTrace]
  refine ⟨63590304453637231808321197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84787072604849642411094929 63590304453637231808321197)
  ·
    refine ⟨23846364170113961928120449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63590304453637231808321197 23846364170113961928120449)
    ·
      refine ⟨17884773127585471446090337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23846364170113961928120449 17884773127585471446090337)
      ·
        refine ⟨13413579845689103584567753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17884773127585471446090337 13413579845689103584567753)
        ·
          refine ⟨10060184884266827688425815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13413579845689103584567753 10060184884266827688425815)
          ·
            refine ⟨15090277326400241532638723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060184884266827688425815 15090277326400241532638723)
            ·
              refine ⟨22635415989600362298958085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090277326400241532638723 22635415989600362298958085)
              ·
                refine ⟨4244140498050067931054641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22635415989600362298958085 4244140498050067931054641)
                ·
                  refine ⟨3183105373537550948290981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244140498050067931054641 3183105373537550948290981)
                  ·
                    refine ⟨596832257538290802804559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183105373537550948290981 596832257538290802804559)
                    ·
                      rfl

theorem cell23_3486980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_3486980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3486980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3486980 prefixEnd_3486980 := by exact prefixLift 3486980
  have htrace : WordTrace (prefixWord ++ tailWord_3486980) baseStart_3486980 baseEnd_3486980 := by
    simpa [prefixWord, tailWord_3486980, baseEnd_3486980] using wordTrace_append hprefix tailTrace_3486980
  have hstable : (prefixWord ++ tailWord_3486980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486980).length < 2 ^ (prefixWord ++ tailWord_3486980).sum := by decide
  have hdescent : baseEnd_3486980 < baseStart_3486980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487003 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 3]
def baseStart_3487003 : Nat := 118140960795 + 3487003 * 2 ^ 59
def prefixEnd_3487003 : Nat := 4983230072969 + 3 ^ 40 * 3487003 * 2
def baseEnd_3487003 : Nat := 1790508582669925818426071

theorem tailTrace_3487003 : CollatzResearch.WordTrace tailWord_3487003 prefixEnd_3487003 1790508582669925818426071 := by
  unfold tailWord_3487003
  simp only [CollatzResearch.WordTrace]
  refine ⟨127181447786191138544729663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84787631857460759029819775 127181447786191138544729663)
  ·
    refine ⟨190772171679286707817094495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127181447786191138544729663 190772171679286707817094495)
    ·
      refine ⟨286158257518930061725641743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190772171679286707817094495 286158257518930061725641743)
      ·
        refine ⟨429237386278395092588462615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286158257518930061725641743 429237386278395092588462615)
        ·
          refine ⟨643856079417592638882693923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429237386278395092588462615 643856079417592638882693923)
          ·
            refine ⟨965784119126388958324040885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643856079417592638882693923 965784119126388958324040885)
            ·
              refine ⟨90542261168098964842878833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 965784119126388958324040885 90542261168098964842878833)
              ·
                refine ⟨67906695876074223632159125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90542261168098964842878833 67906695876074223632159125)
                ·
                  refine ⟨3183126369190979232757459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67906695876074223632159125 3183126369190979232757459)
                  ·
                    refine ⟨4774689553786468849136189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183126369190979232757459 4774689553786468849136189)
                    ·
                      refine ⟨1790508582669925818426071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4774689553786468849136189 1790508582669925818426071)
                      ·
                        rfl

theorem cell23_3487003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 3].length) (baseStart_3487003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487003 prefixEnd_3487003 := by exact prefixLift 3487003
  have htrace : WordTrace (prefixWord ++ tailWord_3487003) baseStart_3487003 baseEnd_3487003 := by
    simpa [prefixWord, tailWord_3487003, baseEnd_3487003] using wordTrace_append hprefix tailTrace_3487003
  have hstable : (prefixWord ++ tailWord_3487003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487003).length < 2 ^ (prefixWord ++ tailWord_3487003).sum := by decide
  have hdescent : baseEnd_3487003 < baseStart_3487003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487010 : List Nat := [3, 3, 1, 1, 4, 1, 3, 7]
def baseStart_3487010 : Nat := 118140960795 + 3487010 * 2 ^ 59
def prefixEnd_3487010 : Nat := 4983230072969 + 3 ^ 40 * 3487010 * 2
def baseEnd_3487010 : Nat := 66315265816092862631057

theorem tailTrace_3487010 : CollatzResearch.WordTrace tailWord_3487010 prefixEnd_3487010 66315265816092862631057 := by
  unfold tailWord_3487010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795425774291444685058621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84787802064777185826822989 31795425774291444685058621)
  ·
    refine ⟨11923284665359291756896983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31795425774291444685058621 11923284665359291756896983)
    ·
      refine ⟨17884926998038937635345475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923284665359291756896983 17884926998038937635345475)
      ·
        refine ⟨26827390497058406453018213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17884926998038937635345475 26827390497058406453018213)
        ·
          refine ⟨5030135718198451209940915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26827390497058406453018213 5030135718198451209940915)
          ·
            refine ⟨7545203577297676814911373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030135718198451209940915 7545203577297676814911373)
            ·
              refine ⟨2829451341486628805591765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7545203577297676814911373 2829451341486628805591765)
              ·
                refine ⟨66315265816092862631057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2829451341486628805591765 66315265816092862631057)
                ·
                  rfl

theorem cell23_3487010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_3487010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487010 prefixEnd_3487010 := by exact prefixLift 3487010
  have htrace : WordTrace (prefixWord ++ tailWord_3487010) baseStart_3487010 baseEnd_3487010 := by
    simpa [prefixWord, tailWord_3487010, baseEnd_3487010] using wordTrace_append hprefix tailTrace_3487010
  have hstable : (prefixWord ++ tailWord_3487010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487010).length < 2 ^ (prefixWord ++ tailWord_3487010).sum := by decide
  have hdescent : baseEnd_3487010 < baseStart_3487010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487021 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3487021 : Nat := 118140960795 + 3487021 * 2 ^ 59
def prefixEnd_3487021 : Nat := 4983230072969 + 3 ^ 40 * 3487021 * 2
def baseEnd_3487021 : Nat := 1790517825321706748000989

theorem tailTrace_3487021 : CollatzResearch.WordTrace tailWord_3487021 prefixEnd_3487021 1790517825321706748000989 := by
  unfold tailWord_3487021
  simp only [CollatzResearch.WordTrace]
  refine ⟨127182104300125927618884917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84788069533417285079256611 127182104300125927618884917)
  ·
    refine ⟨11923322278136805714270461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127182104300125927618884917 11923322278136805714270461)
    ·
      refine ⟨4471245854301302142851423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11923322278136805714270461 4471245854301302142851423)
      ·
        refine ⟨6706868781451953214277135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471245854301302142851423 6706868781451953214277135)
        ·
          refine ⟨10060303172177929821415703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706868781451953214277135 10060303172177929821415703)
          ·
            refine ⟨15090454758266894732123555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060303172177929821415703 15090454758266894732123555)
            ·
              refine ⟨22635682137400342098185333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090454758266894732123555 22635682137400342098185333)
              ·
                refine ⟨2122095200381282071704875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22635682137400342098185333 2122095200381282071704875)
                ·
                  refine ⟨3183142800571923107557313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122095200381282071704875 3183142800571923107557313)
                  ·
                    refine ⟨2387357100428942330667985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3183142800571923107557313 2387357100428942330667985)
                    ·
                      refine ⟨1790517825321706748000989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387357100428942330667985 1790517825321706748000989)
                      ·
                        rfl

theorem cell23_3487021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3487021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487021 prefixEnd_3487021 := by exact prefixLift 3487021
  have htrace : WordTrace (prefixWord ++ tailWord_3487021) baseStart_3487021 baseEnd_3487021 := by
    simpa [prefixWord, tailWord_3487021, baseEnd_3487021] using wordTrace_append hprefix tailTrace_3487021
  have hstable : (prefixWord ++ tailWord_3487021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487021).length < 2 ^ (prefixWord ++ tailWord_3487021).sum := by decide
  have hdescent : baseEnd_3487021 < baseStart_3487021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487080 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3487080 : Nat := 118140960795 + 3487080 * 2 ^ 59
def prefixEnd_3487080 : Nat := 4983230072969 + 3 ^ 40 * 3487080 * 2
def baseEnd_3487080 : Nat := 1790548120680322017163217

theorem tailTrace_3487080 : CollatzResearch.WordTrace tailWord_3487080 prefixEnd_3487080 1790548120680322017163217 := by
  unfold tailWord_3487080
  simp only [CollatzResearch.WordTrace]
  refine ⟨63592128103456090347641347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84789504137941453796855129 63592128103456090347641347)
  ·
    refine ⟨95388192155184135521462021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63592128103456090347641347 95388192155184135521462021)
    ·
      refine ⟨17885286029097025410274129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95388192155184135521462021 17885286029097025410274129)
      ·
        refine ⟨13413964521822769057705597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17885286029097025410274129 13413964521822769057705597)
        ·
          refine ⟨5030236695683538396639599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13413964521822769057705597 5030236695683538396639599)
          ·
            refine ⟨7545355043525307594959399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030236695683538396639599 7545355043525307594959399)
            ·
              refine ⟨11318032565287961392439099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545355043525307594959399 11318032565287961392439099)
              ·
                refine ⟨16977048847931942088658649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318032565287961392439099 16977048847931942088658649)
                ·
                  refine ⟨12732786635948956566493987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16977048847931942088658649 12732786635948956566493987)
                  ·
                    refine ⟨19099179953923434849740981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12732786635948956566493987 19099179953923434849740981)
                    ·
                      refine ⟨1790548120680322017163217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19099179953923434849740981 1790548120680322017163217)
                      ·
                        rfl

theorem cell23_3487080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3487080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487080 prefixEnd_3487080 := by exact prefixLift 3487080
  have htrace : WordTrace (prefixWord ++ tailWord_3487080) baseStart_3487080 baseEnd_3487080 := by
    simpa [prefixWord, tailWord_3487080, baseEnd_3487080] using wordTrace_append hprefix tailTrace_3487080
  have hstable : (prefixWord ++ tailWord_3487080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487080).length < 2 ^ (prefixWord ++ tailWord_3487080).sum := by decide
  have hdescent : baseEnd_3487080 < baseStart_3487080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487096 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_3487096 : Nat := 118140960795 + 3487096 * 2 ^ 59
def prefixEnd_3487096 : Nat := 4983230072969 + 3 ^ 40 * 3487096 * 2
def baseEnd_3487096 : Nat := 596852112123597984854381

theorem tailTrace_3487096 : CollatzResearch.WordTrace tailWord_3487096 prefixEnd_3487096 596852112123597984854381 := by
  unfold tailWord_3487096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63592419887427107713932571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84789893183236143618576761 63592419887427107713932571)
  ·
    refine ⟨95388629831140661570898857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63592419887427107713932571 95388629831140661570898857)
    ·
      refine ⟨71541472373355496178174143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95388629831140661570898857 71541472373355496178174143)
      ·
        refine ⟨107312208560033244267261215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71541472373355496178174143 107312208560033244267261215)
        ·
          refine ⟨160968312840049866400891823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107312208560033244267261215 160968312840049866400891823)
          ·
            refine ⟨241452469260074799601337735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160968312840049866400891823 241452469260074799601337735)
            ·
              refine ⟨362178703890112199402006603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241452469260074799601337735 362178703890112199402006603)
              ·
                refine ⟨543268055835168299103009905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362178703890112199402006603 543268055835168299103009905)
                ·
                  refine ⟨407451041876376224327257429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543268055835168299103009905 407451041876376224327257429)
                  ·
                    refine ⟨596852112123597984854381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 407451041876376224327257429 596852112123597984854381)
                    ·
                      rfl

theorem cell23_3487096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_3487096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487096 prefixEnd_3487096 := by exact prefixLift 3487096
  have htrace : WordTrace (prefixWord ++ tailWord_3487096) baseStart_3487096 baseEnd_3487096 := by
    simpa [prefixWord, tailWord_3487096, baseEnd_3487096] using wordTrace_append hprefix tailTrace_3487096
  have hstable : (prefixWord ++ tailWord_3487096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487096).length < 2 ^ (prefixWord ++ tailWord_3487096).sum := by decide
  have hdescent : baseEnd_3487096 < baseStart_3487096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487111 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_3487111 : Nat := 118140960795 + 3487111 * 2 ^ 59
def prefixEnd_3487111 : Nat := 4983230072969 + 3 ^ 40 * 3487111 * 2
def baseEnd_3487111 : Nat := 1790564038580611395875575

theorem tailTrace_3487111 : CollatzResearch.WordTrace tailWord_3487111 prefixEnd_3487111 1790564038580611395875575 := by
  unfold tailWord_3487111
  simp only [CollatzResearch.WordTrace]
  refine ⟨127185386869799872989661187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84790257913199915326440791 127185386869799872989661187)
  ·
    refine ⟨190778080304699809484491781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127185386869799872989661187 190778080304699809484491781)
    ·
      refine ⟨35770890057131214278342209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190778080304699809484491781 35770890057131214278342209)
      ·
        refine ⟨26828167542848410708756657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35770890057131214278342209 26828167542848410708756657)
        ·
          refine ⟨20121125657136308031567493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26828167542848410708756657 20121125657136308031567493)
          ·
            refine ⟨3772711060713057755918905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20121125657136308031567493 3772711060713057755918905)
            ·
              refine ⟨2829533295534793316939179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3772711060713057755918905 2829533295534793316939179)
              ·
                refine ⟨4244299943302189975408769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829533295534793316939179 4244299943302189975408769)
                ·
                  refine ⟨3183224957476642481556577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244299943302189975408769 3183224957476642481556577)
                  ·
                    refine ⟨2387418718107481861167433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3183224957476642481556577 2387418718107481861167433)
                    ·
                      refine ⟨1790564038580611395875575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387418718107481861167433 1790564038580611395875575)
                      ·
                        rfl

theorem cell23_3487111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_3487111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487111 prefixEnd_3487111 := by exact prefixLift 3487111
  have htrace : WordTrace (prefixWord ++ tailWord_3487111) baseStart_3487111 baseEnd_3487111 := by
    simpa [prefixWord, tailWord_3487111, baseEnd_3487111] using wordTrace_append hprefix tailTrace_3487111
  have hstable : (prefixWord ++ tailWord_3487111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487111).length < 2 ^ (prefixWord ++ tailWord_3487111).sum := by decide
  have hdescent : baseEnd_3487111 < baseStart_3487111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487130 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_3487130 : Nat := 118140960795 + 3487130 * 2 ^ 59
def prefixEnd_3487130 : Nat := 4983230072969 + 3 ^ 40 * 3487130 * 2
def baseEnd_3487130 : Nat := 596857931571015607179329

theorem tailTrace_3487130 : CollatzResearch.WordTrace tailWord_3487130 prefixEnd_3487130 596857931571015607179329 := by
  unfold tailWord_3487130
  simp only [CollatzResearch.WordTrace]
  refine ⟨31796519964182759808650711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84790719904487359489735229 31796519964182759808650711)
  ·
    refine ⟨47694779946274139712976067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31796519964182759808650711 47694779946274139712976067)
    ·
      refine ⟨71542169919411209569464101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47694779946274139712976067 71542169919411209569464101)
      ·
        refine ⟨13414156859889601794274519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71542169919411209569464101 13414156859889601794274519)
        ·
          refine ⟨20121235289834402691411779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13414156859889601794274519 20121235289834402691411779)
          ·
            refine ⟨30181852934751604037117669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20121235289834402691411779 30181852934751604037117669)
            ·
              refine ⟨5659097425265925756959563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30181852934751604037117669 5659097425265925756959563)
              ·
                refine ⟨8488646137898888635439345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5659097425265925756959563 8488646137898888635439345)
                ·
                  refine ⟨6366484603424166476579509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8488646137898888635439345 6366484603424166476579509)
                  ·
                    refine ⟨596857931571015607179329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6366484603424166476579509 596857931571015607179329)
                    ·
                      rfl

theorem cell23_3487130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_3487130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487130 prefixEnd_3487130 := by exact prefixLift 3487130
  have htrace : WordTrace (prefixWord ++ tailWord_3487130) baseStart_3487130 baseEnd_3487130 := by
    simpa [prefixWord, tailWord_3487130, baseEnd_3487130] using wordTrace_append hprefix tailTrace_3487130
  have hstable : (prefixWord ++ tailWord_3487130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487130).length < 2 ^ (prefixWord ++ tailWord_3487130).sum := by decide
  have hdescent : baseEnd_3487130 < baseStart_3487130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487153 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3487153 : Nat := 118140960795 + 3487153 * 2 ^ 59
def prefixEnd_3487153 : Nat := 4983230072969 + 3 ^ 40 * 3487153 * 2
def baseEnd_3487153 : Nat := 1790585604768100231550381

theorem tailTrace_3487153 : CollatzResearch.WordTrace tailWord_3487153 prefixEnd_3487153 1790585604768100231550381 := by
  unfold tailWord_3487153
  simp only [CollatzResearch.WordTrace]
  refine ⟨127186918735647714162690113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84791279157098476108460075 127186918735647714162690113)
  ·
    refine ⟨95390189051735785622017585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127186918735647714162690113 95390189051735785622017585)
    ·
      refine ⟨71542641788801839216513189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95390189051735785622017585 71542641788801839216513189)
      ·
        refine ⟨13414245335400344853096223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71542641788801839216513189 13414245335400344853096223)
        ·
          refine ⟨20121368003100517279644335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13414245335400344853096223 20121368003100517279644335)
          ·
            refine ⟨30182052004650775919466503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20121368003100517279644335 30182052004650775919466503)
            ·
              refine ⟨45273078006976163879199755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30182052004650775919466503 45273078006976163879199755)
              ·
                refine ⟨67909617010464245818799633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45273078006976163879199755 67909617010464245818799633)
                ·
                  refine ⟨50932212757848184364099725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67909617010464245818799633 50932212757848184364099725)
                  ·
                    refine ⟨19099579784193069136537397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50932212757848184364099725 19099579784193069136537397)
                    ·
                      refine ⟨1790585604768100231550381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19099579784193069136537397 1790585604768100231550381)
                      ·
                        rfl

theorem cell23_3487153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3487153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487153 prefixEnd_3487153 := by exact prefixLift 3487153
  have htrace : WordTrace (prefixWord ++ tailWord_3487153) baseStart_3487153 baseEnd_3487153 := by
    simpa [prefixWord, tailWord_3487153, baseEnd_3487153] using wordTrace_append hprefix tailTrace_3487153
  have hstable : (prefixWord ++ tailWord_3487153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487153).length < 2 ^ (prefixWord ++ tailWord_3487153).sum := by decide
  have hdescent : baseEnd_3487153 < baseStart_3487153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487194 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_3487194 : Nat := 118140960795 + 3487194 * 2 ^ 59
def prefixEnd_3487194 : Nat := 4983230072969 + 3 ^ 40 * 3487194 * 2
def baseEnd_3487194 : Nat := 596868885824978190379231

theorem tailTrace_3487194 : CollatzResearch.WordTrace tailWord_3487194 prefixEnd_3487194 596868885824978190379231 := by
  unfold tailWord_3487194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31797103532124794541233159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84792276085666118776621757 31797103532124794541233159)
  ·
    refine ⟨47695655298187191811849739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31797103532124794541233159 47695655298187191811849739)
    ·
      refine ⟨71543482947280787717774609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47695655298187191811849739 71543482947280787717774609)
      ·
        refine ⟨53657612210460590788330957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71543482947280787717774609 53657612210460590788330957)
        ·
          refine ⟨20121604578922721545624109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53657612210460590788330957 20121604578922721545624109)
          ·
            refine ⟨7545601717096020579609041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20121604578922721545624109 7545601717096020579609041)
            ·
              refine ⟨5659201287822015434706781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7545601717096020579609041 5659201287822015434706781)
              ·
                refine ⟨2122200482933255788015043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5659201287822015434706781 2122200482933255788015043)
                ·
                  refine ⟨3183300724399883682022565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122200482933255788015043 3183300724399883682022565)
                  ·
                    refine ⟨596868885824978190379231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183300724399883682022565 596868885824978190379231)
                    ·
                      rfl

theorem cell23_3487194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_3487194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487194 prefixEnd_3487194 := by exact prefixLift 3487194
  have htrace : WordTrace (prefixWord ++ tailWord_3487194) baseStart_3487194 baseEnd_3487194 := by
    simpa [prefixWord, tailWord_3487194, baseEnd_3487194] using wordTrace_append hprefix tailTrace_3487194
  have hstable : (prefixWord ++ tailWord_3487194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487194).length < 2 ^ (prefixWord ++ tailWord_3487194).sum := by decide
  have hdescent : baseEnd_3487194 < baseStart_3487194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487207 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 6]
def baseStart_3487207 : Nat := 118140960795 + 3487207 * 2 ^ 59
def prefixEnd_3487207 : Nat := 4983230072969 + 3 ^ 40 * 3487207 * 2
def baseEnd_3487207 : Nat := 198957036969271446697237

theorem tailTrace_3487207 : CollatzResearch.WordTrace tailWord_3487207 prefixEnd_3487207 198957036969271446697237 := by
  unfold tailWord_3487207
  simp only [CollatzResearch.WordTrace]
  refine ⟨127188888277452081385155875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84792592184968054256770583 127188888277452081385155875)
  ·
    refine ⟨190783332416178122077733813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127188888277452081385155875 190783332416178122077733813)
    ·
      refine ⟨17885937414016698944787545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190783332416178122077733813 17885937414016698944787545)
      ·
        refine ⟨13414453060512524208590659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17885937414016698944787545 13414453060512524208590659)
        ·
          refine ⟨20121679590768786312885989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13414453060512524208590659 20121679590768786312885989)
          ·
            refine ⟨3772814923269147433666123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20121679590768786312885989 3772814923269147433666123)
            ·
              refine ⟨5659222384903721150499185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772814923269147433666123 5659222384903721150499185)
              ·
                refine ⟨4244416788677790862874389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5659222384903721150499185 4244416788677790862874389)
                ·
                  refine ⟨198957036969271446697237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4244416788677790862874389 198957036969271446697237)
                  ·
                    rfl

theorem cell23_3487207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 6].length) (baseStart_3487207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487207 prefixEnd_3487207 := by exact prefixLift 3487207
  have htrace : WordTrace (prefixWord ++ tailWord_3487207) baseStart_3487207 baseEnd_3487207 := by
    simpa [prefixWord, tailWord_3487207, baseEnd_3487207] using wordTrace_append hprefix tailTrace_3487207
  have hstable : (prefixWord ++ tailWord_3487207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487207).length < 2 ^ (prefixWord ++ tailWord_3487207).sum := by decide
  have hdescent : baseEnd_3487207 < baseStart_3487207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487217 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_3487217 : Nat := 118140960795 + 3487217 * 2 ^ 59
def prefixEnd_3487217 : Nat := 4983230072969 + 3 ^ 40 * 3487217 * 2
def baseEnd_3487217 : Nat := 1790618467529987981150087

theorem tailTrace_3487217 : CollatzResearch.WordTrace tailWord_3487217 prefixEnd_3487217 1790618467529987981150087 := by
  unfold tailWord_3487217
  simp only [CollatzResearch.WordTrace]
  refine ⟨127189253007415853093019905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84792835338277235395346603 127189253007415853093019905)
  ·
    refine ⟨95391939755561889819764929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127189253007415853093019905 95391939755561889819764929)
    ·
      refine ⟨71543954816671417364823697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95391939755561889819764929 71543954816671417364823697)
      ·
        refine ⟨53657966112503563023617773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71543954816671417364823697 53657966112503563023617773)
        ·
          refine ⟨20121737292188836133856665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53657966112503563023617773 20121737292188836133856665)
          ·
            refine ⟨15091302969141627100392499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20121737292188836133856665 15091302969141627100392499)
            ·
              refine ⟨22636954453712440650588749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15091302969141627100392499 22636954453712440650588749)
              ·
                refine ⟨8488857920142165243970781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22636954453712440650588749 8488857920142165243970781)
                ·
                  refine ⟨3183321720053311966489043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8488857920142165243970781 3183321720053311966489043)
                  ·
                    refine ⟨4774982580079967949733565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183321720053311966489043 4774982580079967949733565)
                    ·
                      refine ⟨1790618467529987981150087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4774982580079967949733565 1790618467529987981150087)
                      ·
                        rfl

theorem cell23_3487217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_3487217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487217 prefixEnd_3487217 := by exact prefixLift 3487217
  have htrace : WordTrace (prefixWord ++ tailWord_3487217) baseStart_3487217 baseEnd_3487217 := by
    simpa [prefixWord, tailWord_3487217, baseEnd_3487217] using wordTrace_append hprefix tailTrace_3487217
  have hstable : (prefixWord ++ tailWord_3487217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487217).length < 2 ^ (prefixWord ++ tailWord_3487217).sum := by decide
  have hdescent : baseEnd_3487217 < baseStart_3487217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487223 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_3487223 : Nat := 118140960795 + 3487223 * 2 ^ 59
def prefixEnd_3487223 : Nat := 4983230072969 + 3 ^ 40 * 3487223 * 2
def baseEnd_3487223 : Nat := 1790621548413914957675059

theorem tailTrace_3487223 : CollatzResearch.WordTrace tailWord_3487223 prefixEnd_3487223 1790621548413914957675059 := by
  unfold tailWord_3487223
  simp only [CollatzResearch.WordTrace]
  refine ⟨127189471845394116117738323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84792981230262744078492215 127189471845394116117738323)
  ·
    refine ⟨190784207768091174176607485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127189471845394116117738323 190784207768091174176607485)
    ·
      refine ⟨71544077913034190316227807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190784207768091174176607485 71544077913034190316227807)
      ·
        refine ⟨107316116869551285474341711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71544077913034190316227807 107316116869551285474341711)
        ·
          refine ⟨160974175304326928211512567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107316116869551285474341711 160974175304326928211512567)
          ·
            refine ⟨241461262956490392317268851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160974175304326928211512567 241461262956490392317268851)
            ·
              refine ⟨362191894434735588475903277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241461262956490392317268851 362191894434735588475903277)
              ·
                refine ⟨135821960413025845678463729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362191894434735588475903277 135821960413025845678463729)
                ·
                  refine ⟨101866470309769384258847797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135821960413025845678463729 101866470309769384258847797)
                  ·
                    refine ⟨9549981591540879774266981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101866470309769384258847797 9549981591540879774266981)
                    ·
                      refine ⟨1790621548413914957675059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9549981591540879774266981 1790621548413914957675059)
                      ·
                        rfl

theorem cell23_3487223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_3487223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487223 prefixEnd_3487223 := by exact prefixLift 3487223
  have htrace : WordTrace (prefixWord ++ tailWord_3487223) baseStart_3487223 baseEnd_3487223 := by
    simpa [prefixWord, tailWord_3487223, baseEnd_3487223] using wordTrace_append hprefix tailTrace_3487223
  have hstable : (prefixWord ++ tailWord_3487223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487223).length < 2 ^ (prefixWord ++ tailWord_3487223).sum := by decide
  have hdescent : baseEnd_3487223 < baseStart_3487223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487240 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3487240 : Nat := 118140960795 + 3487240 * 2 ^ 59
def prefixEnd_3487240 : Nat := 4983230072969 + 3 ^ 40 * 3487240 * 2
def baseEnd_3487240 : Nat := 1790630277585041391162481

theorem tailTrace_3487240 : CollatzResearch.WordTrace tailWord_3487240 prefixEnd_3487240 1790630277585041391162481 := by
  unfold tailWord_3487240
  simp only [CollatzResearch.WordTrace]
  refine ⟨63595045943166264010553587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84793394590888352014071449 63595045943166264010553587)
  ·
    refine ⟨95392568914749396015830381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63595045943166264010553587 95392568914749396015830381)
    ·
      refine ⟨35772213343031023505936393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95392568914749396015830381 35772213343031023505936393)
      ·
        refine ⟨26829160007273267629452295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35772213343031023505936393 26829160007273267629452295)
        ·
          refine ⟨40243740010909901444178443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26829160007273267629452295 40243740010909901444178443)
          ·
            refine ⟨60365610016364852166267665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40243740010909901444178443 60365610016364852166267665)
            ·
              refine ⟨45274207512273639124700749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60365610016364852166267665 45274207512273639124700749)
              ·
                refine ⟨16977827817102614671762781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45274207512273639124700749 16977827817102614671762781)
                ·
                  refine ⟨6366685431413480501911043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16977827817102614671762781 6366685431413480501911043)
                  ·
                    refine ⟨9550028147120220752866565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6366685431413480501911043 9550028147120220752866565)
                    ·
                      refine ⟨1790630277585041391162481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9550028147120220752866565 1790630277585041391162481)
                      ·
                        rfl

theorem cell23_3487240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3487240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487240 prefixEnd_3487240 := by exact prefixLift 3487240
  have htrace : WordTrace (prefixWord ++ tailWord_3487240) baseStart_3487240 baseEnd_3487240 := by
    simpa [prefixWord, tailWord_3487240, baseEnd_3487240] using wordTrace_append hprefix tailTrace_3487240
  have hstable : (prefixWord ++ tailWord_3487240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487240).length < 2 ^ (prefixWord ++ tailWord_3487240).sum := by decide
  have hdescent : baseEnd_3487240 < baseStart_3487240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487245 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3487245 : Nat := 118140960795 + 3487245 * 2 ^ 59
def prefixEnd_3487245 : Nat := 4983230072969 + 3 ^ 40 * 3487245 * 2
def baseEnd_3487245 : Nat := 596877614996104623866653

theorem tailTrace_3487245 : CollatzResearch.WordTrace tailWord_3487245 prefixEnd_3487245 596877614996104623866653 := by
  unfold tailWord_3487245
  simp only [CollatzResearch.WordTrace]
  refine ⟨127190274251314413875039189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84793516167542942583359459 127190274251314413875039189)
  ·
    refine ⟨2981022052765181575196231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127190274251314413875039189 2981022052765181575196231)
    ·
      refine ⟨4471533079147772362794347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981022052765181575196231 4471533079147772362794347)
      ·
        refine ⟨6707299618721658544191521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471533079147772362794347 6707299618721658544191521)
        ·
          refine ⟨5030474714041243908143641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6707299618721658544191521 5030474714041243908143641)
          ·
            refine ⟨3772856035530932931107731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030474714041243908143641 3772856035530932931107731)
            ·
              refine ⟨5659284053296399396661597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772856035530932931107731 5659284053296399396661597)
              ·
                refine ⟨2122231519986149773748099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5659284053296399396661597 2122231519986149773748099)
                ·
                  refine ⟨3183347279979224660622149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122231519986149773748099 3183347279979224660622149)
                  ·
                    refine ⟨596877614996104623866653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183347279979224660622149 596877614996104623866653)
                    ·
                      rfl

theorem cell23_3487245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3487245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487245 prefixEnd_3487245 := by exact prefixLift 3487245
  have htrace : WordTrace (prefixWord ++ tailWord_3487245) baseStart_3487245 baseEnd_3487245 := by
    simpa [prefixWord, tailWord_3487245, baseEnd_3487245] using wordTrace_append hprefix tailTrace_3487245
  have hstable : (prefixWord ++ tailWord_3487245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487245).length < 2 ^ (prefixWord ++ tailWord_3487245).sum := by decide
  have hdescent : baseEnd_3487245 < baseStart_3487245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487251 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 1, 1, 3]
def baseStart_3487251 : Nat := 118140960795 + 3487251 * 2 ^ 59
def prefixEnd_3487251 : Nat := 4983230072969 + 3 ^ 40 * 3487251 * 2
def baseEnd_3487251 : Nat := 1790635925872240848124931

theorem tailTrace_3487251 : CollatzResearch.WordTrace tailWord_3487251 prefixEnd_3487251 1790635925872240848124931 := by
  unfold tailWord_3487251
  simp only [CollatzResearch.WordTrace]
  refine ⟨127190493089292676899757607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84793662059528451266505071 127190493089292676899757607)
  ·
    refine ⟨190785739633939015349636411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127190493089292676899757607 190785739633939015349636411)
    ·
      refine ⟨286178609450908523024454617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190785739633939015349636411 286178609450908523024454617)
      ·
        refine ⟨214633957088181392268340963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286178609450908523024454617 214633957088181392268340963)
        ·
          refine ⟨321950935632272088402511445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214633957088181392268340963 321950935632272088402511445)
          ·
            refine ⟨3772862526940688535966931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 321950935632272088402511445 3772862526940688535966931)
            ·
              refine ⟨5659293790411032803950397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772862526940688535966931 5659293790411032803950397)
              ·
                refine ⟨2122235171404137301481399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5659293790411032803950397 2122235171404137301481399)
                ·
                  refine ⟨3183352757106205952222099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122235171404137301481399 3183352757106205952222099)
                  ·
                    refine ⟨4775029135659308928333149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183352757106205952222099 4775029135659308928333149)
                    ·
                      refine ⟨1790635925872240848124931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775029135659308928333149 1790635925872240848124931)
                      ·
                        rfl

theorem cell23_3487251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 1, 3].length) (baseStart_3487251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487251 prefixEnd_3487251 := by exact prefixLift 3487251
  have htrace : WordTrace (prefixWord ++ tailWord_3487251) baseStart_3487251 baseEnd_3487251 := by
    simpa [prefixWord, tailWord_3487251, baseEnd_3487251] using wordTrace_append hprefix tailTrace_3487251
  have hstable : (prefixWord ++ tailWord_3487251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487251).length < 2 ^ (prefixWord ++ tailWord_3487251).sum := by decide
  have hdescent : baseEnd_3487251 < baseStart_3487251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487262 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3487262 : Nat := 118140960795 + 3487262 * 2 ^ 59
def prefixEnd_3487262 : Nat := 4983230072969 + 3 ^ 40 * 3487262 * 2
def baseEnd_3487262 : Nat := 596880524719813435029127

theorem tailTrace_3487262 : CollatzResearch.WordTrace tailWord_3487262 prefixEnd_3487262 596880524719813435029127 := by
  unfold tailWord_3487262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15898861786531603222301005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84793929528168550518938693 15898861786531603222301005)
  ·
    refine ⟨5962073169949351208362877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15898861786531603222301005 5962073169949351208362877)
    ·
      refine ⟨2235777438731006703136079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5962073169949351208362877 2235777438731006703136079)
      ·
        refine ⟨3353666158096510054704119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235777438731006703136079 3353666158096510054704119)
        ·
          refine ⟨5030499237144765082056179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353666158096510054704119 5030499237144765082056179)
          ·
            refine ⟨7545748855717147623084269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030499237144765082056179 7545748855717147623084269)
            ·
              refine ⟨2829655820893930358656601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7545748855717147623084269 2829655820893930358656601)
              ·
                refine ⟨2122241865670447768992451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829655820893930358656601 2122241865670447768992451)
                ·
                  refine ⟨3183362798505671653488677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122241865670447768992451 3183362798505671653488677)
                  ·
                    refine ⟨596880524719813435029127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183362798505671653488677 596880524719813435029127)
                    ·
                      rfl

theorem cell23_3487262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3487262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487262 prefixEnd_3487262 := by exact prefixLift 3487262
  have htrace : WordTrace (prefixWord ++ tailWord_3487262) baseStart_3487262 baseEnd_3487262 := by
    simpa [prefixWord, tailWord_3487262, baseEnd_3487262] using wordTrace_append hprefix tailTrace_3487262
  have hstable : (prefixWord ++ tailWord_3487262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487262).length < 2 ^ (prefixWord ++ tailWord_3487262).sum := by decide
  have hdescent : baseEnd_3487262 < baseStart_3487262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487263 : List Nat := [1, 1, 2, 4, 1, 1, 13]
def baseStart_3487263 : Nat := 118140960795 + 3487263 * 2 ^ 59
def prefixEnd_3487263 : Nat := 4983230072969 + 3 ^ 40 * 3487263 * 2
def baseEnd_3487263 : Nat := 22106692440001170384875

theorem tailTrace_3487263 : CollatzResearch.WordTrace tailWord_3487263 prefixEnd_3487263 22106692440001170384875 := by
  unfold tailWord_3487263
  simp only [CollatzResearch.WordTrace]
  refine ⟨127190930765249202949194443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84793953843499468632796295 127190930765249202949194443)
  ·
    refine ⟨190786396147873804423791665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127190930765249202949194443 190786396147873804423791665)
    ·
      refine ⟨143089797110905353317843749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190786396147873804423791665 143089797110905353317843749)
      ·
        refine ⟨26829336958294753747095703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143089797110905353317843749 26829336958294753747095703)
        ·
          refine ⟨40244005437442130620643555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26829336958294753747095703 40244005437442130620643555)
          ·
            refine ⟨60366008156163195930965333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40244005437442130620643555 60366008156163195930965333)
            ·
              refine ⟨22106692440001170384875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 60366008156163195930965333 22106692440001170384875)
              ·
                rfl

theorem cell23_3487263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 13].length) (baseStart_3487263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487263 prefixEnd_3487263 := by exact prefixLift 3487263
  have htrace : WordTrace (prefixWord ++ tailWord_3487263) baseStart_3487263 baseEnd_3487263 := by
    simpa [prefixWord, tailWord_3487263, baseEnd_3487263] using wordTrace_append hprefix tailTrace_3487263
  have hstable : (prefixWord ++ tailWord_3487263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487263).length < 2 ^ (prefixWord ++ tailWord_3487263).sum := by decide
  have hdescent : baseEnd_3487263 < baseStart_3487263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487360 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_3487360 : Nat := 118140960795 + 3487360 * 2 ^ 59
def prefixEnd_3487360 : Nat := 4983230072969 + 3 ^ 40 * 3487360 * 2
def baseEnd_3487360 : Nat := 1790691895263580921661929

theorem tailTrace_3487360 : CollatzResearch.WordTrace tailWord_3487360 prefixEnd_3487360 1790691895263580921661929 := by
  unfold tailWord_3487360
  simp only [CollatzResearch.WordTrace]
  refine ⟨63597234322948894257737767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84796312430598525676983689 63597234322948894257737767)
  ·
    refine ⟨95395851484423341386606651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63597234322948894257737767 95395851484423341386606651)
    ·
      refine ⟨143093777226635012079909977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95395851484423341386606651 143093777226635012079909977)
      ·
        refine ⟨107320332919976259059932483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143093777226635012079909977 107320332919976259059932483)
        ·
          refine ⟨160980499379964388589898725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107320332919976259059932483 160980499379964388589898725)
          ·
            refine ⟨30183843633743322860606011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160980499379964388589898725 30183843633743322860606011)
            ·
              refine ⟨45275765450614984290909017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30183843633743322860606011 45275765450614984290909017)
              ·
                refine ⟨33956824087961238218181763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45275765450614984290909017 33956824087961238218181763)
                ·
                  refine ⟨50935236131941857327272645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33956824087961238218181763 50935236131941857327272645)
                  ·
                    refine ⟨9550356774739098248863621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50935236131941857327272645 9550356774739098248863621)
                    ·
                      refine ⟨1790691895263580921661929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9550356774739098248863621 1790691895263580921661929)
                      ·
                        rfl

theorem cell23_3487360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_3487360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487360 prefixEnd_3487360 := by exact prefixLift 3487360
  have htrace : WordTrace (prefixWord ++ tailWord_3487360) baseStart_3487360 baseEnd_3487360 := by
    simpa [prefixWord, tailWord_3487360, baseEnd_3487360] using wordTrace_append hprefix tailTrace_3487360
  have hstable : (prefixWord ++ tailWord_3487360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487360).length < 2 ^ (prefixWord ++ tailWord_3487360).sum := by decide
  have hdescent : baseEnd_3487360 < baseStart_3487360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487368 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3487368 : Nat := 118140960795 + 3487368 * 2 ^ 59
def prefixEnd_3487368 : Nat := 4983230072969 + 3 ^ 40 * 3487368 * 2
def baseEnd_3487368 : Nat := 1790696003108816890361893

theorem tailTrace_3487368 : CollatzResearch.WordTrace tailWord_3487368 prefixEnd_3487368 1790696003108816890361893 := by
  unfold tailWord_3487368
  simp only [CollatzResearch.WordTrace]
  refine ⟨63597380214934402940883379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84796506953245870587844505 63597380214934402940883379)
  ·
    refine ⟨95396070322401604411325069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63597380214934402940883379 95396070322401604411325069)
    ·
      refine ⟨35773526370900601654246901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95396070322401604411325069 35773526370900601654246901)
      ·
        refine ⟨3353768097271931405085647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35773526370900601654246901 3353768097271931405085647)
        ·
          refine ⟨5030652145907897107628471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353768097271931405085647 5030652145907897107628471)
          ·
            refine ⟨7545978218861845661442707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030652145907897107628471 7545978218861845661442707)
            ·
              refine ⟨11318967328292768492164061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545978218861845661442707 11318967328292768492164061)
              ·
                refine ⟨4244612748109788184561523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11318967328292768492164061 4244612748109788184561523)
                ·
                  refine ⟨6366919122164682276842285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244612748109788184561523 6366919122164682276842285)
                  ·
                    refine ⟨2387594670811755853815857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6366919122164682276842285 2387594670811755853815857)
                    ·
                      refine ⟨1790696003108816890361893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387594670811755853815857 1790696003108816890361893)
                      ·
                        rfl

theorem cell23_3487368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3487368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487368 prefixEnd_3487368 := by exact prefixLift 3487368
  have htrace : WordTrace (prefixWord ++ tailWord_3487368) baseStart_3487368 baseEnd_3487368 := by
    simpa [prefixWord, tailWord_3487368, baseEnd_3487368] using wordTrace_append hprefix tailTrace_3487368
  have hstable : (prefixWord ++ tailWord_3487368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487368).length < 2 ^ (prefixWord ++ tailWord_3487368).sum := by decide
  have hdescent : baseEnd_3487368 < baseStart_3487368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487397 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_3487397 : Nat := 118140960795 + 3487397 * 2 ^ 59
def prefixEnd_3487397 : Nat := 4983230072969 + 3 ^ 40 * 3487397 * 2
def baseEnd_3487397 : Nat := 1790710894047797276899259

theorem tailTrace_3487397 : CollatzResearch.WordTrace tailWord_3487397 prefixEnd_3487397 1790710894047797276899259 := by
  unfold tailWord_3487397
  simp only [CollatzResearch.WordTrace]
  refine ⟨127195818146763743834572445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84797212097842495889714963 127195818146763743834572445)
  ·
    refine ⟨47698431805036403937964667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127195818146763743834572445 47698431805036403937964667)
    ·
      refine ⟨71547647707554605906947001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47698431805036403937964667 71547647707554605906947001)
      ·
        refine ⟨53660735780665954430210251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71547647707554605906947001 53660735780665954430210251)
        ·
          refine ⟨80491103670998931645315377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53660735780665954430210251 80491103670998931645315377)
          ·
            refine ⟨60368327753249198733986533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80491103670998931645315377 60368327753249198733986533)
            ·
              refine ⟨11319061453734224762622475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60368327753249198733986533 11319061453734224762622475)
              ·
                refine ⟨16978592180601337143933713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319061453734224762622475 16978592180601337143933713)
                ·
                  refine ⟨12733944135451002857950285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16978592180601337143933713 12733944135451002857950285)
                  ·
                    refine ⟨4775229050794126071731357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12733944135451002857950285 4775229050794126071731357)
                    ·
                      refine ⟨1790710894047797276899259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775229050794126071731357 1790710894047797276899259)
                      ·
                        rfl

theorem cell23_3487397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_3487397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487397 prefixEnd_3487397 := by exact prefixLift 3487397
  have htrace : WordTrace (prefixWord ++ tailWord_3487397) baseStart_3487397 baseEnd_3487397 := by
    simpa [prefixWord, tailWord_3487397, baseEnd_3487397] using wordTrace_append hprefix tailTrace_3487397
  have hstable : (prefixWord ++ tailWord_3487397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487397).length < 2 ^ (prefixWord ++ tailWord_3487397).sum := by decide
  have hdescent : baseEnd_3487397 < baseStart_3487397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487434 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_3487434 : Nat := 118140960795 + 3487434 * 2 ^ 59
def prefixEnd_3487434 : Nat := 4983230072969 + 3 ^ 40 * 3487434 * 2
def baseEnd_3487434 : Nat := 596909964277337877378863

theorem tailTrace_3487434 : CollatzResearch.WordTrace tailWord_3487434 prefixEnd_3487434 596909964277337877378863 := by
  unfold tailWord_3487434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31799291911907424788417339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84798111765086466102446237 31799291911907424788417339)
  ·
    refine ⟨47698937867861137182626009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31799291911907424788417339 47698937867861137182626009)
    ·
      refine ⟨35774203400895852886969507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47698937867861137182626009 35774203400895852886969507)
      ·
        refine ⟨53661305101343779330454261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35774203400895852886969507 53661305101343779330454261)
        ·
          refine ⟨5030747353250979312230087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53661305101343779330454261 5030747353250979312230087)
          ·
            refine ⟨7546121029876468968345131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030747353250979312230087 7546121029876468968345131)
            ·
              refine ⟨11319181544814703452517697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546121029876468968345131 11319181544814703452517697)
              ·
                refine ⟨8489386158611027589388273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11319181544814703452517697 8489386158611027589388273)
                ·
                  refine ⟨6367039618958270692041205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8489386158611027589388273 6367039618958270692041205)
                  ·
                    refine ⟨596909964277337877378863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6367039618958270692041205 596909964277337877378863)
                    ·
                      rfl

theorem cell23_3487434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_3487434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487434 prefixEnd_3487434 := by exact prefixLift 3487434
  have htrace : WordTrace (prefixWord ++ tailWord_3487434) baseStart_3487434 baseEnd_3487434 := by
    simpa [prefixWord, tailWord_3487434, baseEnd_3487434] using wordTrace_append hprefix tailTrace_3487434
  have hstable : (prefixWord ++ tailWord_3487434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487434).length < 2 ^ (prefixWord ++ tailWord_3487434).sum := by decide
  have hdescent : baseEnd_3487434 < baseStart_3487434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487440 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_3487440 : Nat := 118140960795 + 3487440 * 2 ^ 59
def prefixEnd_3487440 : Nat := 4983230072969 + 3 ^ 40 * 3487440 * 2
def baseEnd_3487440 : Nat := 1790732973715940608661561

theorem tailTrace_3487440 : CollatzResearch.WordTrace tailWord_3487440 prefixEnd_3487440 1790732973715940608661561 := by
  unfold tailWord_3487440
  simp only [CollatzResearch.WordTrace]
  refine ⟨63598693242803981089193887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84798257657071974785591849 63598693242803981089193887)
  ·
    refine ⟨95398039864205971633790831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63598693242803981089193887 95398039864205971633790831)
    ·
      refine ⟨143097059796308957450686247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95398039864205971633790831 143097059796308957450686247)
      ·
        refine ⟨214645589694463436176029371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143097059796308957450686247 214645589694463436176029371)
        ·
          refine ⟨321968384541695154264044057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214645589694463436176029371 321968384541695154264044057)
          ·
            refine ⟨241476288406271365698033043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321968384541695154264044057 241476288406271365698033043)
            ·
              refine ⟨362214432609407048547049565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241476288406271365698033043 362214432609407048547049565)
              ·
                refine ⟨135830412228527643205143587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362214432609407048547049565 135830412228527643205143587)
                ·
                  refine ⟨203745618342791464807715381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135830412228527643205143587 203745618342791464807715381)
                  ·
                    refine ⟨19101151719636699825723317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203745618342791464807715381 19101151719636699825723317)
                    ·
                      refine ⟨1790732973715940608661561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19101151719636699825723317 1790732973715940608661561)
                      ·
                        rfl

theorem cell23_3487440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_3487440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487440 prefixEnd_3487440 := by exact prefixLift 3487440
  have htrace : WordTrace (prefixWord ++ tailWord_3487440) baseStart_3487440 baseEnd_3487440 := by
    simpa [prefixWord, tailWord_3487440, baseEnd_3487440] using wordTrace_append hprefix tailTrace_3487440
  have hstable : (prefixWord ++ tailWord_3487440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487440).length < 2 ^ (prefixWord ++ tailWord_3487440).sum := by decide
  have hdescent : baseEnd_3487440 < baseStart_3487440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487444 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3487444 : Nat := 118140960795 + 3487444 * 2 ^ 59
def prefixEnd_3487444 : Nat := 4983230072969 + 3 ^ 40 * 3487444 * 2
def baseEnd_3487444 : Nat := 1790735027638558593011543

theorem tailTrace_3487444 : CollatzResearch.WordTrace tailWord_3487444 prefixEnd_3487444 1790735027638558593011543 := by
  unfold tailWord_3487444
  simp only [CollatzResearch.WordTrace]
  refine ⟨63598766188796735430766693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84798354918395647241022257 63598766188796735430766693)
  ·
    refine ⟨11924768660399387893268755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63598766188796735430766693 11924768660399387893268755)
    ·
      refine ⟨17887152990599081839903133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924768660399387893268755 17887152990599081839903133)
      ·
        refine ⟨6707682371474655689963675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17887152990599081839903133 6707682371474655689963675)
        ·
          refine ⟨10061523557211983534945513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707682371474655689963675 10061523557211983534945513)
          ·
            refine ⟨7546142667908987651209135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10061523557211983534945513 7546142667908987651209135)
            ·
              refine ⟨11319214001863481476813703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546142667908987651209135 11319214001863481476813703)
              ·
                refine ⟨16978821002795222215220555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319214001863481476813703 16978821002795222215220555)
                ·
                  refine ⟨25468231504192833322830833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16978821002795222215220555 25468231504192833322830833)
                  ·
                    refine ⟨19101173628144624992123125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25468231504192833322830833 19101173628144624992123125)
                    ·
                      refine ⟨1790735027638558593011543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19101173628144624992123125 1790735027638558593011543)
                      ·
                        rfl

theorem cell23_3487444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3487444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487444 prefixEnd_3487444 := by exact prefixLift 3487444
  have htrace : WordTrace (prefixWord ++ tailWord_3487444) baseStart_3487444 baseEnd_3487444 := by
    simpa [prefixWord, tailWord_3487444, baseEnd_3487444] using wordTrace_append hprefix tailTrace_3487444
  have hstable : (prefixWord ++ tailWord_3487444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487444).length < 2 ^ (prefixWord ++ tailWord_3487444).sum := by decide
  have hdescent : baseEnd_3487444 < baseStart_3487444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487498 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_3487498 : Nat := 118140960795 + 3487498 * 2 ^ 59
def prefixEnd_3487498 : Nat := 4983230072969 + 3 ^ 40 * 3487498 * 2
def baseEnd_3487498 : Nat := 596920918531300460578765

theorem tailTrace_3487498 : CollatzResearch.WordTrace tailWord_3487498 prefixEnd_3487498 596920918531300460578765 := by
  unfold tailWord_3487498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31799875479849459520999787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84799667946265225389332765 31799875479849459520999787)
  ·
    refine ⟨47699813219774189281499681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31799875479849459520999787 47699813219774189281499681)
    ·
      refine ⟨35774859914830641961124761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47699813219774189281499681 35774859914830641961124761)
      ·
        refine ⟨26831144936122981470843571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35774859914830641961124761 26831144936122981470843571)
        ·
          refine ⟨40246717404184472206265357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26831144936122981470843571 40246717404184472206265357)
          ·
            refine ⟨15092519026569177077349509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40246717404184472206265357 15092519026569177077349509)
            ·
              refine ⟨2829847317481720702003033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15092519026569177077349509 2829847317481720702003033)
              ·
                refine ⟨2122385488111290526502275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829847317481720702003033 2122385488111290526502275)
                ·
                  refine ⟨3183578232166935789753413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122385488111290526502275 3183578232166935789753413)
                  ·
                    refine ⟨596920918531300460578765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183578232166935789753413 596920918531300460578765)
                    ·
                      rfl

theorem cell23_3487498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_3487498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487498 prefixEnd_3487498 := by exact prefixLift 3487498
  have htrace : WordTrace (prefixWord ++ tailWord_3487498) baseStart_3487498 baseEnd_3487498 := by
    simpa [prefixWord, tailWord_3487498, baseEnd_3487498] using wordTrace_append hprefix tailTrace_3487498
  have hstable : (prefixWord ++ tailWord_3487498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487498).length < 2 ^ (prefixWord ++ tailWord_3487498).sum := by decide
  have hdescent : baseEnd_3487498 < baseStart_3487498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487521 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3487521 : Nat := 118140960795 + 3487521 * 2 ^ 59
def prefixEnd_3487521 : Nat := 4983230072969 + 3 ^ 40 * 3487521 * 2
def baseEnd_3487521 : Nat := 1790774565648954791748689

theorem tailTrace_3487521 : CollatzResearch.WordTrace tailWord_3487521 prefixEnd_3487521 1790774565648954791748689 := by
  unfold tailWord_3487521
  simp only [CollatzResearch.WordTrace]
  refine ⟨127200340798314513012086417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84800227198876342008057611 127200340798314513012086417)
  ·
    refine ⟨95400255598735884759064813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127200340798314513012086417 95400255598735884759064813)
    ·
      refine ⟨35775095849525956784649305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95400255598735884759064813 35775095849525956784649305)
      ·
        refine ⟨26831321887144467588486979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35775095849525956784649305 26831321887144467588486979)
        ·
          refine ⟨40246982830716701382730469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26831321887144467588486979 40246982830716701382730469)
          ·
            refine ⟨7546309280759381509261963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40246982830716701382730469 7546309280759381509261963)
            ·
              refine ⟨11319463921139072263892945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546309280759381509261963 11319463921139072263892945)
              ·
                refine ⟨8489597940854304197919709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11319463921139072263892945 8489597940854304197919709)
                ·
                  refine ⟨3183599227820364074219891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8489597940854304197919709 3183599227820364074219891)
                  ·
                    refine ⟨4775398841730546111329837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183599227820364074219891 4775398841730546111329837)
                    ·
                      refine ⟨1790774565648954791748689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775398841730546111329837 1790774565648954791748689)
                      ·
                        rfl

theorem cell23_3487521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3487521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487521 prefixEnd_3487521 := by exact prefixLift 3487521
  have htrace : WordTrace (prefixWord ++ tailWord_3487521) baseStart_3487521 baseEnd_3487521 := by
    simpa [prefixWord, tailWord_3487521, baseEnd_3487521] using wordTrace_append hprefix tailTrace_3487521
  have hstable : (prefixWord ++ tailWord_3487521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487521).length < 2 ^ (prefixWord ++ tailWord_3487521).sum := by decide
  have hdescent : baseEnd_3487521 < baseStart_3487521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487524 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_3487524 : Nat := 118140960795 + 3487524 * 2 ^ 59
def prefixEnd_3487524 : Nat := 4983230072969 + 3 ^ 40 * 3487524 * 2
def baseEnd_3487524 : Nat := 596925368696972760003725

theorem tailTrace_3487524 : CollatzResearch.WordTrace tailWord_3487524 prefixEnd_3487524 596925368696972760003725 := by
  unfold tailWord_3487524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63600225108651822262222813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84800300144869096349630417 63600225108651822262222813)
  ·
    refine ⟨23850084415744433348333555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63600225108651822262222813 23850084415744433348333555)
    ·
      refine ⟨35775126623616650022500333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23850084415744433348333555 35775126623616650022500333)
      ·
        refine ⟨13415672483856243758437625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35775126623616650022500333 13415672483856243758437625)
        ·
          refine ⟨10061754362892182818828219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13415672483856243758437625 10061754362892182818828219)
          ·
            refine ⟨15092631544338274228242329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10061754362892182818828219 15092631544338274228242329)
            ·
              refine ⟨11319473658253705671181747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15092631544338274228242329 11319473658253705671181747)
              ·
                refine ⟨16979210487380558506772621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319473658253705671181747 16979210487380558506772621)
                ·
                  refine ⟨6367203932767709440039733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16979210487380558506772621 6367203932767709440039733)
                  ·
                    refine ⟨596925368696972760003725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6367203932767709440039733 596925368696972760003725)
                    ·
                      rfl

theorem cell23_3487524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_3487524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487524 prefixEnd_3487524 := by exact prefixLift 3487524
  have htrace : WordTrace (prefixWord ++ tailWord_3487524) baseStart_3487524 baseEnd_3487524 := by
    simpa [prefixWord, tailWord_3487524, baseEnd_3487524] using wordTrace_append hprefix tailTrace_3487524
  have hstable : (prefixWord ++ tailWord_3487524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487524).length < 2 ^ (prefixWord ++ tailWord_3487524).sum := by decide
  have hdescent : baseEnd_3487524 < baseStart_3487524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487538 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_3487538 : Nat := 118140960795 + 3487538 * 2 ^ 59
def prefixEnd_3487538 : Nat := 4983230072969 + 3 ^ 40 * 3487538 * 2
def baseEnd_3487538 : Nat := 1790783294820081225236111

theorem tailTrace_3487538 : CollatzResearch.WordTrace tailWord_3487538 prefixEnd_3487538 1790783294820081225236111 := by
  unfold tailWord_3487538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31800240209813231228863817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84800640559501949943636845 31800240209813231228863817)
  ·
    refine ⟨23850180157359923421647863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31800240209813231228863817 23850180157359923421647863)
    ·
      refine ⟨35775270236039885132471795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23850180157359923421647863 35775270236039885132471795)
      ·
        refine ⟨53662905354059827698707693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35775270236039885132471795 53662905354059827698707693)
        ·
          refine ⟨20123589507772435387015385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53662905354059827698707693 20123589507772435387015385)
          ·
            refine ⟨15092692130829326540261539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20123589507772435387015385 15092692130829326540261539)
            ·
              refine ⟨22639038196243989810392309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15092692130829326540261539 22639038196243989810392309)
              ·
                refine ⟨2122409830897874044724279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22639038196243989810392309 2122409830897874044724279)
                ·
                  refine ⟨3183614746346811067086419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122409830897874044724279 3183614746346811067086419)
                  ·
                    refine ⟨4775422119520216600629629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183614746346811067086419 4775422119520216600629629)
                    ·
                      refine ⟨1790783294820081225236111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775422119520216600629629 1790783294820081225236111)
                      ·
                        rfl

theorem cell23_3487538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_3487538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487538 prefixEnd_3487538 := by exact prefixLift 3487538
  have htrace : WordTrace (prefixWord ++ tailWord_3487538) baseStart_3487538 baseEnd_3487538 := by
    simpa [prefixWord, tailWord_3487538, baseEnd_3487538] using wordTrace_append hprefix tailTrace_3487538
  have hstable : (prefixWord ++ tailWord_3487538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487538).length < 2 ^ (prefixWord ++ tailWord_3487538).sum := by decide
  have hdescent : baseEnd_3487538 < baseStart_3487538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487541 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3487541 : Nat := 118140960795 + 3487541 * 2 ^ 59
def prefixEnd_3487541 : Nat := 4983230072969 + 3 ^ 40 * 3487541 * 2
def baseEnd_3487541 : Nat := 596928278420681571166199

theorem tailTrace_3487541 : CollatzResearch.WordTrace tailWord_3487541 prefixEnd_3487541 596928278420681571166199 := by
  unfold tailWord_3487541
  simp only [CollatzResearch.WordTrace]
  refine ⟨127201070258242056427814477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84800713505494704285209651 127201070258242056427814477)
  ·
    refine ⟨47700401346840771160430429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127201070258242056427814477 47700401346840771160430429)
    ·
      refine ⟨17887650505065289185161411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47700401346840771160430429 17887650505065289185161411)
      ·
        refine ⟨26831475757597933777742117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17887650505065289185161411 26831475757597933777742117)
        ·
          refine ⟨5030901704549612583326647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26831475757597933777742117 5030901704549612583326647)
          ·
            refine ⟨7546352556824418874989971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030901704549612583326647 7546352556824418874989971)
            ·
              refine ⟨11319528835236628312484957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546352556824418874989971 11319528835236628312484957)
              ·
                refine ⟨4244823313213735617181859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11319528835236628312484957 4244823313213735617181859)
                ·
                  refine ⟨6367234969820603425772789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244823313213735617181859 6367234969820603425772789)
                  ·
                    refine ⟨596928278420681571166199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6367234969820603425772789 596928278420681571166199)
                    ·
                      rfl

theorem cell23_3487541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3487541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487541 prefixEnd_3487541 := by exact prefixLift 3487541
  have htrace : WordTrace (prefixWord ++ tailWord_3487541) baseStart_3487541 baseEnd_3487541 := by
    simpa [prefixWord, tailWord_3487541, baseEnd_3487541] using wordTrace_append hprefix tailTrace_3487541
  have hstable : (prefixWord ++ tailWord_3487541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487541).length < 2 ^ (prefixWord ++ tailWord_3487541).sum := by decide
  have hdescent : baseEnd_3487541 < baseStart_3487541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487557 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3487557 : Nat := 118140960795 + 3487557 * 2 ^ 59
def prefixEnd_3487557 : Nat := 4983230072969 + 3 ^ 40 * 3487557 * 2
def baseEnd_3487557 : Nat := 1790793050952516650898523

theorem tailTrace_3487557 : CollatzResearch.WordTrace tailWord_3487557 prefixEnd_3487557 1790793050952516650898523 := by
  unfold tailWord_3487557
  simp only [CollatzResearch.WordTrace]
  refine ⟨127201653826184091160396925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84801102550789394106931283 127201653826184091160396925)
  ·
    refine ⟨47700620184819034185148847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127201653826184091160396925 47700620184819034185148847)
    ·
      refine ⟨71550930277228551277723271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47700620184819034185148847 71550930277228551277723271)
      ·
        refine ⟨107326395415842826916584907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71550930277228551277723271 107326395415842826916584907)
        ·
          refine ⟨160989593123764240374877361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107326395415842826916584907 160989593123764240374877361)
          ·
            refine ⟨120742194842823180281158021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160989593123764240374877361 120742194842823180281158021)
            ·
              refine ⟨22639161533029346302717129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120742194842823180281158021 22639161533029346302717129)
              ·
                refine ⟨16979371149772009727037847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22639161533029346302717129 16979371149772009727037847)
                ·
                  refine ⟨25469056724658014590556771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16979371149772009727037847 25469056724658014590556771)
                  ·
                    refine ⟨38203585086987021885835157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25469056724658014590556771 38203585086987021885835157)
                    ·
                      refine ⟨1790793050952516650898523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38203585086987021885835157 1790793050952516650898523)
                      ·
                        rfl

theorem cell23_3487557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3487557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487557 prefixEnd_3487557 := by exact prefixLift 3487557
  have htrace : WordTrace (prefixWord ++ tailWord_3487557) baseStart_3487557 baseEnd_3487557 := by
    simpa [prefixWord, tailWord_3487557, baseEnd_3487557] using wordTrace_append hprefix tailTrace_3487557
  have hstable : (prefixWord ++ tailWord_3487557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487557).length < 2 ^ (prefixWord ++ tailWord_3487557).sum := by decide
  have hdescent : baseEnd_3487557 < baseStart_3487557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487584 : List Nat := [2, 1, 1, 3, 3, 2, 4, 7]
def baseStart_3487584 : Nat := 118140960795 + 3487584 * 2 ^ 59
def prefixEnd_3487584 : Nat := 4983230072969 + 3 ^ 40 * 3487584 * 2
def baseEnd_3487584 : Nat := 66326182034451409083737

theorem tailTrace_3487584 : CollatzResearch.WordTrace tailWord_3487584 prefixEnd_3487584 66326182034451409083737 := by
  unfold tailWord_3487584
  simp only [CollatzResearch.WordTrace]
  refine ⟨63601319298543137385814903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84801759064724183181086537 63601319298543137385814903)
  ·
    refine ⟨95401978947814706078722355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63601319298543137385814903 95401978947814706078722355)
    ·
      refine ⟨143102968421722059118083533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95401978947814706078722355 143102968421722059118083533)
      ·
        refine ⟨53663613158145772169281325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143102968421722059118083533 53663613158145772169281325)
        ·
          refine ⟨20123854934304664563480497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53663613158145772169281325 20123854934304664563480497)
          ·
            refine ⟨15092891200728498422610373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20123854934304664563480497 15092891200728498422610373)
            ·
              refine ⟨2829917100136593454239445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15092891200728498422610373 2829917100136593454239445)
              ·
                refine ⟨66326182034451409083737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2829917100136593454239445 66326182034451409083737)
                ·
                  rfl

theorem cell23_3487584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 7].length) (baseStart_3487584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487584 prefixEnd_3487584 := by exact prefixLift 3487584
  have htrace : WordTrace (prefixWord ++ tailWord_3487584) baseStart_3487584 baseEnd_3487584 := by
    simpa [prefixWord, tailWord_3487584, baseEnd_3487584] using wordTrace_append hprefix tailTrace_3487584
  have hstable : (prefixWord ++ tailWord_3487584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487584).length < 2 ^ (prefixWord ++ tailWord_3487584).sum := by decide
  have hdescent : baseEnd_3487584 < baseStart_3487584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487598 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3487598 : Nat := 118140960795 + 3487598 * 2 ^ 59
def prefixEnd_3487598 : Nat := 4983230072969 + 3 ^ 40 * 3487598 * 2
def baseEnd_3487598 : Nat := 1790814103659350990485835

theorem tailTrace_3487598 : CollatzResearch.WordTrace tailWord_3487598 prefixEnd_3487598 1790814103659350990485835 := by
  unfold tailWord_3487598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15900393652379444395329931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84802099479357036775092965 15900393652379444395329931)
  ·
    refine ⟨23850590478569166592994897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15900393652379444395329931 23850590478569166592994897)
    ·
      refine ⟨17887942858926874944746173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23850590478569166592994897 17887942858926874944746173)
      ·
        refine ⟨6707978572097578104279815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17887942858926874944746173 6707978572097578104279815)
        ·
          refine ⟨10061967858146367156419723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707978572097578104279815 10061967858146367156419723)
          ·
            refine ⟨15092951787219550734629585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10061967858146367156419723 15092951787219550734629585)
            ·
              refine ⟨11319713840414663050972189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15092951787219550734629585 11319713840414663050972189)
              ·
                refine ⟨4244892690155498644114571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11319713840414663050972189 4244892690155498644114571)
                ·
                  refine ⟨6367339035233247966171857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244892690155498644114571 6367339035233247966171857)
                  ·
                    refine ⟨4775504276424935974628893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6367339035233247966171857 4775504276424935974628893)
                    ·
                      refine ⟨1790814103659350990485835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775504276424935974628893 1790814103659350990485835)
                      ·
                        rfl

theorem cell23_3487598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3487598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487598 prefixEnd_3487598 := by exact prefixLift 3487598
  have htrace : WordTrace (prefixWord ++ tailWord_3487598) baseStart_3487598 baseEnd_3487598 := by
    simpa [prefixWord, tailWord_3487598, baseEnd_3487598] using wordTrace_append hprefix tailTrace_3487598
  have hstable : (prefixWord ++ tailWord_3487598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487598).length < 2 ^ (prefixWord ++ tailWord_3487598).sum := by decide
  have hdescent : baseEnd_3487598 < baseStart_3487598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487611 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 3]
def baseStart_3487611 : Nat := 118140960795 + 3487611 * 2 ^ 59
def prefixEnd_3487611 : Nat := 4983230072969 + 3 ^ 40 * 3487611 * 2
def baseEnd_3487611 : Nat := 1790820778907859439623275

theorem tailTrace_3487611 : CollatzResearch.WordTrace tailWord_3487611 prefixEnd_3487611 1790820778907859439623275 := by
  unfold tailWord_3487611
  simp only [CollatzResearch.WordTrace]
  refine ⟨127203623367988458382862687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84802415578658972255241791 127203623367988458382862687)
  ·
    refine ⟨190805435051982687574294031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127203623367988458382862687 190805435051982687574294031)
    ·
      refine ⟨286208152577974031361441047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190805435051982687574294031 286208152577974031361441047)
      ·
        refine ⟨429312228866961047042161571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286208152577974031361441047 429312228866961047042161571)
        ·
          refine ⟨643968343300441570563242357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429312228866961047042161571 643968343300441570563242357)
          ·
            refine ⟨60372032184416397240303971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 643968343300441570563242357 60372032184416397240303971)
            ·
              refine ⟨90558048276624595860455957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60372032184416397240303971 90558048276624595860455957)
              ·
                refine ⟨4244908512966777930958873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90558048276624595860455957 4244908512966777930958873)
                ·
                  refine ⟨3183681384725083448219155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244908512966777930958873 3183681384725083448219155)
                  ·
                    refine ⟨4775522077087625172328733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183681384725083448219155 4775522077087625172328733)
                    ·
                      refine ⟨1790820778907859439623275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775522077087625172328733 1790820778907859439623275)
                      ·
                        rfl

theorem cell23_3487611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 3].length) (baseStart_3487611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487611 prefixEnd_3487611 := by exact prefixLift 3487611
  have htrace : WordTrace (prefixWord ++ tailWord_3487611) baseStart_3487611 baseEnd_3487611 := by
    simpa [prefixWord, tailWord_3487611, baseEnd_3487611] using wordTrace_append hprefix tailTrace_3487611
  have hstable : (prefixWord ++ tailWord_3487611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487611).length < 2 ^ (prefixWord ++ tailWord_3487611).sum := by decide
  have hdescent : baseEnd_3487611 < baseStart_3487611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487621 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 3, 3, 2]
def baseStart_3487621 : Nat := 118140960795 + 3487621 * 2 ^ 59
def prefixEnd_3487621 : Nat := 4983230072969 + 3 ^ 40 * 3487621 * 2
def baseEnd_3487621 : Nat := 1790825913714404400498229

theorem tailTrace_3487621 : CollatzResearch.WordTrace tailWord_3487621 prefixEnd_3487621 1790825913714404400498229 := by
  unfold tailWord_3487621
  simp only [CollatzResearch.WordTrace]
  refine ⟨127203988097952230090726717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84802658731968153393817811 127203988097952230090726717)
  ·
    refine ⟨47701495536732086284022519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127203988097952230090726717 47701495536732086284022519)
    ·
      refine ⟨71552243305098129426033779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47701495536732086284022519 71552243305098129426033779)
      ·
        refine ⟨107328364957647194139050669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71552243305098129426033779 107328364957647194139050669)
        ·
          refine ⟨40248136859117697802144001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107328364957647194139050669 40248136859117697802144001)
          ·
            refine ⟨30186102644338273351608001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40248136859117697802144001 30186102644338273351608001)
            ·
              refine ⟨22639576983253705013706001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30186102644338273351608001 22639576983253705013706001)
              ·
                refine ⟨16979682737440278760279501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22639576983253705013706001 16979682737440278760279501)
                ·
                  refine ⟨6367381026540104535104813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16979682737440278760279501 6367381026540104535104813)
                  ·
                    refine ⟨2387767884952539200664305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6367381026540104535104813 2387767884952539200664305)
                    ·
                      refine ⟨1790825913714404400498229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387767884952539200664305 1790825913714404400498229)
                      ·
                        rfl

theorem cell23_3487621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_3487621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487621 prefixEnd_3487621 := by exact prefixLift 3487621
  have htrace : WordTrace (prefixWord ++ tailWord_3487621) baseStart_3487621 baseEnd_3487621 := by
    simpa [prefixWord, tailWord_3487621, baseEnd_3487621] using wordTrace_append hprefix tailTrace_3487621
  have hstable : (prefixWord ++ tailWord_3487621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487621).length < 2 ^ (prefixWord ++ tailWord_3487621).sum := by decide
  have hdescent : baseEnd_3487621 < baseStart_3487621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487627 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 8]
def baseStart_3487627 : Nat := 118140960795 + 3487627 * 2 ^ 59
def prefixEnd_3487627 : Nat := 4983230072969 + 3 ^ 40 * 3487627 * 2
def baseEnd_3487627 : Nat := 596942998199443792341067

theorem tailTrace_3487627 : CollatzResearch.WordTrace tailWord_3487627 prefixEnd_3487627 596942998199443792341067 := by
  unfold tailWord_3487627
  simp only [CollatzResearch.WordTrace]
  refine ⟨127204206935930493115445135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84802804623953662076963423 127204206935930493115445135)
  ·
    refine ⟨190806310403895739673167703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127204206935930493115445135 190806310403895739673167703)
    ·
      refine ⟨286209465605843609509751555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190806310403895739673167703 286209465605843609509751555)
      ·
        refine ⟨429314198408765414264627333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286209465605843609509751555 429314198408765414264627333)
        ·
          refine ⟨80496412201643515174617625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429314198408765414264627333 80496412201643515174617625)
          ·
            refine ⟨60372309151232636380963219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80496412201643515174617625 60372309151232636380963219)
            ·
              refine ⟨90558463726848954571444829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60372309151232636380963219 90558463726848954571444829)
              ·
                refine ⟨33959423897568357964291811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90558463726848954571444829 33959423897568357964291811)
                ·
                  refine ⟨50939135846352536946437717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33959423897568357964291811 50939135846352536946437717)
                  ·
                    refine ⟨596942998199443792341067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50939135846352536946437717 596942998199443792341067)
                    ·
                      rfl

theorem cell23_3487627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_3487627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487627 prefixEnd_3487627 := by exact prefixLift 3487627
  have htrace : WordTrace (prefixWord ++ tailWord_3487627) baseStart_3487627 baseEnd_3487627 := by
    simpa [prefixWord, tailWord_3487627, baseEnd_3487627] using wordTrace_append hprefix tailTrace_3487627
  have hstable : (prefixWord ++ tailWord_3487627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487627).length < 2 ^ (prefixWord ++ tailWord_3487627).sum := by decide
  have hdescent : baseEnd_3487627 < baseStart_3487627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487657 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 11]
def baseStart_3487657 : Nat := 118140960795 + 3487657 * 2 ^ 59
def prefixEnd_3487657 : Nat := 4983230072969 + 3 ^ 40 * 3487657 * 2
def baseEnd_3487657 : Nat := 198982711001996251072007

theorem tailTrace_3487657 : CollatzResearch.WordTrace tailWord_3487657 prefixEnd_3487657 198982711001996251072007 := by
  unfold tailWord_3487657
  simp only [CollatzResearch.WordTrace]
  refine ⟨127205301125821808239037225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84803534083881205492691483 127205301125821808239037225)
  ·
    refine ⟨95403975844366356179277919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127205301125821808239037225 95403975844366356179277919)
    ·
      refine ⟨143105963766549534268916879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95403975844366356179277919 143105963766549534268916879)
      ·
        refine ⟨214658945649824301403375319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143105963766549534268916879 214658945649824301403375319)
        ·
          refine ⟨321988418474736452105062979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214658945649824301403375319 321988418474736452105062979)
          ·
            refine ⟨482982627712104678157594469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321988418474736452105062979 482982627712104678157594469)
            ·
              refine ⟨90559242696019627154548963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 482982627712104678157594469 90559242696019627154548963)
              ·
                refine ⟨135838864044029440731823445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90559242696019627154548963 135838864044029440731823445)
                ·
                  refine ⟨198982711001996251072007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 135838864044029440731823445 198982711001996251072007)
                  ·
                    rfl

theorem cell23_3487657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_3487657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487657 prefixEnd_3487657 := by exact prefixLift 3487657
  have htrace : WordTrace (prefixWord ++ tailWord_3487657) baseStart_3487657 baseEnd_3487657 := by
    simpa [prefixWord, tailWord_3487657, baseEnd_3487657] using wordTrace_append hprefix tailTrace_3487657
  have hstable : (prefixWord ++ tailWord_3487657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487657).length < 2 ^ (prefixWord ++ tailWord_3487657).sum := by decide
  have hdescent : baseEnd_3487657 < baseStart_3487657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487704 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_3487704 : Nat := 118140960795 + 3487704 * 2 ^ 59
def prefixEnd_3487704 : Nat := 4983230072969 + 3 ^ 40 * 3487704 * 2
def baseEnd_3487704 : Nat := 596956177536242525253449

theorem tailTrace_3487704 : CollatzResearch.WordTrace tailWord_3487704 prefixEnd_3487704 596956177536242525253449 := by
  unfold tailWord_3487704
  simp only [CollatzResearch.WordTrace]
  refine ⟨63603507678325767632999083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84804676904434356843998777 63603507678325767632999083)
  ·
    refine ⟨95405261517488651449498625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63603507678325767632999083 95405261517488651449498625)
    ·
      refine ⟨71553946138116488587123969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95405261517488651449498625 71553946138116488587123969)
      ·
        refine ⟨53665459603587366440342977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71553946138116488587123969 53665459603587366440342977)
        ·
          refine ⟨40249094702690524830257233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53665459603587366440342977 40249094702690524830257233)
          ·
            refine ⟨30186821027017893622692925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40249094702690524830257233 30186821027017893622692925)
            ·
              refine ⟨11320057885131710108509847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30186821027017893622692925 11320057885131710108509847)
              ·
                refine ⟨16980086827697565162764771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11320057885131710108509847 16980086827697565162764771)
                ·
                  refine ⟨25470130241546347744147157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16980086827697565162764771 25470130241546347744147157)
                  ·
                    refine ⟨596956177536242525253449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25470130241546347744147157 596956177536242525253449)
                    ·
                      rfl

theorem cell23_3487704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_3487704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487704 prefixEnd_3487704 := by exact prefixLift 3487704
  have htrace : WordTrace (prefixWord ++ tailWord_3487704) baseStart_3487704 baseEnd_3487704 := by
    simpa [prefixWord, tailWord_3487704, baseEnd_3487704] using wordTrace_append hprefix tailTrace_3487704
  have hstable : (prefixWord ++ tailWord_3487704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487704).length < 2 ^ (prefixWord ++ tailWord_3487704).sum := by decide
  have hdescent : baseEnd_3487704 < baseStart_3487704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487719 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3487719 : Nat := 118140960795 + 3487719 * 2 ^ 59
def prefixEnd_3487719 : Nat := 4983230072969 + 3 ^ 40 * 3487719 * 2
def baseEnd_3487719 : Nat := 1790876234818545017072779

theorem tailTrace_3487719 : CollatzResearch.WordTrace tailWord_3487719 prefixEnd_3487719 1790876234818545017072779 := by
  unfold tailWord_3487719
  simp only [CollatzResearch.WordTrace]
  refine ⟨127207562451597192827794211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84805041634398128551862807 127207562451597192827794211)
  ·
    refine ⟨190811343677395789241691317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127207562451597192827794211 190811343677395789241691317)
    ·
      refine ⟨17888563469755855241408561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190811343677395789241691317 17888563469755855241408561)
      ·
        refine ⟨13416422602316891431056421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17888563469755855241408561 13416422602316891431056421)
        ·
          refine ⟨2515579237934417143323079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13416422602316891431056421 2515579237934417143323079)
          ·
            refine ⟨3773368856901625714984619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515579237934417143323079 3773368856901625714984619)
            ·
              refine ⟨5660053285352438572476929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773368856901625714984619 5660053285352438572476929)
              ·
                refine ⟨4245039964014328929357697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5660053285352438572476929 4245039964014328929357697)
                ·
                  refine ⟨3183779973010746697018273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4245039964014328929357697 3183779973010746697018273)
                  ·
                    refine ⟨2387834979758060022763705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3183779973010746697018273 2387834979758060022763705)
                    ·
                      refine ⟨1790876234818545017072779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387834979758060022763705 1790876234818545017072779)
                      ·
                        rfl

theorem cell23_3487719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3487719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487719 prefixEnd_3487719 := by exact prefixLift 3487719
  have htrace : WordTrace (prefixWord ++ tailWord_3487719) baseStart_3487719 baseEnd_3487719 := by
    simpa [prefixWord, tailWord_3487719, baseEnd_3487719] using wordTrace_append hprefix tailTrace_3487719
  have hstable : (prefixWord ++ tailWord_3487719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487719).length < 2 ^ (prefixWord ++ tailWord_3487719).sum := by decide
  have hdescent : baseEnd_3487719 < baseStart_3487719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487778 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_3487778 : Nat := 118140960795 + 3487778 * 2 ^ 59
def prefixEnd_3487778 : Nat := 4983230072969 + 3 ^ 40 * 3487778 * 2
def baseEnd_3487778 : Nat := 1790906530177160286235007

theorem tailTrace_3487778 : CollatzResearch.WordTrace tailWord_3487778 prefixEnd_3487778 1790906530177160286235007 := by
  unfold tailWord_3487778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31802428589595861476047997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84806476238922297269461325 31802428589595861476047997)
  ·
    refine ⟨11925910721098448053517999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31802428589595861476047997 11925910721098448053517999)
    ·
      refine ⟨17888866081647672080276999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11925910721098448053517999 17888866081647672080276999)
      ·
        refine ⟨26833299122471508120415499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17888866081647672080276999 26833299122471508120415499)
        ·
          refine ⟨40249948683707262180623249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26833299122471508120415499 40249948683707262180623249)
          ·
            refine ⟨30187461512780446635467437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40249948683707262180623249 30187461512780446635467437)
            ·
              refine ⟨11320298067292667488300289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30187461512780446635467437 11320298067292667488300289)
              ·
                refine ⟨8490223550469500616225217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11320298067292667488300289 8490223550469500616225217)
                ·
                  refine ⟨6367667662852125462168913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8490223550469500616225217 6367667662852125462168913)
                  ·
                    refine ⟨4775750747139094096626685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6367667662852125462168913 4775750747139094096626685)
                    ·
                      refine ⟨1790906530177160286235007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775750747139094096626685 1790906530177160286235007)
                      ·
                        rfl

theorem cell23_3487778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_3487778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487778 prefixEnd_3487778 := by exact prefixLift 3487778
  have htrace : WordTrace (prefixWord ++ tailWord_3487778) baseStart_3487778 baseEnd_3487778 := by
    simpa [prefixWord, tailWord_3487778, baseEnd_3487778] using wordTrace_append hprefix tailTrace_3487778
  have hstable : (prefixWord ++ tailWord_3487778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487778).length < 2 ^ (prefixWord ++ tailWord_3487778).sum := by decide
  have hdescent : baseEnd_3487778 < baseStart_3487778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487798 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3487798 : Nat := 118140960795 + 3487798 * 2 ^ 59
def prefixEnd_3487798 : Nat := 4983230072969 + 3 ^ 40 * 3487798 * 2
def baseEnd_3487798 : Nat := 198990755532250023109435

theorem tailTrace_3487798 : CollatzResearch.WordTrace tailWord_3487798 prefixEnd_3487798 198990755532250023109435 := by
  unfold tailWord_3487798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950652738644436832495003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84806962545540659546613365 7950652738644436832495003)
  ·
    refine ⟨11925979107966655248742505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950652738644436832495003 11925979107966655248742505)
    ·
      refine ⟨8944484330974991436556879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11925979107966655248742505 8944484330974991436556879)
      ·
        refine ⟨13416726496462487154835319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8944484330974991436556879 13416726496462487154835319)
        ·
          refine ⟨20125089744693730732252979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13416726496462487154835319 20125089744693730732252979)
          ·
            refine ⟨30187634617040596098379469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20125089744693730732252979 30187634617040596098379469)
            ·
              refine ⟨11320362981390223536892301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30187634617040596098379469 11320362981390223536892301)
              ·
                refine ⟨4245136118021333826334613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11320362981390223536892301 4245136118021333826334613)
                ·
                  refine ⟨198990755532250023109435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4245136118021333826334613 198990755532250023109435)
                  ·
                    rfl

theorem cell23_3487798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3487798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487798 prefixEnd_3487798 := by exact prefixLift 3487798
  have htrace : WordTrace (prefixWord ++ tailWord_3487798) baseStart_3487798 baseEnd_3487798 := by
    simpa [prefixWord, tailWord_3487798, baseEnd_3487798] using wordTrace_append hprefix tailTrace_3487798
  have hstable : (prefixWord ++ tailWord_3487798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487798).length < 2 ^ (prefixWord ++ tailWord_3487798).sum := by decide
  have hdescent : baseEnd_3487798 < baseStart_3487798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487811 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 1, 5]
def baseStart_3487811 : Nat := 118140960795 + 3487811 * 2 ^ 59
def prefixEnd_3487811 : Nat := 4983230072969 + 3 ^ 40 * 3487811 * 2
def baseEnd_3487811 : Nat := 596974491679586219040785

theorem tailTrace_3487811 : CollatzResearch.WordTrace tailWord_3487811 prefixEnd_3487811 596974491679586219040785 := by
  unfold tailWord_3487811
  simp only [CollatzResearch.WordTrace]
  refine ⟨127210917967263892540143287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84807278644842595026762191 127210917967263892540143287)
  ·
    refine ⟨190816376950895838810214931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127210917967263892540143287 190816376950895838810214931)
    ·
      refine ⟨286224565426343758215322397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190816376950895838810214931 286224565426343758215322397)
      ·
        refine ⟨107334212034878909330745899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286224565426343758215322397 107334212034878909330745899)
        ·
          refine ⟨161001318052318363996118849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107334212034878909330745899 161001318052318363996118849)
          ·
            refine ⟨120750988539238772997089137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161001318052318363996118849 120750988539238772997089137)
            ·
              refine ⟨90563241404429079747816853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120750988539238772997089137 90563241404429079747816853)
              ·
                refine ⟨4245151940832613113178915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90563241404429079747816853 4245151940832613113178915)
                ·
                  refine ⟨6367727911248919669768373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245151940832613113178915 6367727911248919669768373)
                  ·
                    refine ⟨596974491679586219040785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6367727911248919669768373 596974491679586219040785)
                    ·
                      rfl

theorem cell23_3487811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 5].length) (baseStart_3487811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487811 prefixEnd_3487811 := by exact prefixLift 3487811
  have htrace : WordTrace (prefixWord ++ tailWord_3487811) baseStart_3487811 baseEnd_3487811 := by
    simpa [prefixWord, tailWord_3487811, baseEnd_3487811] using wordTrace_append hprefix tailTrace_3487811
  have hstable : (prefixWord ++ tailWord_3487811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487811).length < 2 ^ (prefixWord ++ tailWord_3487811).sum := by decide
  have hdescent : baseEnd_3487811 < baseStart_3487811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487825 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 1, 1, 3]
def baseStart_3487825 : Nat := 118140960795 + 3487825 * 2 ^ 59
def prefixEnd_3487825 : Nat := 4983230072969 + 3 ^ 40 * 3487825 * 2
def baseEnd_3487825 : Nat := 1790930663767921602347291

theorem tailTrace_3487825 : CollatzResearch.WordTrace tailWord_3487825 prefixEnd_3487825 1790930663767921602347291 := by
  unfold tailWord_3487825
  simp only [CollatzResearch.WordTrace]
  refine ⟨127211428589213172931152929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84807619059475448620768619 127211428589213172931152929)
  ·
    refine ⟨95408571441909879698364697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127211428589213172931152929 95408571441909879698364697)
    ·
      refine ⟨71556428581432409773773523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95408571441909879698364697 71556428581432409773773523)
      ·
        refine ⟨107334642872148614660660285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71556428581432409773773523 107334642872148614660660285)
        ·
          refine ⟨40250491077055730497747607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107334642872148614660660285 40250491077055730497747607)
          ·
            refine ⟨60375736615583595746621411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40250491077055730497747607 60375736615583595746621411)
            ·
              refine ⟨90563604923375393619932117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60375736615583595746621411 90563604923375393619932117)
              ·
                refine ⟨2122584490391610787967159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90563604923375393619932117 2122584490391610787967159)
                ·
                  refine ⟨3183876735587416181950739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122584490391610787967159 3183876735587416181950739)
                  ·
                    refine ⟨4775815103381124272926109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183876735587416181950739 4775815103381124272926109)
                    ·
                      refine ⟨1790930663767921602347291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775815103381124272926109 1790930663767921602347291)
                      ·
                        rfl

theorem cell23_3487825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_3487825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487825 prefixEnd_3487825 := by exact prefixLift 3487825
  have htrace : WordTrace (prefixWord ++ tailWord_3487825) baseStart_3487825 baseEnd_3487825 := by
    simpa [prefixWord, tailWord_3487825, baseEnd_3487825] using wordTrace_append hprefix tailTrace_3487825
  have hstable : (prefixWord ++ tailWord_3487825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487825).length < 2 ^ (prefixWord ++ tailWord_3487825).sum := by decide
  have hdescent : baseEnd_3487825 < baseStart_3487825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487858 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3487858 : Nat := 118140960795 + 3487858 * 2 ^ 59
def prefixEnd_3487858 : Nat := 4983230072969 + 3 ^ 40 * 3487858 * 2
def baseEnd_3487858 : Nat := 596982536209839991078213

theorem tailTrace_3487858 : CollatzResearch.WordTrace tailWord_3487858 prefixEnd_3487858 596982536209839991078213 := by
  unfold tailWord_3487858
  simp only [CollatzResearch.WordTrace]
  refine ⟨31803158049523404891776057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84808421465395746378069485 31803158049523404891776057)
  ·
    refine ⟨23852368537142553668832043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31803158049523404891776057 23852368537142553668832043)
    ·
      refine ⟨35778552805713830503248065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23852368537142553668832043 35778552805713830503248065)
      ·
        refine ⟨26833914604285372877436049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35778552805713830503248065 26833914604285372877436049)
        ·
          refine ⟨20125435953214029658077037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26833914604285372877436049 20125435953214029658077037)
          ·
            refine ⟨7547038482455261121778889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20125435953214029658077037 7547038482455261121778889)
            ·
              refine ⟨5660278861841445841334167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7547038482455261121778889 5660278861841445841334167)
              ·
                refine ⟨8490418292762168762001251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660278861841445841334167 8490418292762168762001251)
                ·
                  refine ⟨12735627439143253143001877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8490418292762168762001251 12735627439143253143001877)
                  ·
                    refine ⟨596982536209839991078213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12735627439143253143001877 596982536209839991078213)
                    ·
                      rfl

theorem cell23_3487858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3487858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487858 prefixEnd_3487858 := by exact prefixLift 3487858
  have htrace : WordTrace (prefixWord ++ tailWord_3487858) baseStart_3487858 baseEnd_3487858 := by
    simpa [prefixWord, tailWord_3487858, baseEnd_3487858] using wordTrace_append hprefix tailTrace_3487858
  have hstable : (prefixWord ++ tailWord_3487858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487858).length < 2 ^ (prefixWord ++ tailWord_3487858).sum := by decide
  have hdescent : baseEnd_3487858 < baseStart_3487858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487865 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 5, 2, 2]
def baseStart_3487865 : Nat := 118140960795 + 3487865 * 2 ^ 59
def prefixEnd_3487865 : Nat := 4983230072969 + 3 ^ 40 * 3487865 * 2
def baseEnd_3487865 : Nat := 1790951202994101445847107

theorem tailTrace_3487865 : CollatzResearch.WordTrace tailWord_3487865 prefixEnd_3487865 1790951202994101445847107 := by
  unfold tailWord_3487865
  simp only [CollatzResearch.WordTrace]
  refine ⟨127212887509068259762609049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84808591672712173175072699 127212887509068259762609049)
  ·
    refine ⟨95409665631801194821956787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127212887509068259762609049 95409665631801194821956787)
    ·
      refine ⟨143114498447701792232935181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95409665631801194821956787 143114498447701792232935181)
      ·
        refine ⟨53667936917888172087350693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143114498447701792232935181 53667936917888172087350693)
        ·
          refine ⟨10062738172104032266378255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53667936917888172087350693 10062738172104032266378255)
          ·
            refine ⟨15094107258156048399567383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10062738172104032266378255 15094107258156048399567383)
            ·
              refine ⟨22641160887234072599351075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15094107258156048399567383 22641160887234072599351075)
              ·
                refine ⟨33961741330851108899026613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22641160887234072599351075 33961741330851108899026613)
                ·
                  refine ⟨3183913249767291459283745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33961741330851108899026613 3183913249767291459283745)
                  ·
                    refine ⟨2387934937325468594462809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3183913249767291459283745 2387934937325468594462809)
                    ·
                      refine ⟨1790951202994101445847107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2387934937325468594462809 1790951202994101445847107)
                      ·
                        rfl

theorem cell23_3487865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_3487865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487865 prefixEnd_3487865 := by exact prefixLift 3487865
  have htrace : WordTrace (prefixWord ++ tailWord_3487865) baseStart_3487865 baseEnd_3487865 := by
    simpa [prefixWord, tailWord_3487865, baseEnd_3487865] using wordTrace_append hprefix tailTrace_3487865
  have hstable : (prefixWord ++ tailWord_3487865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487865).length < 2 ^ (prefixWord ++ tailWord_3487865).sum := by decide
  have hdescent : baseEnd_3487865 < baseStart_3487865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487868 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_3487868 : Nat := 118140960795 + 3487868 * 2 ^ 59
def prefixEnd_3487868 : Nat := 4983230072969 + 3 ^ 40 * 3487868 * 2
def baseEnd_3487868 : Nat := 1790952743436064934109593

theorem tailTrace_3487868 : CollatzResearch.WordTrace tailWord_3487868 prefixEnd_3487868 1790952743436064934109593 := by
  unfold tailWord_3487868
  simp only [CollatzResearch.WordTrace]
  refine ⟨63606498464028695637484129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84808664618704927516645505 63606498464028695637484129)
  ·
    refine ⟨47704873848021521728113097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63606498464028695637484129 47704873848021521728113097)
    ·
      refine ⟨35778655386016141296084823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47704873848021521728113097 35778655386016141296084823)
      ·
        refine ⟨53667983079024211944127235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35778655386016141296084823 53667983079024211944127235)
        ·
          refine ⟨80501974618536317916190853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53667983079024211944127235 80501974618536317916190853)
          ·
            refine ⟨15094120240975559609285785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80501974618536317916190853 15094120240975559609285785)
            ·
              refine ⟨11320590180731669706964339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15094120240975559609285785 11320590180731669706964339)
              ·
                refine ⟨16980885271097504560446509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11320590180731669706964339 16980885271097504560446509)
                ·
                  refine ⟨6367831976661564210167441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16980885271097504560446509 6367831976661564210167441)
                  ·
                    refine ⟨4775873982496173157625581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6367831976661564210167441 4775873982496173157625581)
                    ·
                      refine ⟨1790952743436064934109593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4775873982496173157625581 1790952743436064934109593)
                      ·
                        rfl

theorem cell23_3487868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_3487868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487868 prefixEnd_3487868 := by exact prefixLift 3487868
  have htrace : WordTrace (prefixWord ++ tailWord_3487868) baseStart_3487868 baseEnd_3487868 := by
    simpa [prefixWord, tailWord_3487868, baseEnd_3487868] using wordTrace_append hprefix tailTrace_3487868
  have hstable : (prefixWord ++ tailWord_3487868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487868).length < 2 ^ (prefixWord ++ tailWord_3487868).sum := by decide
  have hdescent : baseEnd_3487868 < baseStart_3487868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487882 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_3487882 : Nat := 118140960795 + 3487882 * 2 ^ 59
def prefixEnd_3487882 : Nat := 4983230072969 + 3 ^ 40 * 3487882 * 2
def baseEnd_3487882 : Nat := 1790959932165227879334529

theorem tailTrace_3487882 : CollatzResearch.WordTrace tailWord_3487882 prefixEnd_3487882 1790959932165227879334529 := by
  unfold tailWord_3487882
  simp only [CollatzResearch.WordTrace]
  refine ⟨31803376887501667916494475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84809005033337781110651933 31803376887501667916494475)
  ·
    refine ⟨47705065331252501874741713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31803376887501667916494475 47705065331252501874741713)
    ·
      refine ⟨35778798998439376406056285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47705065331252501874741713 35778798998439376406056285)
      ·
        refine ⟨13417049624414766152271107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35778798998439376406056285 13417049624414766152271107)
        ·
          refine ⟨20125574436622149228406661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13417049624414766152271107 20125574436622149228406661)
          ·
            refine ⟨3773545206866652980326249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20125574436622149228406661 3773545206866652980326249)
            ·
              refine ⟨2830158905149989735244687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773545206866652980326249 2830158905149989735244687)
              ·
                refine ⟨4245238357724984602867031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830158905149989735244687 4245238357724984602867031)
                ·
                  refine ⟨6367857536587476904300547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245238357724984602867031 6367857536587476904300547)
                  ·
                    refine ⟨9551786304881215356450821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6367857536587476904300547 9551786304881215356450821)
                    ·
                      refine ⟨1790959932165227879334529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9551786304881215356450821 1790959932165227879334529)
                      ·
                        rfl

theorem cell23_3487882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_3487882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487882 prefixEnd_3487882 := by exact prefixLift 3487882
  have htrace : WordTrace (prefixWord ++ tailWord_3487882) baseStart_3487882 baseEnd_3487882 := by
    simpa [prefixWord, tailWord_3487882, baseEnd_3487882] using wordTrace_append hprefix tailTrace_3487882
  have hstable : (prefixWord ++ tailWord_3487882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487882).length < 2 ^ (prefixWord ++ tailWord_3487882).sum := by decide
  have hdescent : baseEnd_3487882 < baseStart_3487882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487892 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3487892 : Nat := 118140960795 + 3487892 * 2 ^ 59
def prefixEnd_3487892 : Nat := 4983230072969 + 3 ^ 40 * 3487892 * 2
def baseEnd_3487892 : Nat := 596988355657257613403161

theorem tailTrace_3487892 : CollatzResearch.WordTrace tailWord_3487892 prefixEnd_3487892 596988355657257613403161 := by
  unfold tailWord_3487892
  simp only [CollatzResearch.WordTrace]
  refine ⟨63606936139985221686920965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84809248186646962249227953 63606936139985221686920965)
  ·
    refine ⟨11926300526247229066297681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63606936139985221686920965 11926300526247229066297681)
    ·
      refine ⟨8944725394685421799723261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11926300526247229066297681 8944725394685421799723261)
      ·
        refine ⟨3354272023007033174896223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8944725394685421799723261 3354272023007033174896223)
        ·
          refine ⟨5031408034510549762344335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354272023007033174896223 5031408034510549762344335)
          ·
            refine ⟨7547112051765824643516503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031408034510549762344335 7547112051765824643516503)
            ·
              refine ⟨11320668077648736965274755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547112051765824643516503 11320668077648736965274755)
              ·
                refine ⟨16981002116473105447912133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11320668077648736965274755 16981002116473105447912133)
                ·
                  refine ⟨3183937896838707271483525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16981002116473105447912133 3183937896838707271483525)
                  ·
                    refine ⟨596988355657257613403161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183937896838707271483525 596988355657257613403161)
                    ·
                      rfl

theorem cell23_3487892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3487892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487892 prefixEnd_3487892 := by exact prefixLift 3487892
  have htrace : WordTrace (prefixWord ++ tailWord_3487892) baseStart_3487892 baseEnd_3487892 := by
    simpa [prefixWord, tailWord_3487892, baseEnd_3487892] using wordTrace_append hprefix tailTrace_3487892
  have hstable : (prefixWord ++ tailWord_3487892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487892).length < 2 ^ (prefixWord ++ tailWord_3487892).sum := by decide
  have hdescent : baseEnd_3487892 < baseStart_3487892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487941 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3487941 : Nat := 118140960795 + 3487941 * 2 ^ 59
def prefixEnd_3487941 : Nat := 4983230072969 + 3 ^ 40 * 3487941 * 2
def baseEnd_3487941 : Nat := 1790990227523843148496757

theorem tailTrace_3487941 : CollatzResearch.WordTrace tailWord_3487941 prefixEnd_3487941 1790990227523843148496757 := by
  unfold tailWord_3487941
  simp only [CollatzResearch.WordTrace]
  refine ⟨127215659456792924742375677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84810439637861949828250451 127215659456792924742375677)
  ·
    refine ⟨47705872296297346778390879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127215659456792924742375677 47705872296297346778390879)
    ·
      refine ⟨71558808444446020167586319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47705872296297346778390879 71558808444446020167586319)
      ·
        refine ⟨107338212666669030251379479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71558808444446020167586319 107338212666669030251379479)
        ·
          refine ⟨161007319000003545377069219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107338212666669030251379479 161007319000003545377069219)
          ·
            refine ⟨241510978500005318065603829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161007319000003545377069219 241510978500005318065603829)
            ·
              refine ⟨22641654234375498568650359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241510978500005318065603829 22641654234375498568650359)
              ·
                refine ⟨33962481351563247852975539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22641654234375498568650359 33962481351563247852975539)
                ·
                  refine ⟨50943722027344871779463309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33962481351563247852975539 50943722027344871779463309)
                  ·
                    refine ⟨19103895760254326917298741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50943722027344871779463309 19103895760254326917298741)
                    ·
                      refine ⟨1790990227523843148496757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19103895760254326917298741 1790990227523843148496757)
                      ·
                        rfl

theorem cell23_3487941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3487941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3487941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3487941 prefixEnd_3487941 := by exact prefixLift 3487941
  have htrace : WordTrace (prefixWord ++ tailWord_3487941) baseStart_3487941 baseEnd_3487941 := by
    simpa [prefixWord, tailWord_3487941, baseEnd_3487941] using wordTrace_append hprefix tailTrace_3487941
  have hstable : (prefixWord ++ tailWord_3487941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487941).length < 2 ^ (prefixWord ++ tailWord_3487941).sum := by decide
  have hdescent : baseEnd_3487941 < baseStart_3487941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488028 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3488028 : Nat := 118140960795 + 3488028 * 2 ^ 59
def prefixEnd_3488028 : Nat := 4983230072969 + 3 ^ 40 * 3488028 * 2
def baseEnd_3488028 : Nat := 1791034900340784308108857

theorem tailTrace_3488028 : CollatzResearch.WordTrace tailWord_3488028 prefixEnd_3488028 1791034900340784308108857 := by
  unfold tailWord_3488028
  simp only [CollatzResearch.WordTrace]
  refine ⟨63609416303738869300396369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84812555071651825733861825 63609416303738869300396369)
  ·
    refine ⟨47707062227804151975297277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63609416303738869300396369 47707062227804151975297277)
    ·
      refine ⟨17890148335426556990736479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47707062227804151975297277 17890148335426556990736479)
      ·
        refine ⟨26835222503139835486104719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17890148335426556990736479 26835222503139835486104719)
        ·
          refine ⟨40252833754709753229157079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26835222503139835486104719 40252833754709753229157079)
          ·
            refine ⟨60379250632064629843735619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40252833754709753229157079 60379250632064629843735619)
            ·
              refine ⟨90568875948096944765603429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60379250632064629843735619 90568875948096944765603429)
              ·
                refine ⟨16981664240268177143550643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90568875948096944765603429 16981664240268177143550643)
                ·
                  refine ⟨25472496360402265715325965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16981664240268177143550643 25472496360402265715325965)
                  ·
                    refine ⟨9552186135150849643247237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25472496360402265715325965 9552186135150849643247237)
                    ·
                      refine ⟨1791034900340784308108857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9552186135150849643247237 1791034900340784308108857)
                      ·
                        rfl

theorem cell23_3488028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3488028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488028 prefixEnd_3488028 := by exact prefixLift 3488028
  have htrace : WordTrace (prefixWord ++ tailWord_3488028) baseStart_3488028 baseEnd_3488028 := by
    simpa [prefixWord, tailWord_3488028, baseEnd_3488028] using wordTrace_append hprefix tailTrace_3488028
  have hstable : (prefixWord ++ tailWord_3488028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488028).length < 2 ^ (prefixWord ++ tailWord_3488028).sum := by decide
  have hdescent : baseEnd_3488028 < baseStart_3488028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488058 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_3488058 : Nat := 118140960795 + 3488058 * 2 ^ 59
def prefixEnd_3488058 : Nat := 4983230072969 + 3 ^ 40 * 3488058 * 2
def baseEnd_3488058 : Nat := 1791050304760419190733719

theorem tailTrace_3488058 : CollatzResearch.WordTrace tailWord_3488058 prefixEnd_3488058 1791050304760419190733719 := by
  unfold tailWord_3488058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31804981699342263431096207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84813284531579369149589885 31804981699342263431096207)
  ·
    refine ⟨47707472549013395146644311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31804981699342263431096207 47707472549013395146644311)
    ·
      refine ⟨71561208823520092719966467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47707472549013395146644311 71561208823520092719966467)
      ·
        refine ⟨107341813235280139079949701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71561208823520092719966467 107341813235280139079949701)
        ·
          refine ⟨20126589981615026077490569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107341813235280139079949701 20126589981615026077490569)
          ·
            refine ⟨15094942486211269558117927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20126589981615026077490569 15094942486211269558117927)
            ·
              refine ⟨22642413729316904337176891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15094942486211269558117927 22642413729316904337176891)
              ·
                refine ⟨33963620593975356505765337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22642413729316904337176891 33963620593975356505765337)
                ·
                  refine ⟨25472715445481517379324003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33963620593975356505765337 25472715445481517379324003)
                  ·
                    refine ⟨38209073168222276068986005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25472715445481517379324003 38209073168222276068986005)
                    ·
                      refine ⟨1791050304760419190733719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38209073168222276068986005 1791050304760419190733719)
                      ·
                        rfl

theorem cell23_3488058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_3488058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488058 prefixEnd_3488058 := by exact prefixLift 3488058
  have htrace : WordTrace (prefixWord ++ tailWord_3488058) baseStart_3488058 baseEnd_3488058 := by
    simpa [prefixWord, tailWord_3488058, baseEnd_3488058] using wordTrace_append hprefix tailTrace_3488058
  have hstable : (prefixWord ++ tailWord_3488058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488058).length < 2 ^ (prefixWord ++ tailWord_3488058).sum := by decide
  have hdescent : baseEnd_3488058 < baseStart_3488058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488062 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_3488062 : Nat := 118140960795 + 3488062 * 2 ^ 59
def prefixEnd_3488062 : Nat := 4983230072969 + 3 ^ 40 * 3488062 * 2
def baseEnd_3488062 : Nat := 1791052358683037175083701

theorem tailTrace_3488062 : CollatzResearch.WordTrace tailWord_3488062 prefixEnd_3488062 1791052358683037175083701 := by
  unfold tailWord_3488062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902509086169320300941305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84813381792903041605020293 15902509086169320300941305)
  ·
    refine ⟨11926881814626990225705979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15902509086169320300941305 11926881814626990225705979)
    ·
      refine ⟨17890322721940485338558969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11926881814626990225705979 17890322721940485338558969)
      ·
        refine ⟨13417742041455364003919227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17890322721940485338558969 13417742041455364003919227)
        ·
          refine ⟨20126613062183046005878841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13417742041455364003919227 20126613062183046005878841)
          ·
            refine ⟨15094959796637284504409131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20126613062183046005878841 15094959796637284504409131)
            ·
              refine ⟨22642439694955926756613697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15094959796637284504409131 22642439694955926756613697)
              ·
                refine ⟨16981829771216945067460273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22642439694955926756613697 16981829771216945067460273)
                ·
                  refine ⟨12736372328412708800595205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16981829771216945067460273 12736372328412708800595205)
                  ·
                    refine ⟨2388069811577382900111601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12736372328412708800595205 2388069811577382900111601)
                    ·
                      refine ⟨1791052358683037175083701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388069811577382900111601 1791052358683037175083701)
                      ·
                        rfl

theorem cell23_3488062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_3488062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488062 prefixEnd_3488062 := by exact prefixLift 3488062
  have htrace : WordTrace (prefixWord ++ tailWord_3488062) baseStart_3488062 baseEnd_3488062 := by
    simpa [prefixWord, tailWord_3488062, baseEnd_3488062] using wordTrace_append hprefix tailTrace_3488062
  have hstable : (prefixWord ++ tailWord_3488062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488062).length < 2 ^ (prefixWord ++ tailWord_3488062).sum := by decide
  have hdescent : baseEnd_3488062 < baseStart_3488062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488072 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 1, 4]
def baseStart_3488072 : Nat := 118140960795 + 3488072 * 2 ^ 59
def prefixEnd_3488072 : Nat := 4983230072969 + 3 ^ 40 * 3488072 * 2
def baseEnd_3488072 : Nat := 597019164496527378652885

theorem tailTrace_3488072 : CollatzResearch.WordTrace tailWord_3488072 prefixEnd_3488072 597019164496527378652885 := by
  unfold tailWord_3488072
  simp only [CollatzResearch.WordTrace]
  refine ⟨63610218709659167057697235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84813624946212222743596313 63610218709659167057697235)
  ·
    refine ⟨95415328064488750586545853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63610218709659167057697235 95415328064488750586545853)
    ·
      refine ⟨35780748024183281469954695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95415328064488750586545853 35780748024183281469954695)
      ·
        refine ⟨53671122036274922204932043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35780748024183281469954695 53671122036274922204932043)
        ·
          refine ⟨80506683054412383307398065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53671122036274922204932043 80506683054412383307398065)
          ·
            refine ⟨60380012290809287480548549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80506683054412383307398065 60380012290809287480548549)
            ·
              refine ⟨11321252304526741402602853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60380012290809287480548549 11321252304526741402602853)
              ·
                refine ⟨2122734807098764012988035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11321252304526741402602853 2122734807098764012988035)
                ·
                  refine ⟨3184102210648146019482053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122734807098764012988035 3184102210648146019482053)
                  ·
                    refine ⟨597019164496527378652885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184102210648146019482053 597019164496527378652885)
                    ·
                      rfl

theorem cell23_3488072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_3488072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488072 prefixEnd_3488072 := by exact prefixLift 3488072
  have htrace : WordTrace (prefixWord ++ tailWord_3488072) baseStart_3488072 baseEnd_3488072 := by
    simpa [prefixWord, tailWord_3488072, baseEnd_3488072] using wordTrace_append hprefix tailTrace_3488072
  have hstable : (prefixWord ++ tailWord_3488072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488072).length < 2 ^ (prefixWord ++ tailWord_3488072).sum := by decide
  have hdescent : baseEnd_3488072 < baseStart_3488072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488105 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 1, 5, 2]
def baseStart_3488105 : Nat := 118140960795 + 3488105 * 2 ^ 59
def prefixEnd_3488105 : Nat := 4983230072969 + 3 ^ 40 * 3488105 * 2
def baseEnd_3488105 : Nat := 1791074438351180506846003

theorem tailTrace_3488105 : CollatzResearch.WordTrace tailWord_3488105 prefixEnd_3488105 1791074438351180506846003 := by
  unfold tailWord_3488105
  simp only [CollatzResearch.WordTrace]
  refine ⟨127221641028198780751345769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84814427352132520500897179 127221641028198780751345769)
  ·
    refine ⟨95416230771149085563509327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127221641028198780751345769 95416230771149085563509327)
    ·
      refine ⟨143124346156723628345263991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95416230771149085563509327 143124346156723628345263991)
      ·
        refine ⟨214686519235085442517895987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143124346156723628345263991 214686519235085442517895987)
        ·
          refine ⟨322029778852628163776843981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214686519235085442517895987 322029778852628163776843981)
          ·
            refine ⟨120761167069735561416316493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322029778852628163776843981 120761167069735561416316493)
            ·
              refine ⟨45285437651150835531118685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120761167069735561416316493 45285437651150835531118685)
              ·
                refine ⟨16982039119181563324169507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45285437651150835531118685 16982039119181563324169507)
                ·
                  refine ⟨25473058678772344986254261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16982039119181563324169507 25473058678772344986254261)
                  ·
                    refine ⟨2388099251134907342461337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25473058678772344986254261 2388099251134907342461337)
                    ·
                      refine ⟨1791074438351180506846003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388099251134907342461337 1791074438351180506846003)
                      ·
                        rfl

theorem cell23_3488105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 5, 2].length) (baseStart_3488105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488105 prefixEnd_3488105 := by exact prefixLift 3488105
  have htrace : WordTrace (prefixWord ++ tailWord_3488105) baseStart_3488105 baseEnd_3488105 := by
    simpa [prefixWord, tailWord_3488105, baseEnd_3488105] using wordTrace_append hprefix tailTrace_3488105
  have hstable : (prefixWord ++ tailWord_3488105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488105).length < 2 ^ (prefixWord ++ tailWord_3488105).sum := by decide
  have hdescent : baseEnd_3488105 < baseStart_3488105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488106 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3488106 : Nat := 118140960795 + 3488106 * 2 ^ 59
def prefixEnd_3488106 : Nat := 4983230072969 + 3 ^ 40 * 3488106 * 2
def baseEnd_3488106 : Nat := 597024983943945000977833

theorem tailTrace_3488106 : CollatzResearch.WordTrace tailWord_3488106 prefixEnd_3488106 597024983943945000977833 := by
  unfold tailWord_3488106
  simp only [CollatzResearch.WordTrace]
  refine ⟨31805419375298789480533043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84814451667463438614754781 31805419375298789480533043)
  ·
    refine ⟨47708129062948184220799565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31805419375298789480533043 47708129062948184220799565)
    ·
      refine ⟨17890548398605569082799837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47708129062948184220799565 17890548398605569082799837)
      ·
        refine ⟨6708955649477088406049939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17890548398605569082799837 6708955649477088406049939)
        ·
          refine ⟨10063433474215632609074909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708955649477088406049939 10063433474215632609074909)
          ·
            refine ⟨3773787552830862228403091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10063433474215632609074909 3773787552830862228403091)
            ·
              refine ⟨5660681329246293342604637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773787552830862228403091 5660681329246293342604637)
              ·
                refine ⟨2122755498467360003476739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5660681329246293342604637 2122755498467360003476739)
                ·
                  refine ⟨3184133247701040005215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122755498467360003476739 3184133247701040005215109)
                  ·
                    refine ⟨597024983943945000977833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184133247701040005215109 597024983943945000977833)
                    ·
                      rfl

theorem cell23_3488106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3488106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488106 prefixEnd_3488106 := by exact prefixLift 3488106
  have htrace : WordTrace (prefixWord ++ tailWord_3488106) baseStart_3488106 baseEnd_3488106 := by
    simpa [prefixWord, tailWord_3488106, baseEnd_3488106] using wordTrace_append hprefix tailTrace_3488106
  have hstable : (prefixWord ++ tailWord_3488106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488106).length < 2 ^ (prefixWord ++ tailWord_3488106).sum := by decide
  have hdescent : baseEnd_3488106 < baseStart_3488106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488129 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3488129 : Nat := 118140960795 + 3488129 * 2 ^ 59
def prefixEnd_3488129 : Nat := 4983230072969 + 3 ^ 40 * 3488129 * 2
def baseEnd_3488129 : Nat := 1791086761886888412945893

theorem tailTrace_3488129 : CollatzResearch.WordTrace tailWord_3488129 prefixEnd_3488129 1791086761886888412945893 := by
  unfold tailWord_3488129
  simp only [CollatzResearch.WordTrace]
  refine ⟨127222516380111832850219441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84815010920074555233479627 127222516380111832850219441)
  ·
    refine ⟨95416887285083874637664581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127222516380111832850219441 95416887285083874637664581)
    ·
      refine ⟨17890666365953226494562109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95416887285083874637664581 17890666365953226494562109)
      ·
        refine ⟨6708999887232459935460791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17890666365953226494562109 6708999887232459935460791)
        ·
          refine ⟨10063499830848689903191187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708999887232459935460791 10063499830848689903191187)
          ·
            refine ⟨15095249746273034854786781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10063499830848689903191187 15095249746273034854786781)
            ·
              refine ⟨5660718654852388070545043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15095249746273034854786781 5660718654852388070545043)
              ·
                refine ⟨8491077982278582105817565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660718654852388070545043 8491077982278582105817565)
                ·
                  refine ⟨3184154243354468289681587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8491077982278582105817565 3184154243354468289681587)
                  ·
                    refine ⟨4776231365031702434522381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3184154243354468289681587 4776231365031702434522381)
                    ·
                      refine ⟨1791086761886888412945893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4776231365031702434522381 1791086761886888412945893)
                      ·
                        rfl

theorem cell23_3488129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3488129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488129 prefixEnd_3488129 := by exact prefixLift 3488129
  have htrace : WordTrace (prefixWord ++ tailWord_3488129) baseStart_3488129 baseEnd_3488129 := by
    simpa [prefixWord, tailWord_3488129, baseEnd_3488129] using wordTrace_append hprefix tailTrace_3488129
  have hstable : (prefixWord ++ tailWord_3488129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488129).length < 2 ^ (prefixWord ++ tailWord_3488129).sum := by decide
  have hdescent : baseEnd_3488129 < baseStart_3488129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488135 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3488135 : Nat := 118140960795 + 3488135 * 2 ^ 59
def prefixEnd_3488135 : Nat := 4983230072969 + 3 ^ 40 * 3488135 * 2
def baseEnd_3488135 : Nat := 1791089842770815389470865

theorem tailTrace_3488135 : CollatzResearch.WordTrace tailWord_3488135 prefixEnd_3488135 1791089842770815389470865 := by
  unfold tailWord_3488135
  simp only [CollatzResearch.WordTrace]
  refine ⟨127222735218090095874937859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84815156812060063916625239 127222735218090095874937859)
  ·
    refine ⟨190834102827135143812406789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127222735218090095874937859 190834102827135143812406789)
    ·
      refine ⟨35781394280087839464826273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190834102827135143812406789 35781394280087839464826273)
      ·
        refine ⟨26836045710065879598619705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35781394280087839464826273 26836045710065879598619705)
        ·
          refine ⟨20127034282549409698964779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26836045710065879598619705 20127034282549409698964779)
          ·
            refine ⟨30190551423824114548447169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20127034282549409698964779 30190551423824114548447169)
            ·
              refine ⟨22642913567868085911335377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30190551423824114548447169 22642913567868085911335377)
              ·
                refine ⟨16982185175901064433501533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22642913567868085911335377 16982185175901064433501533)
                ·
                  refine ⟨6368319440962899162563075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16982185175901064433501533 6368319440962899162563075)
                  ·
                    refine ⟨9552479161444348743844613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6368319440962899162563075 9552479161444348743844613)
                    ·
                      refine ⟨1791089842770815389470865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9552479161444348743844613 1791089842770815389470865)
                      ·
                        rfl

theorem cell23_3488135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3488135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488135 prefixEnd_3488135 := by exact prefixLift 3488135
  have htrace : WordTrace (prefixWord ++ tailWord_3488135) baseStart_3488135 baseEnd_3488135 := by
    simpa [prefixWord, tailWord_3488135, baseEnd_3488135] using wordTrace_append hprefix tailTrace_3488135
  have hstable : (prefixWord ++ tailWord_3488135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488135).length < 2 ^ (prefixWord ++ tailWord_3488135).sum := by decide
  have hdescent : baseEnd_3488135 < baseStart_3488135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488152 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3488152 : Nat := 118140960795 + 3488152 * 2 ^ 59
def prefixEnd_3488152 : Nat := 4983230072969 + 3 ^ 40 * 3488152 * 2
def baseEnd_3488152 : Nat := 1791098571941941822958287

theorem tailTrace_3488152 : CollatzResearch.WordTrace tailWord_3488152 prefixEnd_3488152 1791098571941941822958287 := by
  unfold tailWord_3488152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63611677629514253889153355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84815570172685671852204473 63611677629514253889153355)
  ·
    refine ⟨95417516444271380833730033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63611677629514253889153355 95417516444271380833730033)
    ·
      refine ⟨71563137333203535625297525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95417516444271380833730033 71563137333203535625297525)
      ·
        refine ⟨6709044124987831464871643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71563137333203535625297525 6709044124987831464871643)
        ·
          refine ⟨10063566187481747197307465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709044124987831464871643 10063566187481747197307465)
          ·
            refine ⟨7547674640611310397980599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10063566187481747197307465 7547674640611310397980599)
            ·
              refine ⟨11321511960916965596970899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547674640611310397980599 11321511960916965596970899)
              ·
                refine ⟨16982267941375448395456349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321511960916965596970899 16982267941375448395456349)
                ·
                  refine ⟨6368350478015793148296131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16982267941375448395456349 6368350478015793148296131)
                  ·
                    refine ⟨9552525717023689722444197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6368350478015793148296131 9552525717023689722444197)
                    ·
                      refine ⟨1791098571941941822958287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9552525717023689722444197 1791098571941941822958287)
                      ·
                        rfl

theorem cell23_3488152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3488152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488152 prefixEnd_3488152 := by exact prefixLift 3488152
  have htrace : WordTrace (prefixWord ++ tailWord_3488152) baseStart_3488152 baseEnd_3488152 := by
    simpa [prefixWord, tailWord_3488152, baseEnd_3488152] using wordTrace_append hprefix tailTrace_3488152
  have hstable : (prefixWord ++ tailWord_3488152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488152).length < 2 ^ (prefixWord ++ tailWord_3488152).sum := by decide
  have hdescent : baseEnd_3488152 < baseStart_3488152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488165 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3488165 : Nat := 118140960795 + 3488165 * 2 ^ 59
def prefixEnd_3488165 : Nat := 4983230072969 + 3 ^ 40 * 3488165 * 2
def baseEnd_3488165 : Nat := 1791105247190450272095727

theorem tailTrace_3488165 : CollatzResearch.WordTrace tailWord_3488165 prefixEnd_3488165 1791105247190450272095727 := by
  unfold tailWord_3488165
  simp only [CollatzResearch.WordTrace]
  refine ⟨127223829407981410998529949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84815886271987607332353299 127223829407981410998529949)
  ·
    refine ⟨47708936027993029124448731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127223829407981410998529949 47708936027993029124448731)
    ·
      refine ⟨71563404041989543686673097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47708936027993029124448731 71563404041989543686673097)
      ·
        refine ⟨53672553031492157765004823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71563404041989543686673097 53672553031492157765004823)
        ·
          refine ⟨80508829547238236647507235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53672553031492157765004823 80508829547238236647507235)
          ·
            refine ⟨120763244320857354971260853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80508829547238236647507235 120763244320857354971260853)
            ·
              refine ⟨11321554155080377028555705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120763244320857354971260853 11321554155080377028555705)
              ·
                refine ⟨8491165616310282771416779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11321554155080377028555705 8491165616310282771416779)
                ·
                  refine ⟨12736748424465424157125169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491165616310282771416779 12736748424465424157125169)
                  ·
                    refine ⟨9552561318349068117843877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12736748424465424157125169 9552561318349068117843877)
                    ·
                      refine ⟨1791105247190450272095727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9552561318349068117843877 1791105247190450272095727)
                      ·
                        rfl

theorem cell23_3488165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3488165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488165 prefixEnd_3488165 := by exact prefixLift 3488165
  have htrace : WordTrace (prefixWord ++ tailWord_3488165) baseStart_3488165 baseEnd_3488165 := by
    simpa [prefixWord, tailWord_3488165, baseEnd_3488165] using wordTrace_append hprefix tailTrace_3488165
  have hstable : (prefixWord ++ tailWord_3488165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488165).length < 2 ^ (prefixWord ++ tailWord_3488165).sum := by decide
  have hdescent : baseEnd_3488165 < baseStart_3488165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488180 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3488180 : Nat := 118140960795 + 3488180 * 2 ^ 59
def prefixEnd_3488180 : Nat := 4983230072969 + 3 ^ 40 * 3488180 * 2
def baseEnd_3488180 : Nat := 1791112949400267713408159

theorem tailTrace_3488180 : CollatzResearch.WordTrace tailWord_3488180 prefixEnd_3488180 1791112949400267713408159 := by
  unfold tailWord_3488180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63612188251463534280162997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84816251001951379040217329 63612188251463534280162997)
  ·
    refine ⟨5963642648574706338765281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63612188251463534280162997 5963642648574706338765281)
    ·
      refine ⟨4472731986431029754073961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5963642648574706338765281 4472731986431029754073961)
      ·
        refine ⟨3354548989823272315555471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4472731986431029754073961 3354548989823272315555471)
        ·
          refine ⟨5031823484734908473333207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354548989823272315555471 5031823484734908473333207)
          ·
            refine ⟨7547735227102362709999811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031823484734908473333207 7547735227102362709999811)
            ·
              refine ⟨11321602840653544064999717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547735227102362709999811 11321602840653544064999717)
              ·
                refine ⟨2122800532622539512187447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11321602840653544064999717 2122800532622539512187447)
                ·
                  refine ⟨3184200798933809268281171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122800532622539512187447 3184200798933809268281171)
                  ·
                    refine ⟨4776301198400713902421757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3184200798933809268281171 4776301198400713902421757)
                    ·
                      refine ⟨1791112949400267713408159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4776301198400713902421757 1791112949400267713408159)
                      ·
                        rfl

theorem cell23_3488180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3488180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488180 prefixEnd_3488180 := by exact prefixLift 3488180
  have htrace : WordTrace (prefixWord ++ tailWord_3488180) baseStart_3488180 baseEnd_3488180 := by
    simpa [prefixWord, tailWord_3488180, baseEnd_3488180] using wordTrace_append hprefix tailTrace_3488180
  have hstable : (prefixWord ++ tailWord_3488180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488180).length < 2 ^ (prefixWord ++ tailWord_3488180).sum := by decide
  have hdescent : baseEnd_3488180 < baseStart_3488180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488202 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_3488202 : Nat := 118140960795 + 3488202 * 2 ^ 59
def prefixEnd_3488202 : Nat := 4983230072969 + 3 ^ 40 * 3488202 * 2
def baseEnd_3488202 : Nat := 1791124245974666627333057

theorem tailTrace_3488202 : CollatzResearch.WordTrace tailWord_3488202 prefixEnd_3488202 1791124245974666627333057 := by
  unfold tailWord_3488202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31806294727211841579406715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84816785939231577545084573 31806294727211841579406715)
  ·
    refine ⟨47709442090817762369110073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31806294727211841579406715 47709442090817762369110073)
    ·
      refine ⟨35782081568113321776832555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47709442090817762369110073 35782081568113321776832555)
      ·
        refine ⟨53673122352169982665248833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35782081568113321776832555 53673122352169982665248833)
        ·
          refine ⟨40254841764127486998936625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53673122352169982665248833 40254841764127486998936625)
          ·
            refine ⟨30191131323095615249202469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40254841764127486998936625 30191131323095615249202469)
            ·
              refine ⟨5660837123080427859225463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30191131323095615249202469 5660837123080427859225463)
              ·
                refine ⟨8491255684620641788838195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660837123080427859225463 8491255684620641788838195)
                ·
                  refine ⟨12736883526930962683257293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491255684620641788838195 12736883526930962683257293)
                  ·
                    refine ⟨4776331322599111006221485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12736883526930962683257293 4776331322599111006221485)
                    ·
                      refine ⟨1791124245974666627333057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4776331322599111006221485 1791124245974666627333057)
                      ·
                        rfl

theorem cell23_3488202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_3488202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488202 prefixEnd_3488202 := by exact prefixLift 3488202
  have htrace : WordTrace (prefixWord ++ tailWord_3488202) baseStart_3488202 baseEnd_3488202 := by
    simpa [prefixWord, tailWord_3488202, baseEnd_3488202] using wordTrace_append hprefix tailTrace_3488202
  have hstable : (prefixWord ++ tailWord_3488202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488202).length < 2 ^ (prefixWord ++ tailWord_3488202).sum := by decide
  have hdescent : baseEnd_3488202 < baseStart_3488202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488208 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_3488208 : Nat := 118140960795 + 3488208 * 2 ^ 59
def prefixEnd_3488208 : Nat := 4983230072969 + 3 ^ 40 * 3488208 * 2
def baseEnd_3488208 : Nat := 1791127326858593603858029

theorem tailTrace_3488208 : CollatzResearch.WordTrace tailWord_3488208 prefixEnd_3488208 1791127326858593603858029 := by
  unfold tailWord_3488208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63612698873412814671172639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84816931831217086228230185 63612698873412814671172639)
  ·
    refine ⟨95419048310119222006758959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63612698873412814671172639 95419048310119222006758959)
    ·
      refine ⟨143128572465178833010138439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95419048310119222006758959 143128572465178833010138439)
      ·
        refine ⟨214692858697768249515207659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143128572465178833010138439 214692858697768249515207659)
        ·
          refine ⟨322039288046652374272811489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214692858697768249515207659 322039288046652374272811489)
          ·
            refine ⟨241529466034989280704608617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322039288046652374272811489 241529466034989280704608617)
            ·
              refine ⟨181147099526241960528456463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241529466034989280704608617 181147099526241960528456463)
              ·
                refine ⟨271720649289362940792684695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181147099526241960528456463 271720649289362940792684695)
                ·
                  refine ⟨407580973934044411189027043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271720649289362940792684695 407580973934044411189027043)
                  ·
                    refine ⟨611371460901066616783540565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407580973934044411189027043 611371460901066616783540565)
                    ·
                      refine ⟨1791127326858593603858029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 611371460901066616783540565 1791127326858593603858029)
                      ·
                        rfl

theorem cell23_3488208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_3488208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488208 prefixEnd_3488208 := by exact prefixLift 3488208
  have htrace : WordTrace (prefixWord ++ tailWord_3488208) baseStart_3488208 baseEnd_3488208 := by
    simpa [prefixWord, tailWord_3488208, baseEnd_3488208] using wordTrace_append hprefix tailTrace_3488208
  have hstable : (prefixWord ++ tailWord_3488208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488208).length < 2 ^ (prefixWord ++ tailWord_3488208).sum := by decide
  have hdescent : baseEnd_3488208 < baseStart_3488208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488255 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_3488255 : Nat := 118140960795 + 3488255 * 2 ^ 59
def prefixEnd_3488255 : Nat := 4983230072969 + 3 ^ 40 * 3488255 * 2
def baseEnd_3488255 : Nat := 1791151460449354919970313

theorem tailTrace_3488255 : CollatzResearch.WordTrace tailWord_3488255 prefixEnd_3488255 1791151460449354919970313 := by
  unfold tailWord_3488255
  simp only [CollatzResearch.WordTrace]
  refine ⟨127227111977655356369306219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84818074651770237579537479 127227111977655356369306219)
  ·
    refine ⟨190840667966483034553959329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127227111977655356369306219 190840667966483034553959329)
    ·
      refine ⟨143130500974862275915469497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190840667966483034553959329 143130500974862275915469497)
      ·
        refine ⟨107347875731146706936602123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143130500974862275915469497 107347875731146706936602123)
        ·
          refine ⟨161021813596720060404903185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107347875731146706936602123 161021813596720060404903185)
          ·
            refine ⟨120766360197540045303677389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161021813596720060404903185 120766360197540045303677389)
            ·
              refine ⟨45287385074077516988879021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120766360197540045303677389 45287385074077516988879021)
              ·
                refine ⟨16982769402779068870829633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45287385074077516988879021 16982769402779068870829633)
                ·
                  refine ⟨12737077052084301653122225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16982769402779068870829633 12737077052084301653122225)
                  ·
                    refine ⟨9552807789063226239841669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12737077052084301653122225 9552807789063226239841669)
                    ·
                      refine ⟨1791151460449354919970313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9552807789063226239841669 1791151460449354919970313)
                      ·
                        rfl

theorem cell23_3488255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_3488255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488255 prefixEnd_3488255 := by exact prefixLift 3488255
  have htrace : WordTrace (prefixWord ++ tailWord_3488255) baseStart_3488255 baseEnd_3488255 := by
    simpa [prefixWord, tailWord_3488255, baseEnd_3488255] using wordTrace_append hprefix tailTrace_3488255
  have hstable : (prefixWord ++ tailWord_3488255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488255).length < 2 ^ (prefixWord ++ tailWord_3488255).sum := by decide
  have hdescent : baseEnd_3488255 < baseStart_3488255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488279 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3488279 : Nat := 118140960795 + 3488279 * 2 ^ 59
def prefixEnd_3488279 : Nat := 4983230072969 + 3 ^ 40 * 3488279 * 2
def baseEnd_3488279 : Nat := 1791163783985062826070203

theorem tailTrace_3488279 : CollatzResearch.WordTrace tailWord_3488279 prefixEnd_3488279 1791163783985062826070203 := by
  unfold tailWord_3488279
  simp only [CollatzResearch.WordTrace]
  refine ⟨127227987329568408468179891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84818658219712272312119927 127227987329568408468179891)
  ·
    refine ⟨190841980994352612702269837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127227987329568408468179891 190841980994352612702269837)
    ·
      refine ⟨71565742872882229763351189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190841980994352612702269837 71565742872882229763351189)
      ·
        refine ⟨3354644197166354520157087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71565742872882229763351189 3354644197166354520157087)
        ·
          refine ⟨5031966295749531780235631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354644197166354520157087 5031966295749531780235631)
          ·
            refine ⟨7547949443624297670353447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031966295749531780235631 7547949443624297670353447)
            ·
              refine ⟨11321924165436446505530171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547949443624297670353447 11321924165436446505530171)
              ·
                refine ⟨16982886248154669758295257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321924165436446505530171 16982886248154669758295257)
                ·
                  refine ⟨12737164686116002318721443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16982886248154669758295257 12737164686116002318721443)
                  ·
                    refine ⟨19105747029174003478082165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12737164686116002318721443 19105747029174003478082165)
                    ·
                      refine ⟨1791163783985062826070203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19105747029174003478082165 1791163783985062826070203)
                      ·
                        rfl

theorem cell23_3488279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3488279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488279 prefixEnd_3488279 := by exact prefixLift 3488279
  have htrace : WordTrace (prefixWord ++ tailWord_3488279) baseStart_3488279 baseEnd_3488279 := by
    simpa [prefixWord, tailWord_3488279, baseEnd_3488279] using wordTrace_append hprefix tailTrace_3488279
  have hstable : (prefixWord ++ tailWord_3488279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488279).length < 2 ^ (prefixWord ++ tailWord_3488279).sum := by decide
  have hdescent : baseEnd_3488279 < baseStart_3488279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488305 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3488305 : Nat := 118140960795 + 3488305 * 2 ^ 59
def prefixEnd_3488305 : Nat := 4983230072969 + 3 ^ 40 * 3488305 * 2
def baseEnd_3488305 : Nat := 1791177134482079724345083

theorem tailTrace_3488305 : CollatzResearch.WordTrace tailWord_3488305 prefixEnd_3488305 1791177134482079724345083 := by
  unfold tailWord_3488305
  simp only [CollatzResearch.WordTrace]
  refine ⟨127228935627474214908626369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84819290418316143272417579 127228935627474214908626369)
  ·
    refine ⟨95421701720605661181469777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127228935627474214908626369 95421701720605661181469777)
    ·
      refine ⟨71566276290454245886102333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95421701720605661181469777 71566276290454245886102333)
      ·
        refine ⟨26837353608920342207288375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71566276290454245886102333 26837353608920342207288375)
        ·
          refine ⟨40256030413380513310932563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26837353608920342207288375 40256030413380513310932563)
          ·
            refine ⟨60384045620070769966398845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40256030413380513310932563 60384045620070769966398845)
            ·
              refine ⟨22644017107526538737399567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60384045620070769966398845 22644017107526538737399567)
              ·
                refine ⟨33966025661289808106099351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22644017107526538737399567 33966025661289808106099351)
                ·
                  refine ⟨50949038491934712159149027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33966025661289808106099351 50949038491934712159149027)
                  ·
                    refine ⟨76423557737902068238723541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50949038491934712159149027 76423557737902068238723541)
                    ·
                      refine ⟨1791177134482079724345083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76423557737902068238723541 1791177134482079724345083)
                      ·
                        rfl

theorem cell23_3488305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3488305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488305 prefixEnd_3488305 := by exact prefixLift 3488305
  have htrace : WordTrace (prefixWord ++ tailWord_3488305) baseStart_3488305 baseEnd_3488305 := by
    simpa [prefixWord, tailWord_3488305, baseEnd_3488305] using wordTrace_append hprefix tailTrace_3488305
  have hstable : (prefixWord ++ tailWord_3488305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488305).length < 2 ^ (prefixWord ++ tailWord_3488305).sum := by decide
  have hdescent : baseEnd_3488305 < baseStart_3488305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488310 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3488310 : Nat := 118140960795 + 3488310 * 2 ^ 59
def prefixEnd_3488310 : Nat := 4983230072969 + 3 ^ 40 * 3488310 * 2
def baseEnd_3488310 : Nat := 1791179701885352204782561

theorem tailTrace_3488310 : CollatzResearch.WordTrace tailWord_3488310 prefixEnd_3488310 1791179701885352204782561 := by
  unfold tailWord_3488310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951819874528506297659899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84819411994970733841705589 7951819874528506297659899)
  ·
    refine ⟨11927729811792759446489849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7951819874528506297659899 11927729811792759446489849)
    ·
      refine ⟨8945797358844569584867387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11927729811792759446489849 8945797358844569584867387)
      ·
        refine ⟨13418696038266854377301081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945797358844569584867387 13418696038266854377301081)
        ·
          refine ⟨10064022028700140782975811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13418696038266854377301081 10064022028700140782975811)
          ·
            refine ⟨15096033043050211174463717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064022028700140782975811 15096033043050211174463717)
            ·
              refine ⟨2830506195571914595211947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15096033043050211174463717 2830506195571914595211947)
              ·
                refine ⟨4245759293357871892817921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830506195571914595211947 4245759293357871892817921)
                ·
                  refine ⟨3184319470018403919613441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4245759293357871892817921 3184319470018403919613441)
                  ·
                    refine ⟨2388239602513802939710081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3184319470018403919613441 2388239602513802939710081)
                    ·
                      refine ⟨1791179701885352204782561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388239602513802939710081 1791179701885352204782561)
                      ·
                        rfl

theorem cell23_3488310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3488310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488310 prefixEnd_3488310 := by exact prefixLift 3488310
  have htrace : WordTrace (prefixWord ++ tailWord_3488310) baseStart_3488310 baseEnd_3488310 := by
    simpa [prefixWord, tailWord_3488310, baseEnd_3488310] using wordTrace_append hprefix tailTrace_3488310
  have hstable : (prefixWord ++ tailWord_3488310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488310).length < 2 ^ (prefixWord ++ tailWord_3488310).sum := by decide
  have hdescent : baseEnd_3488310 < baseStart_3488310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488350 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3488350 : Nat := 118140960795 + 3488350 * 2 ^ 59
def prefixEnd_3488350 : Nat := 4983230072969 + 3 ^ 40 * 3488350 * 2
def baseEnd_3488350 : Nat := 199022249012392449809153

theorem tailTrace_3488350 : CollatzResearch.WordTrace tailWord_3488350 prefixEnd_3488350 199022249012392449809153 := by
  unfold tailWord_3488350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903822114038898449251813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84820384608207458396009669 15903822114038898449251813)
  ·
    refine ⟨2981966646382293459234715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15903822114038898449251813 2981966646382293459234715)
    ·
      refine ⟨4472949969573440188852073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981966646382293459234715 4472949969573440188852073)
      ·
        refine ⟨3354712477180080141639055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4472949969573440188852073 3354712477180080141639055)
        ·
          refine ⟨5032068715770120212458583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354712477180080141639055 5032068715770120212458583)
          ·
            refine ⟨7548103073655180318687875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5032068715770120212458583 7548103073655180318687875)
            ·
              refine ⟨11322154610482770478031813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7548103073655180318687875 11322154610482770478031813)
              ·
                refine ⟨2122903989465519464630965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11322154610482770478031813 2122903989465519464630965)
                ·
                  refine ⟨199022249012392449809153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122903989465519464630965 199022249012392449809153)
                  ·
                    rfl

theorem cell23_3488350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3488350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488350 prefixEnd_3488350 := by exact prefixLift 3488350
  have htrace : WordTrace (prefixWord ++ tailWord_3488350) baseStart_3488350 baseEnd_3488350 := by
    simpa [prefixWord, tailWord_3488350, baseEnd_3488350] using wordTrace_append hprefix tailTrace_3488350
  have hstable : (prefixWord ++ tailWord_3488350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488350).length < 2 ^ (prefixWord ++ tailWord_3488350).sum := by decide
  have hdescent : baseEnd_3488350 < baseStart_3488350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488366 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_3488366 : Nat := 118140960795 + 3488366 * 2 ^ 59
def prefixEnd_3488366 : Nat := 4983230072969 + 3 ^ 40 * 3488366 * 2
def baseEnd_3488366 : Nat := 1791208456802003985682303

theorem tailTrace_3488366 : CollatzResearch.WordTrace tailWord_3488366 prefixEnd_3488366 1791208456802003985682303 := by
  unfold tailWord_3488366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903895060031652790824619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84820773653502148217731301 15903895060031652790824619)
  ·
    refine ⟨23855842590047479186236929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15903895060031652790824619 23855842590047479186236929)
    ·
      refine ⟨17891881942535609389677697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23855842590047479186236929 17891881942535609389677697)
      ·
        refine ⟨13418911456901707042258273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17891881942535609389677697 13418911456901707042258273)
        ·
          refine ⟨10064183592676280281693705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13418911456901707042258273 10064183592676280281693705)
          ·
            refine ⟨7548137694507210211270279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10064183592676280281693705 7548137694507210211270279)
            ·
              refine ⟨11322206541760815316905419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7548137694507210211270279 11322206541760815316905419)
              ·
                refine ⟨16983309812641222975358129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11322206541760815316905419 16983309812641222975358129)
                ·
                  refine ⟨12737482359480917231518597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16983309812641222975358129 12737482359480917231518597)
                  ·
                    refine ⟨2388277942402671980909737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12737482359480917231518597 2388277942402671980909737)
                    ·
                      refine ⟨1791208456802003985682303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388277942402671980909737 1791208456802003985682303)
                      ·
                        rfl

theorem cell23_3488366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_3488366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488366 prefixEnd_3488366 := by exact prefixLift 3488366
  have htrace : WordTrace (prefixWord ++ tailWord_3488366) baseStart_3488366 baseEnd_3488366 := by
    simpa [prefixWord, tailWord_3488366, baseEnd_3488366] using wordTrace_append hprefix tailTrace_3488366
  have hstable : (prefixWord ++ tailWord_3488366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488366).length < 2 ^ (prefixWord ++ tailWord_3488366).sum := by decide
  have hdescent : baseEnd_3488366 < baseStart_3488366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488409 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 4, 3, 2]
def baseStart_3488409 : Nat := 118140960795 + 3488409 * 2 ^ 59
def prefixEnd_3488409 : Nat := 4983230072969 + 3 ^ 40 * 3488409 * 2
def baseEnd_3488409 : Nat := 1791230536470147317444605

theorem tailTrace_3488409 : CollatzResearch.WordTrace tailWord_3488409 prefixEnd_3488409 1791230536470147317444605 := by
  unfold tailWord_3488409
  simp only [CollatzResearch.WordTrace]
  refine ⟨127232728819097440670412281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84821819212731627113608187 127232728819097440670412281)
  ·
    refine ⟨95424546614323080502809211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127232728819097440670412281 95424546614323080502809211)
    ·
      refine ⟨143136819921484620754213817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95424546614323080502809211 143136819921484620754213817)
      ·
        refine ⟨107352614941113465565660363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143136819921484620754213817 107352614941113465565660363)
        ·
          refine ⟨161028922411670198348490545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107352614941113465565660363 161028922411670198348490545)
          ·
            refine ⟨120771691808752648761367909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161028922411670198348490545 120771691808752648761367909)
            ·
              refine ⟨22644692214141121642756483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120771691808752648761367909 22644692214141121642756483)
              ·
                refine ⟨33967038321211682464134725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22644692214141121642756483 33967038321211682464134725)
                ·
                  refine ⟨6368819685227190462025261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33967038321211682464134725 6368819685227190462025261)
                  ·
                    refine ⟨2388307381960196423259473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6368819685227190462025261 2388307381960196423259473)
                    ·
                      refine ⟨1791230536470147317444605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388307381960196423259473 1791230536470147317444605)
                      ·
                        rfl

theorem cell23_3488409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_3488409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488409 prefixEnd_3488409 := by exact prefixLift 3488409
  have htrace : WordTrace (prefixWord ++ tailWord_3488409) baseStart_3488409 baseEnd_3488409 := by
    simpa [prefixWord, tailWord_3488409, baseEnd_3488409] using wordTrace_append hprefix tailTrace_3488409
  have hstable : (prefixWord ++ tailWord_3488409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488409).length < 2 ^ (prefixWord ++ tailWord_3488409).sum := by decide
  have hdescent : baseEnd_3488409 < baseStart_3488409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488423 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 6]
def baseStart_3488423 : Nat := 118140960795 + 3488423 * 2 ^ 59
def prefixEnd_3488423 : Nat := 4983230072969 + 3 ^ 40 * 3488423 * 2
def baseEnd_3488423 : Nat := 199026413911034473629949

theorem tailTrace_3488423 : CollatzResearch.WordTrace tailWord_3488423 prefixEnd_3488423 199026413911034473629949 := by
  unfold tailWord_3488423
  simp only [CollatzResearch.WordTrace]
  refine ⟨127233239441046721061421923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84822159627364480707614615 127233239441046721061421923)
  ·
    refine ⟨190849859161570081592132885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127233239441046721061421923 190849859161570081592132885)
    ·
      refine ⟨8946087148198597574631229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190849859161570081592132885 8946087148198597574631229)
      ·
        refine ⟨3354782680574474090486711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8946087148198597574631229 3354782680574474090486711)
        ·
          refine ⟨5032174020861711135730067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354782680574474090486711 5032174020861711135730067)
          ·
            refine ⟨7548261031292566703595101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5032174020861711135730067 7548261031292566703595101)
            ·
              refine ⟨2830597886734712513848163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7548261031292566703595101 2830597886734712513848163)
              ·
                refine ⟨4245896830102068770772245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830597886734712513848163 4245896830102068770772245)
                ·
                  refine ⟨199026413911034473629949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4245896830102068770772245 199026413911034473629949)
                  ·
                    rfl

theorem cell23_3488423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 6].length) (baseStart_3488423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488423 prefixEnd_3488423 := by exact prefixLift 3488423
  have htrace : WordTrace (prefixWord ++ tailWord_3488423) baseStart_3488423 baseEnd_3488423 := by
    simpa [prefixWord, tailWord_3488423, baseEnd_3488423] using wordTrace_append hprefix tailTrace_3488423
  have hstable : (prefixWord ++ tailWord_3488423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488423).length < 2 ^ (prefixWord ++ tailWord_3488423).sum := by decide
  have hdescent : baseEnd_3488423 < baseStart_3488423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488442 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_3488442 : Nat := 118140960795 + 3488442 * 2 ^ 59
def prefixEnd_3488442 : Nat := 4983230072969 + 3 ^ 40 * 3488442 * 2
def baseEnd_3488442 : Nat := 1791247481331745688331953

theorem tailTrace_3488442 : CollatzResearch.WordTrace tailWord_3488442 prefixEnd_3488442 1791247481331745688331953 := by
  unfold tailWord_3488442
  simp only [CollatzResearch.WordTrace]
  refine ⟨31808483106994471826590895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84822621618651924870909053 31808483106994471826590895)
  ·
    refine ⟨47712724660491707739886343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31808483106994471826590895 47712724660491707739886343)
    ·
      refine ⟨71569086990737561609829515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47712724660491707739886343 71569086990737561609829515)
      ·
        refine ⟨107353630486106342414744273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71569086990737561609829515 107353630486106342414744273)
        ·
          refine ⟨80515222864579756811058205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107353630486106342414744273 80515222864579756811058205)
          ·
            refine ⟨30193208574217408804146827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80515222864579756811058205 30193208574217408804146827)
            ·
              refine ⟨45289812861326113206220241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30193208574217408804146827 45289812861326113206220241)
              ·
                refine ⟨33967359645994584904665181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45289812861326113206220241 33967359645994584904665181)
                ·
                  refine ⟨12737759867247969339249443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33967359645994584904665181 12737759867247969339249443)
                  ·
                    refine ⟨19106639800871954008874165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12737759867247969339249443 19106639800871954008874165)
                    ·
                      refine ⟨1791247481331745688331953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19106639800871954008874165 1791247481331745688331953)
                      ·
                        rfl

theorem cell23_3488442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_3488442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488442 prefixEnd_3488442 := by exact prefixLift 3488442
  have htrace : WordTrace (prefixWord ++ tailWord_3488442) baseStart_3488442 baseEnd_3488442 := by
    simpa [prefixWord, tailWord_3488442, baseEnd_3488442] using wordTrace_append hprefix tailTrace_3488442
  have hstable : (prefixWord ++ tailWord_3488442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488442).length < 2 ^ (prefixWord ++ tailWord_3488442).sum := by decide
  have hdescent : baseEnd_3488442 < baseStart_3488442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488462 : List Nat := [4, 1, 1, 1, 3, 2, 11]
def baseStart_3488462 : Nat := 118140960795 + 3488462 * 2 ^ 59
def prefixEnd_3488462 : Nat := 4983230072969 + 3 ^ 40 * 3488462 * 2
def baseEnd_3488462 : Nat := 22114293221541180371381

theorem tailTrace_3488462 : CollatzResearch.WordTrace tailWord_3488462 prefixEnd_3488462 22114293221541180371381 := by
  unfold tailWord_3488462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904332735988178840261455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84823107925270287148061093 15904332735988178840261455)
  ·
    refine ⟨23856499103982268260392183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15904332735988178840261455 23856499103982268260392183)
    ·
      refine ⟨35784748655973402390588275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23856499103982268260392183 35784748655973402390588275)
      ·
        refine ⟨53677122983960103585882413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35784748655973402390588275 53677122983960103585882413)
        ·
          refine ⟨20128921118985038844705905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53677122983960103585882413 20128921118985038844705905)
          ·
            refine ⟨15096690839238779133529429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20128921118985038844705905 15096690839238779133529429)
            ·
              refine ⟨22114293221541180371381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15096690839238779133529429 22114293221541180371381)
              ·
                rfl

theorem cell23_3488462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 11].length) (baseStart_3488462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488462 prefixEnd_3488462 := by exact prefixLift 3488462
  have htrace : WordTrace (prefixWord ++ tailWord_3488462) baseStart_3488462 baseEnd_3488462 := by
    simpa [prefixWord, tailWord_3488462, baseEnd_3488462] using wordTrace_append hprefix tailTrace_3488462
  have hstable : (prefixWord ++ tailWord_3488462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488462).length < 2 ^ (prefixWord ++ tailWord_3488462).sum := by decide
  have hdescent : baseEnd_3488462 < baseStart_3488462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488476 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3488476 : Nat := 118140960795 + 3488476 * 2 ^ 59
def prefixEnd_3488476 : Nat := 4983230072969 + 3 ^ 40 * 3488476 * 2
def baseEnd_3488476 : Nat := 1791264939673998555306797

theorem tailTrace_3488476 : CollatzResearch.WordTrace tailWord_3488476 prefixEnd_3488476 1791264939673998555306797 := by
  unfold tailWord_3488476
  simp only [CollatzResearch.WordTrace]
  refine ⟨63617586254927355556550641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84823448339903140742067521 63617586254927355556550641)
  ·
    refine ⟨47713189691195516667412981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63617586254927355556550641 47713189691195516667412981)
    ·
      refine ⟨4473111533549579687569967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47713189691195516667412981 4473111533549579687569967)
      ·
        refine ⟨6709667300324369531354951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473111533549579687569967 6709667300324369531354951)
        ·
          refine ⟨10064500950486554297032427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709667300324369531354951 10064500950486554297032427)
          ·
            refine ⟨15096751425729831445548641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064500950486554297032427 15096751425729831445548641)
            ·
              refine ⟨11322563569297373584161481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15096751425729831445548641 11322563569297373584161481)
              ·
                refine ⟨8491922676973030188121111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11322563569297373584161481 8491922676973030188121111)
                ·
                  refine ⟨12737884015459545282181667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491922676973030188121111 12737884015459545282181667)
                  ·
                    refine ⟨19106826023189317923272501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12737884015459545282181667 19106826023189317923272501)
                    ·
                      refine ⟨1791264939673998555306797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19106826023189317923272501 1791264939673998555306797)
                      ·
                        rfl

theorem cell23_3488476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3488476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488476 prefixEnd_3488476 := by exact prefixLift 3488476
  have htrace : WordTrace (prefixWord ++ tailWord_3488476) baseStart_3488476 baseEnd_3488476 := by
    simpa [prefixWord, tailWord_3488476, baseEnd_3488476] using wordTrace_append hprefix tailTrace_3488476
  have hstable : (prefixWord ++ tailWord_3488476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488476).length < 2 ^ (prefixWord ++ tailWord_3488476).sum := by decide
  have hdescent : baseEnd_3488476 < baseStart_3488476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488483 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 2, 4]
def baseStart_3488483 : Nat := 118140960795 + 3488483 * 2 ^ 59
def prefixEnd_3488483 : Nat := 4983230072969 + 3 ^ 40 * 3488483 * 2
def baseEnd_3488483 : Nat := 597089511346193342639755

theorem tailTrace_3488483 : CollatzResearch.WordTrace tailWord_3488483 prefixEnd_3488483 597089511346193342639755 := by
  unfold tailWord_3488483
  simp only [CollatzResearch.WordTrace]
  refine ⟨127235427820829351308606103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84823618547219567539070735 127235427820829351308606103)
  ·
    refine ⟨190853141731244026962909155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127235427820829351308606103 190853141731244026962909155)
    ·
      refine ⟨286279712596866040444363733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190853141731244026962909155 286279712596866040444363733)
      ·
        refine ⟨6709680763989047822914775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 286279712596866040444363733 6709680763989047822914775)
        ·
          refine ⟨10064521145983571734372163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709680763989047822914775 10064521145983571734372163)
          ·
            refine ⟨15096781718975357601558245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064521145983571734372163 15096781718975357601558245)
            ·
              refine ⟨2830646572307879550292171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15096781718975357601558245 2830646572307879550292171)
              ·
                refine ⟨4245969858461819325438257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830646572307879550292171 4245969858461819325438257)
                ·
                  refine ⟨3184477393846364494078693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4245969858461819325438257 3184477393846364494078693)
                  ·
                    refine ⟨597089511346193342639755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184477393846364494078693 597089511346193342639755)
                    ·
                      rfl

theorem cell23_3488483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 4].length) (baseStart_3488483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488483 prefixEnd_3488483 := by exact prefixLift 3488483
  have htrace : WordTrace (prefixWord ++ tailWord_3488483) baseStart_3488483 baseEnd_3488483 := by
    simpa [prefixWord, tailWord_3488483, baseEnd_3488483] using wordTrace_append hprefix tailTrace_3488483
  have hstable : (prefixWord ++ tailWord_3488483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488483).length < 2 ^ (prefixWord ++ tailWord_3488483).sum := by decide
  have hdescent : baseEnd_3488483 < baseStart_3488483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488510 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_3488510 : Nat := 118140960795 + 3488510 * 2 ^ 59
def prefixEnd_3488510 : Nat := 4983230072969 + 3 ^ 40 * 3488510 * 2
def baseEnd_3488510 : Nat := 1791282398016251422281641

theorem tailTrace_3488510 : CollatzResearch.WordTrace tailWord_3488510 prefixEnd_3488510 1791282398016251422281641 := by
  unfold tailWord_3488510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904551573966441864979873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84824275061154356613225989 15904551573966441864979873)
  ·
    refine ⟨11928413680474831398734905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15904551573966441864979873 11928413680474831398734905)
    ·
      refine ⟨8946310260356123549051179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11928413680474831398734905 8946310260356123549051179)
      ·
        refine ⟨13419465390534185323576769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8946310260356123549051179 13419465390534185323576769)
        ·
          refine ⟨10064599042900638992682577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13419465390534185323576769 10064599042900638992682577)
          ·
            refine ⟨7548449282175479244511933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10064599042900638992682577 7548449282175479244511933)
            ·
              refine ⟨2830668480815804716691975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7548449282175479244511933 2830668480815804716691975)
              ·
                refine ⟨4246002721223707075037963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830668480815804716691975 4246002721223707075037963)
                ·
                  refine ⟨6369004081835560612556945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246002721223707075037963 6369004081835560612556945)
                  ·
                    refine ⟨4776753061376670459417709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6369004081835560612556945 4776753061376670459417709)
                    ·
                      refine ⟨1791282398016251422281641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4776753061376670459417709 1791282398016251422281641)
                      ·
                        rfl

theorem cell23_3488510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_3488510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488510 prefixEnd_3488510 := by exact prefixLift 3488510
  have htrace : WordTrace (prefixWord ++ tailWord_3488510) baseStart_3488510 baseEnd_3488510 := by
    simpa [prefixWord, tailWord_3488510, baseEnd_3488510] using wordTrace_append hprefix tailTrace_3488510
  have hstable : (prefixWord ++ tailWord_3488510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488510).length < 2 ^ (prefixWord ++ tailWord_3488510).sum := by decide
  have hdescent : baseEnd_3488510 < baseStart_3488510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488512 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_3488512 : Nat := 118140960795 + 3488512 * 2 ^ 59
def prefixEnd_3488512 : Nat := 4983230072969 + 3 ^ 40 * 3488512 * 2
def baseEnd_3488512 : Nat := 1791283424977560414456631

theorem tailTrace_3488512 : CollatzResearch.WordTrace tailWord_3488512 prefixEnd_3488512 1791283424977560414456631 := by
  unfold tailWord_3488512
  simp only [CollatzResearch.WordTrace]
  refine ⟨63618242768862144630705895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84824323691816192840941193 63618242768862144630705895)
  ·
    refine ⟨95427364153293216946058843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63618242768862144630705895 95427364153293216946058843)
    ·
      refine ⟨143141046229939825419088265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95427364153293216946058843 143141046229939825419088265)
      ·
        refine ⟨107355784672454869064316199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143141046229939825419088265 107355784672454869064316199)
        ·
          refine ⟨161033677008682303596474299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107355784672454869064316199 161033677008682303596474299)
          ·
            refine ⟨241550515513023455394711449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161033677008682303596474299 241550515513023455394711449)
            ·
              refine ⟨181162886634767591546033587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241550515513023455394711449 181162886634767591546033587)
              ·
                refine ⟨271744329952151387319050381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181162886634767591546033587 271744329952151387319050381)
                ·
                  refine ⟨101904123732056770244643893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271744329952151387319050381 101904123732056770244643893)
                  ·
                    refine ⟨9553511599880322210435365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101904123732056770244643893 9553511599880322210435365)
                    ·
                      refine ⟨1791283424977560414456631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9553511599880322210435365 1791283424977560414456631)
                      ·
                        rfl

theorem cell23_3488512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_3488512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488512 prefixEnd_3488512 := by exact prefixLift 3488512
  have htrace : WordTrace (prefixWord ++ tailWord_3488512) baseStart_3488512 baseEnd_3488512 := by
    simpa [prefixWord, tailWord_3488512, baseEnd_3488512] using wordTrace_append hprefix tailTrace_3488512
  have hstable : (prefixWord ++ tailWord_3488512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488512).length < 2 ^ (prefixWord ++ tailWord_3488512).sum := by decide
  have hdescent : baseEnd_3488512 < baseStart_3488512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488549 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_3488549 : Nat := 118140960795 + 3488549 * 2 ^ 59
def prefixEnd_3488549 : Nat := 4983230072969 + 3 ^ 40 * 3488549 * 2
def baseEnd_3488549 : Nat := 1791302423761776769693961

theorem tailTrace_3488549 : CollatzResearch.WordTrace tailWord_3488549 prefixEnd_3488549 1791302423761776769693961 := by
  unfold tailWord_3488549
  simp only [CollatzResearch.WordTrace]
  refine ⟨127237835038590244580508701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84825223359060163053672467 127237835038590244580508701)
  ·
    refine ⟨47714188139471341717690763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127237835038590244580508701 47714188139471341717690763)
    ·
      refine ⟨71571282209207012576536145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47714188139471341717690763 71571282209207012576536145)
      ·
        refine ⟨53678461656905259432402109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71571282209207012576536145 53678461656905259432402109)
        ·
          refine ⟨20129423121339472287150791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53678461656905259432402109 20129423121339472287150791)
          ·
            refine ⟨30194134682009208430726187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20129423121339472287150791 30194134682009208430726187)
            ·
              refine ⟨45291202023013812646089281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30194134682009208430726187 45291202023013812646089281)
              ·
                refine ⟨33968401517260359484566961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45291202023013812646089281 33968401517260359484566961)
                ·
                  refine ⟨25476301137945269613425221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33968401517260359484566961 25476301137945269613425221)
                  ·
                    refine ⟨4776806463364738052517229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25476301137945269613425221 4776806463364738052517229)
                    ·
                      refine ⟨1791302423761776769693961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4776806463364738052517229 1791302423761776769693961)
                      ·
                        rfl

theorem cell23_3488549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_3488549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488549 prefixEnd_3488549 := by exact prefixLift 3488549
  have htrace : WordTrace (prefixWord ++ tailWord_3488549) baseStart_3488549 baseEnd_3488549 := by
    simpa [prefixWord, tailWord_3488549, baseEnd_3488549] using wordTrace_append hprefix tailTrace_3488549
  have hstable : (prefixWord ++ tailWord_3488549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488549).length < 2 ^ (prefixWord ++ tailWord_3488549).sum := by decide
  have hdescent : baseEnd_3488549 < baseStart_3488549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488579 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 3]
def baseStart_3488579 : Nat := 118140960795 + 3488579 * 2 ^ 59
def prefixEnd_3488579 : Nat := 4983230072969 + 3 ^ 40 * 3488579 * 2
def baseEnd_3488579 : Nat := 1791317828181411652318823

theorem tailTrace_3488579 : CollatzResearch.WordTrace tailWord_3488579 prefixEnd_3488579 1791317828181411652318823 := by
  unfold tailWord_3488579
  simp only [CollatzResearch.WordTrace]
  refine ⟨127238929228481559704100791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84825952818987706469400527 127238929228481559704100791)
  ·
    refine ⟨190858393842722339556151187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127238929228481559704100791 190858393842722339556151187)
    ·
      refine ⟨286287590764083509334226781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190858393842722339556151187 286287590764083509334226781)
      ·
        refine ⟨107357846536531316000335043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286287590764083509334226781 107357846536531316000335043)
        ·
          refine ⟨161036769804796974000502565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107357846536531316000335043 161036769804796974000502565)
          ·
            refine ⟨30194394338399432625094231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161036769804796974000502565 30194394338399432625094231)
            ·
              refine ⟨45291591507599148937641347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30194394338399432625094231 45291591507599148937641347)
              ·
                refine ⟨67937387261398723406462021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45291591507599148937641347 67937387261398723406462021)
                ·
                  refine ⟨12738260111512260638711629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67937387261398723406462021 12738260111512260638711629)
                  ·
                    refine ⟨4776847541817097739516861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12738260111512260638711629 4776847541817097739516861)
                    ·
                      refine ⟨1791317828181411652318823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4776847541817097739516861 1791317828181411652318823)
                      ·
                        rfl

theorem cell23_3488579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_3488579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488579 prefixEnd_3488579 := by exact prefixLift 3488579
  have htrace : WordTrace (prefixWord ++ tailWord_3488579) baseStart_3488579 baseEnd_3488579 := by
    simpa [prefixWord, tailWord_3488579, baseEnd_3488579] using wordTrace_append hprefix tailTrace_3488579
  have hstable : (prefixWord ++ tailWord_3488579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488579).length < 2 ^ (prefixWord ++ tailWord_3488579).sum := by decide
  have hdescent : baseEnd_3488579 < baseStart_3488579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488599 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 1, 7]
def baseStart_3488599 : Nat := 118140960795 + 3488599 * 2 ^ 59
def prefixEnd_3488599 : Nat := 4983230072969 + 3 ^ 40 * 3488599 * 2
def baseEnd_3488599 : Nat := 597109365931500524689577

theorem tailTrace_3488599 : CollatzResearch.WordTrace tailWord_3488599 prefixEnd_3488599 597109365931500524689577 := by
  unfold tailWord_3488599
  simp only [CollatzResearch.WordTrace]
  refine ⟨127239658688409103119828851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84826439125606068746552567 127239658688409103119828851)
  ·
    refine ⟨190859488032613654679743277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127239658688409103119828851 190859488032613654679743277)
    ·
      refine ⟨71572308012230120504903729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190859488032613654679743277 71572308012230120504903729)
      ·
        refine ⟨53679231009172590378677797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71572308012230120504903729 53679231009172590378677797)
        ·
          refine ⟨10064855814219860696002087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53679231009172590378677797 10064855814219860696002087)
          ·
            refine ⟨15097283721329791044003131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064855814219860696002087 15097283721329791044003131)
            ·
              refine ⟨22645925581994686566004697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097283721329791044003131 22645925581994686566004697)
              ·
                refine ⟨16984444186496014924503523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22645925581994686566004697 16984444186496014924503523)
                ·
                  refine ⟨25476666279744022386755285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16984444186496014924503523 25476666279744022386755285)
                  ·
                    refine ⟨597109365931500524689577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25476666279744022386755285 597109365931500524689577)
                    ·
                      rfl

theorem cell23_3488599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_3488599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488599 prefixEnd_3488599 := by exact prefixLift 3488599
  have htrace : WordTrace (prefixWord ++ tailWord_3488599) baseStart_3488599 baseEnd_3488599 := by
    simpa [prefixWord, tailWord_3488599, baseEnd_3488599] using wordTrace_append hprefix tailTrace_3488599
  have hstable : (prefixWord ++ tailWord_3488599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488599).length < 2 ^ (prefixWord ++ tailWord_3488599).sum := by decide
  have hdescent : baseEnd_3488599 < baseStart_3488599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488619 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4]
def baseStart_3488619 : Nat := 118140960795 + 3488619 * 2 ^ 59
def prefixEnd_3488619 : Nat := 4983230072969 + 3 ^ 40 * 3488619 * 2
def baseEnd_3488619 : Nat := 1791338367407591495818639

theorem tailTrace_3488619 : CollatzResearch.WordTrace tailWord_3488619 prefixEnd_3488619 1791338367407591495818639 := by
  unfold tailWord_3488619
  simp only [CollatzResearch.WordTrace]
  refine ⟨127240388148336646535556911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84826925432224431023704607 127240388148336646535556911)
  ·
    refine ⟨190860582222504969803335367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127240388148336646535556911 190860582222504969803335367)
    ·
      refine ⟨286290873333757454705003051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190860582222504969803335367 286290873333757454705003051)
      ·
        refine ⟨429436310000636182057504577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286290873333757454705003051 429436310000636182057504577)
        ·
          refine ⟨322077232500477136543128433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429436310000636182057504577 322077232500477136543128433)
          ·
            refine ⟨241557924375357852407346325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322077232500477136543128433 241557924375357852407346325)
            ·
              refine ⟨11323027705094899331594359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241557924375357852407346325 11323027705094899331594359)
              ·
                refine ⟨16984541557642348997391539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11323027705094899331594359 16984541557642348997391539)
                ·
                  refine ⟨25476812336463523496087309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16984541557642348997391539 25476812336463523496087309)
                  ·
                    refine ⟨9553804626173821311032741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25476812336463523496087309 9553804626173821311032741)
                    ·
                      refine ⟨1791338367407591495818639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9553804626173821311032741 1791338367407591495818639)
                      ·
                        rfl

theorem cell23_3488619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_3488619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488619 prefixEnd_3488619 := by exact prefixLift 3488619
  have htrace : WordTrace (prefixWord ++ tailWord_3488619) baseStart_3488619 baseEnd_3488619 := by
    simpa [prefixWord, tailWord_3488619, baseEnd_3488619] using wordTrace_append hprefix tailTrace_3488619
  have hstable : (prefixWord ++ tailWord_3488619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488619).length < 2 ^ (prefixWord ++ tailWord_3488619).sum := by decide
  have hdescent : baseEnd_3488619 < baseStart_3488619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488636 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_3488636 : Nat := 118140960795 + 3488636 * 2 ^ 59
def prefixEnd_3488636 : Nat := 4983230072969 + 3 ^ 40 * 3488636 * 2
def baseEnd_3488636 : Nat := 1791347096578717929306061

theorem tailTrace_3488636 : CollatzResearch.WordTrace tailWord_3488636 prefixEnd_3488636 1791347096578717929306061 := by
  unfold tailWord_3488636
  simp only [CollatzResearch.WordTrace]
  refine ⟨63620504094637529219462881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84827338792850038959283841 63620504094637529219462881)
  ·
    refine ⟨47715378070978146914597161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63620504094637529219462881 47715378070978146914597161)
    ·
      refine ⟨35786533553233610185947871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47715378070978146914597161 35786533553233610185947871)
      ·
        refine ⟨53679800329850415278921807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35786533553233610185947871 53679800329850415278921807)
        ·
          refine ⟨80519700494775622918382711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53679800329850415278921807 80519700494775622918382711)
          ·
            refine ⟨120779550742163434377574067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80519700494775622918382711 120779550742163434377574067)
            ·
              refine ⟨181169326113245151566361101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120779550742163434377574067 181169326113245151566361101)
              ·
                refine ⟨67938497292466931837385413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181169326113245151566361101 67938497292466931837385413)
                ·
                  refine ⟨12738468242337549719509765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67938497292466931837385413 12738468242337549719509765)
                  ·
                    refine ⟨2388462795438290572408081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12738468242337549719509765 2388462795438290572408081)
                    ·
                      refine ⟨1791347096578717929306061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388462795438290572408081 1791347096578717929306061)
                      ·
                        rfl

theorem cell23_3488636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_3488636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488636 prefixEnd_3488636 := by exact prefixLift 3488636
  have htrace : WordTrace (prefixWord ++ tailWord_3488636) baseStart_3488636 baseEnd_3488636 := by
    simpa [prefixWord, tailWord_3488636, baseEnd_3488636] using wordTrace_append hprefix tailTrace_3488636
  have hstable : (prefixWord ++ tailWord_3488636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488636).length < 2 ^ (prefixWord ++ tailWord_3488636).sum := by decide
  have hdescent : baseEnd_3488636 < baseStart_3488636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488673 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3488673 : Nat := 118140960795 + 3488673 * 2 ^ 59
def prefixEnd_3488673 : Nat := 4983230072969 + 3 ^ 40 * 3488673 * 2
def baseEnd_3488673 : Nat := 1791366095362934284543391

theorem tailTrace_3488673 : CollatzResearch.WordTrace tailWord_3488673 prefixEnd_3488673 1791366095362934284543391 := by
  unfold tailWord_3488673
  simp only [CollatzResearch.WordTrace]
  refine ⟨127242357690141013758022673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84828238460094009172015115 127242357690141013758022673)
  ·
    refine ⟨95431768267605760318517005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127242357690141013758022673 95431768267605760318517005)
    ·
      refine ⟨35786913100352160119443877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95431768267605760318517005 35786913100352160119443877)
      ·
        refine ⟨6710046206316030022395727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35786913100352160119443877 6710046206316030022395727)
        ·
          refine ⟨10065069309474045033593591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710046206316030022395727 10065069309474045033593591)
          ·
            refine ⟨15097603964211067550390387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065069309474045033593591 15097603964211067550390387)
            ·
              refine ⟨22646405946316601325585581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097603964211067550390387 22646405946316601325585581)
              ·
                refine ⟨8492402229868725497094593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22646405946316601325585581 8492402229868725497094593)
                ·
                  refine ⟨6369301672401544122820945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8492402229868725497094593 6369301672401544122820945)
                  ·
                    refine ⟨4776976254301158092115709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6369301672401544122820945 4776976254301158092115709)
                    ·
                      refine ⟨1791366095362934284543391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4776976254301158092115709 1791366095362934284543391)
                      ·
                        rfl

theorem cell23_3488673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3488673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488673 prefixEnd_3488673 := by exact prefixLift 3488673
  have htrace : WordTrace (prefixWord ++ tailWord_3488673) baseStart_3488673 baseEnd_3488673 := by
    simpa [prefixWord, tailWord_3488673, baseEnd_3488673] using wordTrace_append hprefix tailTrace_3488673
  have hstable : (prefixWord ++ tailWord_3488673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488673).length < 2 ^ (prefixWord ++ tailWord_3488673).sum := by decide
  have hdescent : baseEnd_3488673 < baseStart_3488673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488697 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 1, 4]
def baseStart_3488697 : Nat := 118140960795 + 3488697 * 2 ^ 59
def prefixEnd_3488697 : Nat := 4983230072969 + 3 ^ 40 * 3488697 * 2
def baseEnd_3488697 : Nat := 597126139632880730214427

theorem tailTrace_3488697 : CollatzResearch.WordTrace tailWord_3488697 prefixEnd_3488697 597126139632880730214427 := by
  unfold tailWord_3488697
  simp only [CollatzResearch.WordTrace]
  refine ⟨127243233042054065856896345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84828822028036043904597563 127243233042054065856896345)
  ·
    refine ⟨95432424781540549392672259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127243233042054065856896345 95432424781540549392672259)
    ·
      refine ⟨143148637172310824089008389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95432424781540549392672259 143148637172310824089008389)
      ·
        refine ⟨26840369469808279516689073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143148637172310824089008389 26840369469808279516689073)
        ·
          refine ⟨20130277102356209637516805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26840369469808279516689073 20130277102356209637516805)
          ·
            refine ⟨3774426956691789307034401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20130277102356209637516805 3774426956691789307034401)
            ·
              refine ⟨2830820217518841980275801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774426956691789307034401 2830820217518841980275801)
              ·
                refine ⟨2123115163139131485206851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830820217518841980275801 2123115163139131485206851)
                ·
                  refine ⟨3184672744708697227810277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123115163139131485206851 3184672744708697227810277)
                  ·
                    refine ⟨597126139632880730214427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184672744708697227810277 597126139632880730214427)
                    ·
                      rfl

theorem cell23_3488697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 4].length) (baseStart_3488697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488697 prefixEnd_3488697 := by exact prefixLift 3488697
  have htrace : WordTrace (prefixWord ++ tailWord_3488697) baseStart_3488697 baseEnd_3488697 := by
    simpa [prefixWord, tailWord_3488697, baseEnd_3488697] using wordTrace_append hprefix tailTrace_3488697
  have hstable : (prefixWord ++ tailWord_3488697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488697).length < 2 ^ (prefixWord ++ tailWord_3488697).sum := by decide
  have hdescent : baseEnd_3488697 < baseStart_3488697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
