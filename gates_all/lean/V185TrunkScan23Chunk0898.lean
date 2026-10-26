import V185TrunkScan23Chunk0897

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5315489 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5315489 : Nat := 118140960795 + 5315489 * 2 ^ 59
def prefixEnd_5315489 : Nat := 4983230072969 + 3 ^ 40 * 5315489 * 2
def baseEnd_5315489 : Nat := 2729400770686858858542017

theorem tailTrace_5315489 : CollatzResearch.WordTrace tailWord_5315489 prefixEnd_5315489 2729400770686858858542017 := by
  unfold tailWord_5315489
  simp only [CollatzResearch.WordTrace]
  refine ⟨193871811039898641091605521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129247874026599094061070347 193871811039898641091605521)
  ·
    refine ⟨145403858279923980818704141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193871811039898641091605521 145403858279923980818704141)
    ·
      refine ⟨54526446854971492807014053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145403858279923980818704141 54526446854971492807014053)
      ·
        refine ⟨10223708785307154901315135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54526446854971492807014053 10223708785307154901315135)
        ·
          refine ⟨15335563177960732351972703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10223708785307154901315135 15335563177960732351972703)
          ·
            refine ⟨23003344766941098527959055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15335563177960732351972703 23003344766941098527959055)
            ·
              refine ⟨34505017150411647791938583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23003344766941098527959055 34505017150411647791938583)
              ·
                refine ⟨51757525725617471687907875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34505017150411647791938583 51757525725617471687907875)
                ·
                  refine ⟨77636288588426207531861813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51757525725617471687907875 77636288588426207531861813)
                  ·
                    refine ⟨7278402055164956956112045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77636288588426207531861813 7278402055164956956112045)
                    ·
                      refine ⟨2729400770686858858542017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278402055164956956112045 2729400770686858858542017)
                      ·
                        rfl

theorem cell23_5315489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5315489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315489 prefixEnd_5315489 := by exact prefixLift 5315489
  have htrace : WordTrace (prefixWord ++ tailWord_5315489) baseStart_5315489 baseEnd_5315489 := by
    simpa [prefixWord, tailWord_5315489, baseEnd_5315489] using wordTrace_append hprefix tailTrace_5315489
  have hstable : (prefixWord ++ tailWord_5315489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315489).length < 2 ^ (prefixWord ++ tailWord_5315489).sum := by decide
  have hdescent : baseEnd_5315489 < baseStart_5315489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315492 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_5315492 : Nat := 118140960795 + 5315492 * 2 ^ 59
def prefixEnd_5315492 : Nat := 4983230072969 + 3 ^ 40 * 5315492 * 2
def baseEnd_5315492 : Nat := 909800770376274115601501

theorem tailTrace_5315492 : CollatzResearch.WordTrace tailWord_5315492 prefixEnd_5315492 909800770376274115601501 := by
  unfold tailWord_5315492
  simp only [CollatzResearch.WordTrace]
  refine ⟨96935960229443886301982365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129247946972591848402643153 96935960229443886301982365)
  ·
    refine ⟨36350985086041457363243387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96935960229443886301982365 36350985086041457363243387)
    ·
      refine ⟨54526477629062186044865081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36350985086041457363243387 54526477629062186044865081)
      ·
        refine ⟨40894858221796639533648811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54526477629062186044865081 40894858221796639533648811)
        ·
          refine ⟨61342287332694959300473217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40894858221796639533648811 61342287332694959300473217)
          ·
            refine ⟨46006715499521219475354913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61342287332694959300473217 46006715499521219475354913)
            ·
              refine ⟨34505036624640914606516185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46006715499521219475354913 34505036624640914606516185)
              ·
                refine ⟨25878777468480685954887139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34505036624640914606516185 25878777468480685954887139)
                ·
                  refine ⟨38818166202721028932330709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25878777468480685954887139 38818166202721028932330709)
                  ·
                    refine ⟨909800770376274115601501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38818166202721028932330709 909800770376274115601501)
                    ·
                      rfl

theorem cell23_5315492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_5315492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315492 prefixEnd_5315492 := by exact prefixLift 5315492
  have htrace : WordTrace (prefixWord ++ tailWord_5315492) baseStart_5315492 baseEnd_5315492 := by
    simpa [prefixWord, tailWord_5315492, baseEnd_5315492] using wordTrace_append hprefix tailTrace_5315492
  have hstable : (prefixWord ++ tailWord_5315492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315492).length < 2 ^ (prefixWord ++ tailWord_5315492).sum := by decide
  have hdescent : baseEnd_5315492 < baseStart_5315492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315524 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5315524 : Nat := 118140960795 + 5315524 * 2 ^ 59
def prefixEnd_5315524 : Nat := 4983230072969 + 3 ^ 40 * 5315524 * 2
def baseEnd_5315524 : Nat := 2729418742509766221604357

theorem tailTrace_5315524 : CollatzResearch.WordTrace tailWord_5315524 prefixEnd_5315524 2729418742509766221604357 := by
  unfold tailWord_5315524
  simp only [CollatzResearch.WordTrace]
  refine ⟨96936543797385921034564813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129248725063181228046086417 96936543797385921034564813)
  ·
    refine ⟨36351203924019720387961805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96936543797385921034564813 36351203924019720387961805)
    ·
      refine ⟨13631701471507395145485677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36351203924019720387961805 13631701471507395145485677)
      ·
        refine ⟨5111888051815273179557129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13631701471507395145485677 5111888051815273179557129)
        ·
          refine ⟨3833916038861454884667847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5111888051815273179557129 3833916038861454884667847)
          ·
            refine ⟨5750874058292182327001771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833916038861454884667847 5750874058292182327001771)
            ·
              refine ⟨8626311087438273490502657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750874058292182327001771 8626311087438273490502657)
              ·
                refine ⟨6469733315578705117876993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8626311087438273490502657 6469733315578705117876993)
                ·
                  refine ⟨4852299986684028838407745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6469733315578705117876993 4852299986684028838407745)
                  ·
                    refine ⟨3639224990013021628805809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4852299986684028838407745 3639224990013021628805809)
                    ·
                      refine ⟨2729418742509766221604357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639224990013021628805809 2729418742509766221604357)
                      ·
                        rfl

theorem cell23_5315524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5315524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315524 prefixEnd_5315524 := by exact prefixLift 5315524
  have htrace : WordTrace (prefixWord ++ tailWord_5315524) baseStart_5315524 baseEnd_5315524 := by
    simpa [prefixWord, tailWord_5315524, baseEnd_5315524] using wordTrace_append hprefix tailTrace_5315524
  have hstable : (prefixWord ++ tailWord_5315524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315524).length < 2 ^ (prefixWord ++ tailWord_5315524).sum := by decide
  have hdescent : baseEnd_5315524 < baseStart_5315524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315546 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2]
def baseStart_5315546 : Nat := 118140960795 + 5315546 * 2 ^ 59
def prefixEnd_5315546 : Nat := 4983230072969 + 3 ^ 40 * 5315546 * 2
def baseEnd_5315546 : Nat := 2729430039084165135529255

theorem tailTrace_5315546 : CollatzResearch.WordTrace tailWord_5315546 prefixEnd_5315546 2729430039084165135529255 := by
  unfold tailWord_5315546
  simp only [CollatzResearch.WordTrace]
  refine ⟨48468472500173034956607623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129249260000461426550953661 48468472500173034956607623)
  ·
    refine ⟨72702708750259552434911435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48468472500173034956607623 72702708750259552434911435)
    ·
      refine ⟨109054063125389328652367153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72702708750259552434911435 109054063125389328652367153)
      ·
        refine ⟨81790547344041996489275365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109054063125389328652367153 81790547344041996489275365)
        ·
          refine ⟨15335727627007874341739131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81790547344041996489275365 15335727627007874341739131)
          ·
            refine ⟨23003591440511811512608697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15335727627007874341739131 23003591440511811512608697)
            ·
              refine ⟨17252693580383858634456523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23003591440511811512608697 17252693580383858634456523)
              ·
                refine ⟨25879040370575787951684785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17252693580383858634456523 25879040370575787951684785)
                ·
                  refine ⟨19409280277931840963763589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25879040370575787951684785 19409280277931840963763589)
                  ·
                    refine ⟨3639240052112220180705673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19409280277931840963763589 3639240052112220180705673)
                    ·
                      refine ⟨2729430039084165135529255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639240052112220180705673 2729430039084165135529255)
                      ·
                        rfl

theorem cell23_5315546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_5315546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315546 prefixEnd_5315546 := by exact prefixLift 5315546
  have htrace : WordTrace (prefixWord ++ tailWord_5315546) baseStart_5315546 baseEnd_5315546 := by
    simpa [prefixWord, tailWord_5315546, baseEnd_5315546] using wordTrace_append hprefix tailTrace_5315546
  have hstable : (prefixWord ++ tailWord_5315546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315546).length < 2 ^ (prefixWord ++ tailWord_5315546).sum := by decide
  have hdescent : baseEnd_5315546 < baseStart_5315546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315630 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_5315630 : Nat := 118140960795 + 5315630 * 2 ^ 59
def prefixEnd_5315630 : Nat := 4983230072969 + 3 ^ 40 * 5315630 * 2
def baseEnd_5315630 : Nat := 2729473171459142806878869

theorem tailTrace_5315630 : CollatzResearch.WordTrace tailWord_5315630 prefixEnd_5315630 2729473171459142806878869 := by
  unfold tailWord_5315630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24234619216548477771561043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129251302488258548114992229 24234619216548477771561043)
  ·
    refine ⟨36351928824822716657341565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24234619216548477771561043 36351928824822716657341565)
    ·
      refine ⟨13631973309308518746503087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36351928824822716657341565 13631973309308518746503087)
      ·
        refine ⟨20447959963962778119754631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13631973309308518746503087 20447959963962778119754631)
        ·
          refine ⟨30671939945944167179631947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20447959963962778119754631 30671939945944167179631947)
          ·
            refine ⟨46007909918916250769447921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30671939945944167179631947 46007909918916250769447921)
            ·
              refine ⟨34505932439187188077085941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46007909918916250769447921 34505932439187188077085941)
              ·
                refine ⟨3234931166173798882226807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34505932439187188077085941 3234931166173798882226807)
                ·
                  refine ⟨4852396749260698323340211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234931166173798882226807 4852396749260698323340211)
                  ·
                    refine ⟨7278595123891047485010317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852396749260698323340211 7278595123891047485010317)
                    ·
                      refine ⟨2729473171459142806878869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278595123891047485010317 2729473171459142806878869)
                      ·
                        rfl

theorem cell23_5315630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_5315630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315630 prefixEnd_5315630 := by exact prefixLift 5315630
  have htrace : WordTrace (prefixWord ++ tailWord_5315630) baseStart_5315630 baseEnd_5315630 := by
    simpa [prefixWord, tailWord_5315630, baseEnd_5315630] using wordTrace_append hprefix tailTrace_5315630
  have hstable : (prefixWord ++ tailWord_5315630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315630).length < 2 ^ (prefixWord ++ tailWord_5315630).sum := by decide
  have hdescent : baseEnd_5315630 < baseStart_5315630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315666 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_5315666 : Nat := 118140960795 + 5315666 * 2 ^ 59
def prefixEnd_5315666 : Nat := 4983230072969 + 3 ^ 40 * 5315666 * 2
def baseEnd_5315666 : Nat := 2729491656762704666028703

theorem tailTrace_5315666 : CollatzResearch.WordTrace tailWord_5315666 prefixEnd_5315666 2729491656762704666028703 := by
  unfold tailWord_5315666
  simp only [CollatzResearch.WordTrace]
  refine ⟨48469566690064350080199713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129252177840171600213865901 48469566690064350080199713)
  ·
    refine ⟨36352175017548262560149785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48469566690064350080199713 36352175017548262560149785)
    ·
      refine ⟨27264131263161196920112339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36352175017548262560149785 27264131263161196920112339)
      ·
        refine ⟨40896196894741795380168509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27264131263161196920112339 40896196894741795380168509)
        ·
          refine ⟨15336073835528173267563191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40896196894741795380168509 15336073835528173267563191)
          ·
            refine ⟨23004110753292259901344787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15336073835528173267563191 23004110753292259901344787)
            ·
              refine ⟨34506166129938389852017181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23004110753292259901344787 34506166129938389852017181)
              ·
                refine ⟨12939812298726896194506443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34506166129938389852017181 12939812298726896194506443)
                ·
                  refine ⟨19409718448090344291759665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12939812298726896194506443 19409718448090344291759665)
                  ·
                    refine ⟨14557288836067758218819749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19409718448090344291759665 14557288836067758218819749)
                    ·
                      refine ⟨2729491656762704666028703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14557288836067758218819749 2729491656762704666028703)
                      ·
                        rfl

theorem cell23_5315666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_5315666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315666 prefixEnd_5315666 := by exact prefixLift 5315666
  have htrace : WordTrace (prefixWord ++ tailWord_5315666) baseStart_5315666 baseEnd_5315666 := by
    simpa [prefixWord, tailWord_5315666, baseEnd_5315666] using wordTrace_append hprefix tailTrace_5315666
  have hstable : (prefixWord ++ tailWord_5315666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315666).length < 2 ^ (prefixWord ++ tailWord_5315666).sum := by decide
  have hdescent : baseEnd_5315666 < baseStart_5315666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315676 : List Nat := [2, 2, 4, 1, 1, 1, 5, 7]
def baseStart_5315676 : Nat := 118140960795 + 5315676 * 2 ^ 59
def prefixEnd_5315676 : Nat := 4983230072969 + 3 ^ 40 * 5315676 * 2
def baseEnd_5315676 : Nat := 101092473761824060255691

theorem tailTrace_5315676 : CollatzResearch.WordTrace tailWord_5315676 prefixEnd_5315676 101092473761824060255691 := by
  unfold tailWord_5315676
  simp only [CollatzResearch.WordTrace]
  refine ⟨96939315745110586014331441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129252420993480781352441921 96939315745110586014331441)
  ·
    refine ⟨72704486808832939510748581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96939315745110586014331441 72704486808832939510748581)
    ·
      refine ⟨13632091276656176158265359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72704486808832939510748581 13632091276656176158265359)
      ·
        refine ⟨20448136914984264237398039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13632091276656176158265359 20448136914984264237398039)
        ·
          refine ⟨30672205372476396356097059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20448136914984264237398039 30672205372476396356097059)
          ·
            refine ⟨46008308058714594534145589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30672205372476396356097059 46008308058714594534145589)
            ·
              refine ⟨4313278880504493237576149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46008308058714594534145589 4313278880504493237576149)
              ·
                refine ⟨101092473761824060255691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4313278880504493237576149 101092473761824060255691)
                ·
                  rfl

theorem cell23_5315676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 7].length) (baseStart_5315676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315676 prefixEnd_5315676 := by exact prefixLift 5315676
  have htrace : WordTrace (prefixWord ++ tailWord_5315676) baseStart_5315676 baseEnd_5315676 := by
    simpa [prefixWord, tailWord_5315676, baseEnd_5315676] using wordTrace_append hprefix tailTrace_5315676
  have hstable : (prefixWord ++ tailWord_5315676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315676).length < 2 ^ (prefixWord ++ tailWord_5315676).sum := by decide
  have hdescent : baseEnd_5315676 < baseStart_5315676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315687 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_5315687 : Nat := 118140960795 + 5315687 * 2 ^ 59
def prefixEnd_5315687 : Nat := 4983230072969 + 3 ^ 40 * 5315687 * 2
def baseEnd_5315687 : Nat := 2729502439856449083866107

theorem tailTrace_5315687 : CollatzResearch.WordTrace tailWord_5315687 prefixEnd_5315687 2729502439856449083866107 := by
  unfold tailWord_5315687
  simp only [CollatzResearch.WordTrace]
  refine ⟨193879032693181320907313315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129252688462120880604875543 193879032693181320907313315)
  ·
    refine ⟨290818549039771981360969973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193879032693181320907313315 290818549039771981360969973)
    ·
      refine ⟨27264238972478623252590935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 290818549039771981360969973 27264238972478623252590935)
      ·
        refine ⟨40896358458717934878886403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27264238972478623252590935 40896358458717934878886403)
        ·
          refine ⟨61344537688076902318329605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40896358458717934878886403 61344537688076902318329605)
          ·
            refine ⟨11502100816514419184686801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61344537688076902318329605 11502100816514419184686801)
            ·
              refine ⟨8626575612385814388515101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11502100816514419184686801 8626575612385814388515101)
              ·
                refine ⟨3234965854644680395693163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8626575612385814388515101 3234965854644680395693163)
                ·
                  refine ⟨4852448781967020593539745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234965854644680395693163 4852448781967020593539745)
                  ·
                    refine ⟨3639336586475265445154809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4852448781967020593539745 3639336586475265445154809)
                    ·
                      refine ⟨2729502439856449083866107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639336586475265445154809 2729502439856449083866107)
                      ·
                        rfl

theorem cell23_5315687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_5315687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315687 prefixEnd_5315687 := by exact prefixLift 5315687
  have htrace : WordTrace (prefixWord ++ tailWord_5315687) baseStart_5315687 baseEnd_5315687 := by
    simpa [prefixWord, tailWord_5315687, baseEnd_5315687] using wordTrace_append hprefix tailTrace_5315687
  have hstable : (prefixWord ++ tailWord_5315687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315687).length < 2 ^ (prefixWord ++ tailWord_5315687).sum := by decide
  have hdescent : baseEnd_5315687 < baseStart_5315687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315690 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_5315690 : Nat := 118140960795 + 5315690 * 2 ^ 59
def prefixEnd_5315690 : Nat := 4983230072969 + 3 ^ 40 * 5315690 * 2
def baseEnd_5315690 : Nat := 2729503980298412572128593

theorem tailTrace_5315690 : CollatzResearch.WordTrace tailWord_5315690 prefixEnd_5315690 2729503980298412572128593 := by
  unfold tailWord_5315690
  simp only [CollatzResearch.WordTrace]
  refine ⟨48469785528042613104918131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129252761408113634946448349 48469785528042613104918131)
  ·
    refine ⟨72704678292063919657377197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48469785528042613104918131 72704678292063919657377197)
    ·
      refine ⟨27264254359523969871516449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72704678292063919657377197 27264254359523969871516449)
      ·
        refine ⟨20448190769642977403637337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27264254359523969871516449 20448190769642977403637337)
        ·
          refine ⟨15336143077232233052728003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20448190769642977403637337 15336143077232233052728003)
          ·
            refine ⟨23004214615848349579092005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15336143077232233052728003 23004214615848349579092005)
            ·
              refine ⟨4313290240471565546079751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23004214615848349579092005 4313290240471565546079751)
              ·
                refine ⟨6469935360707348319119627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313290240471565546079751 6469935360707348319119627)
                ·
                  refine ⟨9704903041061022478679441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469935360707348319119627 9704903041061022478679441)
                  ·
                    refine ⟨7278677280795766859009581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9704903041061022478679441 7278677280795766859009581)
                    ·
                      refine ⟨2729503980298412572128593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278677280795766859009581 2729503980298412572128593)
                      ·
                        rfl

theorem cell23_5315690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_5315690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315690 prefixEnd_5315690 := by exact prefixLift 5315690
  have htrace : WordTrace (prefixWord ++ tailWord_5315690) baseStart_5315690 baseEnd_5315690 := by
    simpa [prefixWord, tailWord_5315690, baseEnd_5315690] using wordTrace_append hprefix tailTrace_5315690
  have hstable : (prefixWord ++ tailWord_5315690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315690).length < 2 ^ (prefixWord ++ tailWord_5315690).sum := by decide
  have hdescent : baseEnd_5315690 < baseStart_5315690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315720 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5315720 : Nat := 118140960795 + 5315720 * 2 ^ 59
def prefixEnd_5315720 : Nat := 4983230072969 + 3 ^ 40 * 5315720 * 2
def baseEnd_5315720 : Nat := 2729519384718047454753455

theorem tailTrace_5315720 : CollatzResearch.WordTrace tailWord_5315720 prefixEnd_5315720 2729519384718047454753455 := by
  unfold tailWord_5315720
  simp only [CollatzResearch.WordTrace]
  refine ⟨96940118151030883771632307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129253490868041178362176409 96940118151030883771632307)
  ·
    refine ⟨145410177226546325657448461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96940118151030883771632307 145410177226546325657448461)
    ·
      refine ⟨54528816459954872121543173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145410177226546325657448461 54528816459954872121543173)
      ·
        refine ⟨10224153086241538522789345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54528816459954872121543173 10224153086241538522789345)
        ·
          refine ⟨7668114814681153892092009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10224153086241538522789345 7668114814681153892092009)
          ·
            refine ⟨5751086111010865419069007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7668114814681153892092009 5751086111010865419069007)
            ·
              refine ⟨8626629166516298128603511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751086111010865419069007 8626629166516298128603511)
              ·
                refine ⟨12939943749774447192905267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8626629166516298128603511 12939943749774447192905267)
                ·
                  refine ⟨19409915624661670789357901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12939943749774447192905267 19409915624661670789357901)
                  ·
                    refine ⟨7278718359248126546009213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19409915624661670789357901 7278718359248126546009213)
                    ·
                      refine ⟨2729519384718047454753455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278718359248126546009213 2729519384718047454753455)
                      ·
                        rfl

theorem cell23_5315720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5315720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315720 prefixEnd_5315720 := by exact prefixLift 5315720
  have htrace : WordTrace (prefixWord ++ tailWord_5315720) baseStart_5315720 baseEnd_5315720 := by
    simpa [prefixWord, tailWord_5315720, baseEnd_5315720] using wordTrace_append hprefix tailTrace_5315720
  have hstable : (prefixWord ++ tailWord_5315720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315720).length < 2 ^ (prefixWord ++ tailWord_5315720).sum := by decide
  have hdescent : baseEnd_5315720 < baseStart_5315720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315730 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_5315730 : Nat := 118140960795 + 5315730 * 2 ^ 59
def prefixEnd_5315730 : Nat := 4983230072969 + 3 ^ 40 * 5315730 * 2
def baseEnd_5315730 : Nat := 2729524519524592415628409

theorem tailTrace_5315730 : CollatzResearch.WordTrace tailWord_5315730 prefixEnd_5315730 2729524519524592415628409 := by
  unfold tailWord_5315730
  simp only [CollatzResearch.WordTrace]
  refine ⟨48470150258006384812782161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129253734021350359500752429 48470150258006384812782161)
  ·
    refine ⟨36352612693504788609586621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48470150258006384812782161 36352612693504788609586621)
    ·
      refine ⟨13632229760064295728594983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36352612693504788609586621 13632229760064295728594983)
      ·
        refine ⟨20448344640096443592892475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13632229760064295728594983 20448344640096443592892475)
        ·
          refine ⟨30672516960144665389338713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20448344640096443592892475 30672516960144665389338713)
          ·
            refine ⟨23004387720108499042004035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30672516960144665389338713 23004387720108499042004035)
            ·
              refine ⟨34506581580162748563006053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23004387720108499042004035 34506581580162748563006053)
              ·
                refine ⟨6469984046280515355563635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34506581580162748563006053 6469984046280515355563635)
                ·
                  refine ⟨9704976069420773033345453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469984046280515355563635 9704976069420773033345453)
                  ·
                    refine ⟨3639366026032789887504545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9704976069420773033345453 3639366026032789887504545)
                    ·
                      refine ⟨2729524519524592415628409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639366026032789887504545 2729524519524592415628409)
                      ·
                        rfl

theorem cell23_5315730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_5315730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315730 prefixEnd_5315730 := by exact prefixLift 5315730
  have htrace : WordTrace (prefixWord ++ tailWord_5315730) baseStart_5315730 baseEnd_5315730 := by
    simpa [prefixWord, tailWord_5315730, baseEnd_5315730] using wordTrace_append hprefix tailTrace_5315730
  have hstable : (prefixWord ++ tailWord_5315730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315730).length < 2 ^ (prefixWord ++ tailWord_5315730).sum := by decide
  have hdescent : baseEnd_5315730 < baseStart_5315730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315739 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4]
def baseStart_5315739 : Nat := 118140960795 + 5315739 * 2 ^ 59
def prefixEnd_5315739 : Nat := 4983230072969 + 3 ^ 40 * 5315739 * 2
def baseEnd_5315739 : Nat := 2729529140850482880415867

theorem tailTrace_5315739 : CollatzResearch.WordTrace tailWord_5315739 prefixEnd_5315739 2729529140850482880415867 := by
  unfold tailWord_5315739
  simp only [CollatzResearch.WordTrace]
  refine ⟨193880929288992933788206271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129253952859328622525470847 193880929288992933788206271)
  ·
    refine ⟨290821393933489400682309407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193880929288992933788206271 290821393933489400682309407)
    ·
      refine ⟨436232090900234101023464111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290821393933489400682309407 436232090900234101023464111)
      ·
        refine ⟨654348136350351151535196167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436232090900234101023464111 654348136350351151535196167)
        ·
          refine ⟨981522204525526727302794251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654348136350351151535196167 981522204525526727302794251)
          ·
            refine ⟨1472283306788290090954191377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981522204525526727302794251 1472283306788290090954191377)
            ·
              refine ⟨1104212480091217568215643533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472283306788290090954191377 1104212480091217568215643533)
              ·
                refine ⟨414079680034206588080866325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1104212480091217568215643533 414079680034206588080866325)
                ·
                  refine ⟨19409985001603433816290609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 414079680034206588080866325 19409985001603433816290609)
                  ·
                    refine ⟨14557488751202575362217957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19409985001603433816290609 14557488751202575362217957)
                    ·
                      refine ⟨2729529140850482880415867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14557488751202575362217957 2729529140850482880415867)
                      ·
                        rfl

theorem cell23_5315739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_5315739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315739 prefixEnd_5315739 := by exact prefixLift 5315739
  have htrace : WordTrace (prefixWord ++ tailWord_5315739) baseStart_5315739 baseEnd_5315739 := by
    simpa [prefixWord, tailWord_5315739, baseEnd_5315739] using wordTrace_append hprefix tailTrace_5315739
  have hstable : (prefixWord ++ tailWord_5315739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315739).length < 2 ^ (prefixWord ++ tailWord_5315739).sum := by decide
  have hdescent : baseEnd_5315739 < baseStart_5315739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315779 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 1, 7]
def baseStart_5315779 : Nat := 118140960795 + 5315779 * 2 ^ 59
def prefixEnd_5315779 : Nat := 4983230072969 + 3 ^ 40 * 5315779 * 2
def baseEnd_5315779 : Nat := 909849893358887574638561

theorem tailTrace_5315779 : CollatzResearch.WordTrace tailWord_5315779 prefixEnd_5315779 909849893358887574638561 := by
  unfold tailWord_5315779
  simp only [CollatzResearch.WordTrace]
  refine ⟨193882388208848020619662391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129254925472565347079774927 193882388208848020619662391)
  ·
    refine ⟨290823582313272030929493587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193882388208848020619662391 290823582313272030929493587)
    ·
      refine ⟨436235373469908046394240381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290823582313272030929493587 436235373469908046394240381)
      ·
        refine ⟨163588265051215517397840143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436235373469908046394240381 163588265051215517397840143)
        ·
          refine ⟨245382397576823276096760215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163588265051215517397840143 245382397576823276096760215)
          ·
            refine ⟨368073596365234914145140323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245382397576823276096760215 368073596365234914145140323)
            ·
              refine ⟨552110394547852371217710485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368073596365234914145140323 552110394547852371217710485)
              ·
                refine ⟨25880174744430579900830179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 552110394547852371217710485 25880174744430579900830179)
                ·
                  refine ⟨38820262116645869851245269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25880174744430579900830179 38820262116645869851245269)
                  ·
                    refine ⟨909849893358887574638561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38820262116645869851245269 909849893358887574638561)
                    ·
                      rfl

theorem cell23_5315779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 7].length) (baseStart_5315779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315779 prefixEnd_5315779 := by exact prefixLift 5315779
  have htrace : WordTrace (prefixWord ++ tailWord_5315779) baseStart_5315779 baseEnd_5315779 := by
    simpa [prefixWord, tailWord_5315779, baseEnd_5315779] using wordTrace_append hprefix tailTrace_5315779
  have hstable : (prefixWord ++ tailWord_5315779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315779).length < 2 ^ (prefixWord ++ tailWord_5315779).sum := by decide
  have hdescent : baseEnd_5315779 < baseStart_5315779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315833 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 2, 4, 2]
def baseStart_5315833 : Nat := 118140960795 + 5315833 * 2 ^ 59
def prefixEnd_5315833 : Nat := 4983230072969 + 3 ^ 40 * 5315833 * 2
def baseEnd_5315833 : Nat := 2729577408032005512640435

theorem tailTrace_5315833 : CollatzResearch.WordTrace tailWord_5315833 prefixEnd_5315833 2729577408032005512640435 := by
  unfold tailWord_5315833
  simp only [CollatzResearch.WordTrace]
  refine ⟨193884357750652387842128153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129256238500434925228085435 193884357750652387842128153)
  ·
    refine ⟨145413268312989290881596115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193884357750652387842128153 145413268312989290881596115)
    ·
      refine ⟨218119902469483936322394173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145413268312989290881596115 218119902469483936322394173)
      ·
        refine ⟨81794963426056476120897815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218119902469483936322394173 81794963426056476120897815)
        ·
          refine ⟨122692445139084714181346723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81794963426056476120897815 122692445139084714181346723)
          ·
            refine ⟨184038667708627071272020085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122692445139084714181346723 184038667708627071272020085)
            ·
              refine ⟨17253625097683787931751883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184038667708627071272020085 17253625097683787931751883)
              ·
                refine ⟨25880437646525681897627825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17253625097683787931751883 25880437646525681897627825)
                ·
                  refine ⟨19410328234894261423220869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25880437646525681897627825 19410328234894261423220869)
                  ·
                    refine ⟨3639436544042674016853913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19410328234894261423220869 3639436544042674016853913)
                    ·
                      refine ⟨2729577408032005512640435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639436544042674016853913 2729577408032005512640435)
                      ·
                        rfl

theorem cell23_5315833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_5315833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315833 prefixEnd_5315833 := by exact prefixLift 5315833
  have htrace : WordTrace (prefixWord ++ tailWord_5315833) baseStart_5315833 baseEnd_5315833 := by
    simpa [prefixWord, tailWord_5315833, baseEnd_5315833] using wordTrace_append hprefix tailTrace_5315833
  have hstable : (prefixWord ++ tailWord_5315833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315833).length < 2 ^ (prefixWord ++ tailWord_5315833).sum := by decide
  have hdescent : baseEnd_5315833 < baseStart_5315833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315843 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 3, 4]
def baseStart_5315843 : Nat := 118140960795 + 5315843 * 2 ^ 59
def prefixEnd_5315843 : Nat := 4983230072969 + 3 ^ 40 * 5315843 * 2
def baseEnd_5315843 : Nat := 909860847612850157838463

theorem tailTrace_5315843 : CollatzResearch.WordTrace tailWord_5315843 prefixEnd_5315843 909860847612850157838463 := by
  unfold tailWord_5315843
  simp only [CollatzResearch.WordTrace]
  refine ⟨193884722480616159549992183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129256481653744106366661455 193884722480616159549992183)
  ·
    refine ⟨290827083720924239324988275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193884722480616159549992183 290827083720924239324988275)
    ·
      refine ⟨436240625581386358987482413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290827083720924239324988275 436240625581386358987482413)
      ·
        refine ⟨163590234593019884620305905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436240625581386358987482413 163590234593019884620305905)
        ·
          refine ⟨122692675944764913465229429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163590234593019884620305905 122692675944764913465229429)
          ·
            refine ⟨11502438369821710637365259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122692675944764913465229429 11502438369821710637365259)
            ·
              refine ⟨17253657554732565956047889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11502438369821710637365259 17253657554732565956047889)
              ·
                refine ⟨12940243166049424467035917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17253657554732565956047889 12940243166049424467035917)
                ·
                  refine ⟨4852591187268534175138469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12940243166049424467035917 4852591187268534175138469)
                  ·
                    refine ⟨909860847612850157838463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4852591187268534175138469 909860847612850157838463)
                    ·
                      rfl

theorem cell23_5315843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 4].length) (baseStart_5315843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315843 prefixEnd_5315843 := by exact prefixLift 5315843
  have htrace : WordTrace (prefixWord ++ tailWord_5315843) baseStart_5315843 baseEnd_5315843 := by
    simpa [prefixWord, tailWord_5315843, baseEnd_5315843] using wordTrace_append hprefix tailTrace_5315843
  have hstable : (prefixWord ++ tailWord_5315843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315843).length < 2 ^ (prefixWord ++ tailWord_5315843).sum := by decide
  have hdescent : baseEnd_5315843 < baseStart_5315843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315876 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_5315876 : Nat := 118140960795 + 5315876 * 2 ^ 59
def prefixEnd_5315876 : Nat := 4983230072969 + 3 ^ 40 * 5315876 * 2
def baseEnd_5315876 : Nat := 2729599487700148844402737

theorem tailTrace_5315876 : CollatzResearch.WordTrace tailWord_5315876 prefixEnd_5315876 2729599487700148844402737 := by
  unfold tailWord_5315876
  simp only [CollatzResearch.WordTrace]
  refine ⟨96942963044748303092971741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129257284059664404123962321 96942963044748303092971741)
  ·
    refine ⟨36353611141780613659864403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96942963044748303092971741 36353611141780613659864403)
    ·
      refine ⟨54530416712670920489796605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36353611141780613659864403 54530416712670920489796605)
      ·
        refine ⟨20448906267251595183673727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54530416712670920489796605 20448906267251595183673727)
        ·
          refine ⟨30673359400877392775510591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20448906267251595183673727 30673359400877392775510591)
          ·
            refine ⟨46010039101316089163265887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30673359400877392775510591 46010039101316089163265887)
            ·
              refine ⟨69015058651974133744898831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46010039101316089163265887 69015058651974133744898831)
              ·
                refine ⟨103522587977961200617348247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69015058651974133744898831 103522587977961200617348247)
                ·
                  refine ⟨155283881966941800926022371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103522587977961200617348247 155283881966941800926022371)
                  ·
                    refine ⟨232925822950412701389033557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155283881966941800926022371 232925822950412701389033557)
                    ·
                      refine ⟨2729599487700148844402737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 232925822950412701389033557 2729599487700148844402737)
                      ·
                        rfl

theorem cell23_5315876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_5315876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315876 prefixEnd_5315876 := by exact prefixLift 5315876
  have htrace : WordTrace (prefixWord ++ tailWord_5315876) baseStart_5315876 baseEnd_5315876 := by
    simpa [prefixWord, tailWord_5315876, baseEnd_5315876] using wordTrace_append hprefix tailTrace_5315876
  have hstable : (prefixWord ++ tailWord_5315876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315876).length < 2 ^ (prefixWord ++ tailWord_5315876).sum := by decide
  have hdescent : baseEnd_5315876 < baseStart_5315876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315890 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_5315890 : Nat := 118140960795 + 5315890 * 2 ^ 59
def prefixEnd_5315890 : Nat := 4983230072969 + 3 ^ 40 * 5315890 * 2
def baseEnd_5315890 : Nat := 303289630714367976625297

theorem tailTrace_5315890 : CollatzResearch.WordTrace tailWord_5315890 prefixEnd_5315890 303289630714367976625297 := by
  unfold tailWord_5315890
  simp only [CollatzResearch.WordTrace]
  refine ⟨48471609177861471644238281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129257624474297257717968749 48471609177861471644238281)
  ·
    refine ⟨36353706883396103733178711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48471609177861471644238281 36353706883396103733178711)
    ·
      refine ⟨54530560325094155599768067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36353706883396103733178711 54530560325094155599768067)
      ·
        refine ⟨81795840487641233399652101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54530560325094155599768067 81795840487641233399652101)
        ·
          refine ⟨15336720091432731262434769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81795840487641233399652101 15336720091432731262434769)
          ·
            refine ⟨11502540068574548446826077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15336720091432731262434769 11502540068574548446826077)
            ·
              refine ⟨4313452525715455667559779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11502540068574548446826077 4313452525715455667559779)
              ·
                refine ⟨6470178788573183501339669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313452525715455667559779 6470178788573183501339669)
                ·
                  refine ⟨303289630714367976625297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6470178788573183501339669 303289630714367976625297)
                  ·
                    rfl

theorem cell23_5315890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_5315890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315890 prefixEnd_5315890 := by exact prefixLift 5315890
  have htrace : WordTrace (prefixWord ++ tailWord_5315890) baseStart_5315890 baseEnd_5315890 := by
    simpa [prefixWord, tailWord_5315890, baseEnd_5315890] using wordTrace_append hprefix tailTrace_5315890
  have hstable : (prefixWord ++ tailWord_5315890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315890).length < 2 ^ (prefixWord ++ tailWord_5315890).sum := by decide
  have hdescent : baseEnd_5315890 < baseStart_5315890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315900 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_5315900 : Nat := 118140960795 + 5315900 * 2 ^ 59
def prefixEnd_5315900 : Nat := 4983230072969 + 3 ^ 40 * 5315900 * 2
def baseEnd_5315900 : Nat := 2729611811235856750502627

theorem tailTrace_5315900 : CollatzResearch.WordTrace tailWord_5315900 prefixEnd_5315900 2729611811235856750502627 := by
  unfold tailWord_5315900
  simp only [CollatzResearch.WordTrace]
  refine ⟨96943400720704829142408577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129257867627606438856544769 96943400720704829142408577)
  ·
    refine ⟨72707550540528621856806433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96943400720704829142408577 72707550540528621856806433)
    ·
      refine ⟨54530662905396466392604825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72707550540528621856806433 54530662905396466392604825)
      ·
        refine ⟨40897997179047349794453619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54530662905396466392604825 40897997179047349794453619)
        ·
          refine ⟨61346995768571024691680429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40897997179047349794453619 61346995768571024691680429)
          ·
            refine ⟨23005123413214134259380161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61346995768571024691680429 23005123413214134259380161)
            ·
              refine ⟨17253842559910600694535121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23005123413214134259380161 17253842559910600694535121)
              ·
                refine ⟨12940381919932950520901341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17253842559910600694535121 12940381919932950520901341)
                ·
                  refine ⟨4852643219974856445338003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12940381919932950520901341 4852643219974856445338003)
                  ·
                    refine ⟨7278964829962284668007005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852643219974856445338003 7278964829962284668007005)
                    ·
                      refine ⟨2729611811235856750502627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278964829962284668007005 2729611811235856750502627)
                      ·
                        rfl

theorem cell23_5315900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_5315900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315900 prefixEnd_5315900 := by exact prefixLift 5315900
  have htrace : WordTrace (prefixWord ++ tailWord_5315900) baseStart_5315900 baseEnd_5315900 := by
    simpa [prefixWord, tailWord_5315900, baseEnd_5315900] using wordTrace_append hprefix tailTrace_5315900
  have hstable : (prefixWord ++ tailWord_5315900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315900).length < 2 ^ (prefixWord ++ tailWord_5315900).sum := by decide
  have hdescent : baseEnd_5315900 < baseStart_5315900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315903 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 1, 5]
def baseStart_5315903 : Nat := 118140960795 + 5315903 * 2 ^ 59
def prefixEnd_5315903 : Nat := 4983230072969 + 3 ^ 40 * 5315903 * 2
def baseEnd_5315903 : Nat := 909871117225940079588371

theorem tailTrace_5315903 : CollatzResearch.WordTrace tailWord_5315903 prefixEnd_5315903 909871117225940079588371 := by
  unfold tailWord_5315903
  simp only [CollatzResearch.WordTrace]
  refine ⟨193886910860398789797176363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129257940573599193198117575 193886910860398789797176363)
  ·
    refine ⟨290830366290598184695764545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193886910860398789797176363 290830366290598184695764545)
    ·
      refine ⟨218122774717948638521823409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290830366290598184695764545 218122774717948638521823409)
      ·
        refine ⟨163592081038461478891367557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218122774717948638521823409 163592081038461478891367557)
        ·
          refine ⟨30673515194711527292131417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163592081038461478891367557 30673515194711527292131417)
          ·
            refine ⟨23005136396033645469098563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30673515194711527292131417 23005136396033645469098563)
            ·
              refine ⟨34507704594050468203647845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23005136396033645469098563 34507704594050468203647845)
              ·
                refine ⟨6470194611384462788183971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34507704594050468203647845 6470194611384462788183971)
                ·
                  refine ⟨9705291917076694182275957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470194611384462788183971 9705291917076694182275957)
                  ·
                    refine ⟨909871117225940079588371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9705291917076694182275957 909871117225940079588371)
                    ·
                      rfl

theorem cell23_5315903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_5315903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315903 prefixEnd_5315903 := by exact prefixLift 5315903
  have htrace : WordTrace (prefixWord ++ tailWord_5315903) baseStart_5315903 baseEnd_5315903 := by
    simpa [prefixWord, tailWord_5315903, baseEnd_5315903] using wordTrace_append hprefix tailTrace_5315903
  have hstable : (prefixWord ++ tailWord_5315903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315903).length < 2 ^ (prefixWord ++ tailWord_5315903).sum := by decide
  have hdescent : baseEnd_5315903 < baseStart_5315903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315923 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 4]
def baseStart_5315923 : Nat := 118140960795 + 5315923 * 2 ^ 59
def prefixEnd_5315923 : Nat := 4983230072969 + 3 ^ 40 * 5315923 * 2
def baseEnd_5315923 : Nat := 2729623621290910160515021

theorem tailTrace_5315923 : CollatzResearch.WordTrace tailWord_5315923 prefixEnd_5315923 2729623621290910160515021 := by
  unfold tailWord_5315923
  simp only [CollatzResearch.WordTrace]
  refine ⟨193887640320326333212904423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129258426880217555475269615 193887640320326333212904423)
  ·
    refine ⟨290831460480489499819356635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193887640320326333212904423 290831460480489499819356635)
    ·
      refine ⟨436247190720734249729034953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290831460480489499819356635 436247190720734249729034953)
      ·
        refine ⟨327185393040550687296776215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436247190720734249729034953 327185393040550687296776215)
        ·
          refine ⟨490778089560826030945164323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327185393040550687296776215 490778089560826030945164323)
          ·
            refine ⟨736167134341239046417746485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490778089560826030945164323 736167134341239046417746485)
            ·
              refine ⟨69015668844491160601663733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 736167134341239046417746485 69015668844491160601663733)
              ·
                refine ⟨6470218954171046306405975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69015668844491160601663733 6470218954171046306405975)
                ·
                  refine ⟨9705328431256569459608963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470218954171046306405975 9705328431256569459608963)
                  ·
                    refine ⟨14557992646884854189413445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9705328431256569459608963 14557992646884854189413445)
                    ·
                      refine ⟨2729623621290910160515021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14557992646884854189413445 2729623621290910160515021)
                      ·
                        rfl

theorem cell23_5315923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_5315923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315923 prefixEnd_5315923 := by exact prefixLift 5315923
  have htrace : WordTrace (prefixWord ++ tailWord_5315923) baseStart_5315923 baseEnd_5315923 := by
    simpa [prefixWord, tailWord_5315923, baseEnd_5315923] using wordTrace_append hprefix tailTrace_5315923
  have hstable : (prefixWord ++ tailWord_5315923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315923).length < 2 ^ (prefixWord ++ tailWord_5315923).sum := by decide
  have hdescent : baseEnd_5315923 < baseStart_5315923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315973 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_5315973 : Nat := 118140960795 + 5315973 * 2 ^ 59
def prefixEnd_5315973 : Nat := 4983230072969 + 3 ^ 40 * 5315973 * 2
def baseEnd_5315973 : Nat := 2729649295323634964889791

theorem tailTrace_5315973 : CollatzResearch.WordTrace tailWord_5315973 prefixEnd_5315973 2729649295323634964889791 := by
  unfold tailWord_5315973
  simp only [CollatzResearch.WordTrace]
  refine ⟨193889463970145191752224573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129259642646763461168149715 193889463970145191752224573)
  ·
    refine ⟨72708548988804446907084215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193889463970145191752224573 72708548988804446907084215)
    ·
      refine ⟨109062823483206670360626323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72708548988804446907084215 109062823483206670360626323)
      ·
        refine ⟨163594235224810005540939485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109062823483206670360626323 163594235224810005540939485)
        ·
          refine ⟨61347838209303752077852307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163594235224810005540939485 61347838209303752077852307)
          ·
            refine ⟨92021757313955628116778461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61347838209303752077852307 92021757313955628116778461)
            ·
              refine ⟨34508158992733360543791923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92021757313955628116778461 34508158992733360543791923)
              ·
                refine ⟨51762238489100040815687885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34508158992733360543791923 51762238489100040815687885)
                ·
                  refine ⟨19410839433412515305882957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51762238489100040815687885 19410839433412515305882957)
                  ·
                    refine ⟨7279064787529693239706109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19410839433412515305882957 7279064787529693239706109)
                    ·
                      refine ⟨2729649295323634964889791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279064787529693239706109 2729649295323634964889791)
                      ·
                        rfl

theorem cell23_5315973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_5315973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315973 prefixEnd_5315973 := by exact prefixLift 5315973
  have htrace : WordTrace (prefixWord ++ tailWord_5315973) baseStart_5315973 baseEnd_5315973 := by
    simpa [prefixWord, tailWord_5315973, baseEnd_5315973] using wordTrace_append hprefix tailTrace_5315973
  have hstable : (prefixWord ++ tailWord_5315973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315973).length < 2 ^ (prefixWord ++ tailWord_5315973).sum := by decide
  have hdescent : baseEnd_5315973 < baseStart_5315973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315977 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 1, 1, 5]
def baseStart_5315977 : Nat := 118140960795 + 5315977 * 2 ^ 59
def prefixEnd_5315977 : Nat := 4983230072969 + 3 ^ 40 * 5315977 * 2
def baseEnd_5315977 : Nat := 2729651349246252949239773

theorem tailTrace_5315977 : CollatzResearch.WordTrace tailWord_5315977 prefixEnd_5315977 2729651349246252949239773 := by
  unfold tailWord_5315977
  simp only [CollatzResearch.WordTrace]
  refine ⟨193889609862130700435370185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129259739908087133623580123 193889609862130700435370185)
  ·
    refine ⟨145417207396598025326527639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193889609862130700435370185 145417207396598025326527639)
    ·
      refine ⟨218125811094897037989791459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145417207396598025326527639 218125811094897037989791459)
      ·
        refine ⟨327188716642345556984687189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218125811094897037989791459 327188716642345556984687189)
        ·
          refine ⟨3834242773152486995914303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 327188716642345556984687189 3834242773152486995914303)
          ·
            refine ⟨5751364159728730493871455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834242773152486995914303 5751364159728730493871455)
            ·
              refine ⟨8627046239593095740807183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751364159728730493871455 8627046239593095740807183)
              ·
                refine ⟨12940569359389643611210775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8627046239593095740807183 12940569359389643611210775)
                ·
                  refine ⟨19410854039084465416816163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12940569359389643611210775 19410854039084465416816163)
                  ·
                    refine ⟨29116281058626698125224245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19410854039084465416816163 29116281058626698125224245)
                    ·
                      refine ⟨2729651349246252949239773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29116281058626698125224245 2729651349246252949239773)
                      ·
                        rfl

theorem cell23_5315977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 1, 5].length) (baseStart_5315977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315977 prefixEnd_5315977 := by exact prefixLift 5315977
  have htrace : WordTrace (prefixWord ++ tailWord_5315977) baseStart_5315977 baseEnd_5315977 := by
    simpa [prefixWord, tailWord_5315977, baseEnd_5315977] using wordTrace_append hprefix tailTrace_5315977
  have hstable : (prefixWord ++ tailWord_5315977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315977).length < 2 ^ (prefixWord ++ tailWord_5315977).sum := by decide
  have hdescent : baseEnd_5315977 < baseStart_5315977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316000 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 5, 3, 2]
def baseStart_5316000 : Nat := 118140960795 + 5316000 * 2 ^ 59
def prefixEnd_5316000 : Nat := 4983230072969 + 3 ^ 40 * 5316000 * 2
def baseEnd_5316000 : Nat := 2729663159301306359252167

theorem tailTrace_5316000 : CollatzResearch.WordTrace tailWord_5316000 prefixEnd_5316000 2729663159301306359252167 := by
  unfold tailWord_5316000
  simp only [CollatzResearch.WordTrace]
  refine ⟨96945224370523687681728727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129260299160698250242304969 96945224370523687681728727)
  ·
    refine ⟨145417836555785531522593091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96945224370523687681728727 145417836555785531522593091)
    ·
      refine ⟨218126754833678297283889637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145417836555785531522593091 218126754833678297283889637)
      ·
        refine ⟨40898766531314680740729307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218126754833678297283889637 40898766531314680740729307)
        ·
          refine ⟨61348149796972021111093961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40898766531314680740729307 61348149796972021111093961)
          ·
            refine ⟨46011112347729015833320471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61348149796972021111093961 46011112347729015833320471)
            ·
              refine ⟨69016668521593523749980707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46011112347729015833320471 69016668521593523749980707)
              ·
                refine ⟨103525002782390285624971061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69016668521593523749980707 103525002782390285624971061)
                ·
                  refine ⟨9705469010849089277341037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103525002782390285624971061 9705469010849089277341037)
                  ·
                    refine ⟨3639550879068408479002889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9705469010849089277341037 3639550879068408479002889)
                    ·
                      refine ⟨2729663159301306359252167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639550879068408479002889 2729663159301306359252167)
                      ·
                        rfl

theorem cell23_5316000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_5316000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316000 prefixEnd_5316000 := by exact prefixLift 5316000
  have htrace : WordTrace (prefixWord ++ tailWord_5316000) baseStart_5316000 baseEnd_5316000 := by
    simpa [prefixWord, tailWord_5316000, baseEnd_5316000] using wordTrace_append hprefix tailTrace_5316000
  have hstable : (prefixWord ++ tailWord_5316000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316000).length < 2 ^ (prefixWord ++ tailWord_5316000).sum := by decide
  have hdescent : baseEnd_5316000 < baseStart_5316000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316007 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_5316007 : Nat := 118140960795 + 5316007 * 2 ^ 59
def prefixEnd_5316007 : Nat := 4983230072969 + 3 ^ 40 * 5316007 * 2
def baseEnd_5316007 : Nat := 2729666753665887831864635

theorem tailTrace_5316007 : CollatzResearch.WordTrace tailWord_5316007 prefixEnd_5316007 2729666753665887831864635 := by
  unfold tailWord_5316007
  simp only [CollatzResearch.WordTrace]
  refine ⟨193890704052022015558962275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129260469368014677039308183 193890704052022015558962275)
  ·
    refine ⟨290836056078033023338443413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193890704052022015558962275 290836056078033023338443413)
    ·
      refine ⟨13632940128657797968989535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 290836056078033023338443413 13632940128657797968989535)
      ·
        refine ⟨20449410192986696953484303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13632940128657797968989535 20449410192986696953484303)
        ·
          refine ⟨30674115289480045430226455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20449410192986696953484303 30674115289480045430226455)
          ·
            refine ⟨46011172934220068145339683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30674115289480045430226455 46011172934220068145339683)
            ·
              refine ⟨69016759401330102218009525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46011172934220068145339683 69016759401330102218009525)
              ·
                refine ⟨6470321193874697082938393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69016759401330102218009525 6470321193874697082938393)
                ·
                  refine ⟨4852740895406022812203795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6470321193874697082938393 4852740895406022812203795)
                  ·
                    refine ⟨7279111343109034218305693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852740895406022812203795 7279111343109034218305693)
                    ·
                      refine ⟨2729666753665887831864635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279111343109034218305693 2729666753665887831864635)
                      ·
                        rfl

theorem cell23_5316007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_5316007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316007 prefixEnd_5316007 := by exact prefixLift 5316007
  have htrace : WordTrace (prefixWord ++ tailWord_5316007) baseStart_5316007 baseEnd_5316007 := by
    simpa [prefixWord, tailWord_5316007, baseEnd_5316007] using wordTrace_append hprefix tailTrace_5316007
  have hstable : (prefixWord ++ tailWord_5316007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316007).length < 2 ^ (prefixWord ++ tailWord_5316007).sum := by decide
  have hdescent : baseEnd_5316007 < baseStart_5316007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316017 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5316017 : Nat := 118140960795 + 5316017 * 2 ^ 59
def prefixEnd_5316017 : Nat := 4983230072969 + 3 ^ 40 * 5316017 * 2
def baseEnd_5316017 : Nat := 2729671888472432792739589

theorem tailTrace_5316017 : CollatzResearch.WordTrace tailWord_5316017 prefixEnd_5316017 2729671888472432792739589 := by
  unfold tailWord_5316017
  simp only [CollatzResearch.WordTrace]
  refine ⟨193891068781985787266826305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129260712521323858177884203 193891068781985787266826305)
  ·
    refine ⟨145418301586489340450119729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193891068781985787266826305 145418301586489340450119729)
    ·
      refine ⟨109063726189867005337589797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145418301586489340450119729 109063726189867005337589797)
      ·
        refine ⟨20449448660600063500798087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109063726189867005337589797 20449448660600063500798087)
        ·
          refine ⟨30674172990900095251197131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20449448660600063500798087 30674172990900095251197131)
          ·
            refine ⟨46011259486350142876795697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30674172990900095251197131 46011259486350142876795697)
            ·
              refine ⟨34508444614762607157596773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46011259486350142876795697 34508444614762607157596773)
              ·
                refine ⟨6470333365267988842049395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34508444614762607157596773 6470333365267988842049395)
                ·
                  refine ⟨9705500047901983263074093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470333365267988842049395 9705500047901983263074093)
                  ·
                    refine ⟨3639562517963243723652785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9705500047901983263074093 3639562517963243723652785)
                    ·
                      refine ⟨2729671888472432792739589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639562517963243723652785 2729671888472432792739589)
                      ·
                        rfl

theorem cell23_5316017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5316017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316017 prefixEnd_5316017 := by exact prefixLift 5316017
  have htrace : WordTrace (prefixWord ++ tailWord_5316017) baseStart_5316017 baseEnd_5316017 := by
    simpa [prefixWord, tailWord_5316017, baseEnd_5316017] using wordTrace_append hprefix tailTrace_5316017
  have hstable : (prefixWord ++ tailWord_5316017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316017).length < 2 ^ (prefixWord ++ tailWord_5316017).sum := by decide
  have hdescent : baseEnd_5316017 < baseStart_5316017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316043 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4]
def baseStart_5316043 : Nat := 118140960795 + 5316043 * 2 ^ 59
def prefixEnd_5316043 : Nat := 4983230072969 + 3 ^ 40 * 5316043 * 2
def baseEnd_5316043 : Nat := 2729685238969449691014469

theorem tailTrace_5316043 : CollatzResearch.WordTrace tailWord_5316043 prefixEnd_5316043 2729685238969449691014469 := by
  unfold tailWord_5316043
  simp only [CollatzResearch.WordTrace]
  refine ⟨193892017079891593707272783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129261344719927729138181855 193892017079891593707272783)
  ·
    refine ⟨290838025619837390560909175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193892017079891593707272783 290838025619837390560909175)
    ·
      refine ⟨436257038429756085841363763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290838025619837390560909175 436257038429756085841363763)
      ·
        refine ⟨654385557644634128762045645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436257038429756085841363763 654385557644634128762045645)
        ·
          refine ⟨245394584116737798285767117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 654385557644634128762045645 245394584116737798285767117)
          ·
            refine ⟨92022969043776674357162669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245394584116737798285767117 92022969043776674357162669)
            ·
              refine ⟨34508613391416252883936001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92022969043776674357162669 34508613391416252883936001)
              ·
                refine ⟨25881460043562189662952001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34508613391416252883936001 25881460043562189662952001)
                ·
                  refine ⟨19411095032671642247214001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25881460043562189662952001 19411095032671642247214001)
                  ·
                    refine ⟨14558321274503731685410501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19411095032671642247214001 14558321274503731685410501)
                    ·
                      refine ⟨2729685238969449691014469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14558321274503731685410501 2729685238969449691014469)
                      ·
                        rfl

theorem cell23_5316043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_5316043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316043 prefixEnd_5316043 := by exact prefixLift 5316043
  have htrace : WordTrace (prefixWord ++ tailWord_5316043) baseStart_5316043 baseEnd_5316043 := by
    simpa [prefixWord, tailWord_5316043, baseEnd_5316043] using wordTrace_append hprefix tailTrace_5316043
  have hstable : (prefixWord ++ tailWord_5316043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316043).length < 2 ^ (prefixWord ++ tailWord_5316043).sum := by decide
  have hdescent : baseEnd_5316043 < baseStart_5316043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316133 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_5316133 : Nat := 118140960795 + 5316133 * 2 ^ 59
def prefixEnd_5316133 : Nat := 4983230072969 + 3 ^ 40 * 5316133 * 2
def baseEnd_5316133 : Nat := 2729731452228354338889055

theorem tailTrace_5316133 : CollatzResearch.WordTrace tailWord_5316133 prefixEnd_5316133 2729731452228354338889055 := by
  unfold tailWord_5316133
  simp only [CollatzResearch.WordTrace]
  refine ⟨193895299649565539078049053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129263533099710359385366035 193895299649565539078049053)
  ·
    refine ⟨72710737368587077154268395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193895299649565539078049053 72710737368587077154268395)
    ·
      refine ⟨109066106052880615731402593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72710737368587077154268395 109066106052880615731402593)
      ·
        refine ⟨81799579539660461798551945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109066106052880615731402593 81799579539660461798551945)
        ·
          refine ⟨61349684654745346348913959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81799579539660461798551945 61349684654745346348913959)
          ·
            refine ⟨92024526982118019523370939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61349684654745346348913959 92024526982118019523370939)
            ·
              refine ⟨138036790473177029285056409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92024526982118019523370939 138036790473177029285056409)
              ·
                refine ⟨103527592854882771963792307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138036790473177029285056409 103527592854882771963792307)
                ·
                  refine ⟨155291389282324157945688461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103527592854882771963792307 155291389282324157945688461)
                  ·
                    refine ⟨58234270980871559229633173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155291389282324157945688461 58234270980871559229633173)
                    ·
                      refine ⟨2729731452228354338889055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58234270980871559229633173 2729731452228354338889055)
                      ·
                        rfl

theorem cell23_5316133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_5316133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316133 prefixEnd_5316133 := by exact prefixLift 5316133
  have htrace : WordTrace (prefixWord ++ tailWord_5316133) baseStart_5316133 baseEnd_5316133 := by
    simpa [prefixWord, tailWord_5316133, baseEnd_5316133] using wordTrace_append hprefix tailTrace_5316133
  have hstable : (prefixWord ++ tailWord_5316133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316133).length < 2 ^ (prefixWord ++ tailWord_5316133).sum := by decide
  have hdescent : baseEnd_5316133 < baseStart_5316133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316203 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 10]
def baseStart_5316203 : Nat := 118140960795 + 5316203 * 2 ^ 59
def prefixEnd_5316203 : Nat := 4983230072969 + 3 ^ 40 * 5316203 * 2
def baseEnd_5316203 : Nat := 909922465291389688337911

theorem tailTrace_5316203 : CollatzResearch.WordTrace tailWord_5316203 prefixEnd_5316203 909922465291389688337911 := by
  unfold tailWord_5316203
  simp only [CollatzResearch.WordTrace]
  refine ⟨193897852759311941033097263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129265235172874627355398175 193897852759311941033097263)
  ·
    refine ⟨290846779138967911549645895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193897852759311941033097263 290846779138967911549645895)
    ·
      refine ⟨436270168708451867324468843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290846779138967911549645895 436270168708451867324468843)
      ·
        refine ⟨654405253062677800986703265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436270168708451867324468843 654405253062677800986703265)
        ·
          refine ⟨490803939797008350740027449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654405253062677800986703265 490803939797008350740027449)
          ·
            refine ⟨368102954847756263055020587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490803939797008350740027449 368102954847756263055020587)
            ·
              refine ⟨552154432271634394582530881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368102954847756263055020587 552154432271634394582530881)
              ·
                refine ⟨414115824203725795936898161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552154432271634394582530881 414115824203725795936898161)
                ·
                  refine ⟨310586868152794346952673621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414115824203725795936898161 310586868152794346952673621)
                  ·
                    refine ⟨909922465291389688337911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 310586868152794346952673621 909922465291389688337911)
                    ·
                      rfl

theorem cell23_5316203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_5316203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316203 prefixEnd_5316203 := by exact prefixLift 5316203
  have htrace : WordTrace (prefixWord ++ tailWord_5316203) baseStart_5316203 baseEnd_5316203 := by
    simpa [prefixWord, tailWord_5316203, baseEnd_5316203] using wordTrace_append hprefix tailTrace_5316203
  have hstable : (prefixWord ++ tailWord_5316203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316203).length < 2 ^ (prefixWord ++ tailWord_5316203).sum := by decide
  have hdescent : baseEnd_5316203 < baseStart_5316203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316221 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_5316221 : Nat := 118140960795 + 5316221 * 2 ^ 59
def prefixEnd_5316221 : Nat := 4983230072969 + 3 ^ 40 * 5316221 * 2
def baseEnd_5316221 : Nat := 2729776638525949994588651

theorem tailTrace_5316221 : CollatzResearch.WordTrace tailWord_5316221 prefixEnd_5316221 2729776638525949994588651 := by
  unfold tailWord_5316221
  simp only [CollatzResearch.WordTrace]
  refine ⟨193898509273246730107252517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129265672848831153404835011 193898509273246730107252517)
  ·
    refine ⟨36355970488733761895109847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193898509273246730107252517 36355970488733761895109847)
    ·
      refine ⟨54533955733100642842664771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36355970488733761895109847 54533955733100642842664771)
      ·
        refine ⟨81800933599650964263997157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54533955733100642842664771 81800933599650964263997157)
        ·
          refine ⟨15337675049934555799499467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81800933599650964263997157 15337675049934555799499467)
          ·
            refine ⟨23006512574901833699249201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15337675049934555799499467 23006512574901833699249201)
            ·
              refine ⟨17254884431176375274436901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23006512574901833699249201 17254884431176375274436901)
              ·
                refine ⟨3235290830845570363956919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17254884431176375274436901 3235290830845570363956919)
                ·
                  refine ⟨4852936246268355545935379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235290830845570363956919 4852936246268355545935379)
                  ·
                    refine ⟨7279404369402533318903069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852936246268355545935379 7279404369402533318903069)
                    ·
                      refine ⟨2729776638525949994588651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279404369402533318903069 2729776638525949994588651)
                      ·
                        rfl

theorem cell23_5316221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_5316221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316221 prefixEnd_5316221 := by exact prefixLift 5316221
  have htrace : WordTrace (prefixWord ++ tailWord_5316221) baseStart_5316221 baseEnd_5316221 := by
    simpa [prefixWord, tailWord_5316221, baseEnd_5316221] using wordTrace_append hprefix tailTrace_5316221
  have hstable : (prefixWord ++ tailWord_5316221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316221).length < 2 ^ (prefixWord ++ tailWord_5316221).sum := by decide
  have hdescent : baseEnd_5316221 < baseStart_5316221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316254 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_5316254 : Nat := 118140960795 + 5316254 * 2 ^ 59
def prefixEnd_5316254 : Nat := 4983230072969 + 3 ^ 40 * 5316254 * 2
def baseEnd_5316254 : Nat := 909931194462516121825333

theorem tailTrace_5316254 : CollatzResearch.WordTrace tailWord_5316254 prefixEnd_5316254 909931194462516121825333 := by
  unfold tailWord_5316254
  simp only [CollatzResearch.WordTrace]
  refine ⟨24237464110265897092900477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129266475254751451162135877 24237464110265897092900477)
  ·
    refine ⟨9089049041349711409837679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24237464110265897092900477 9089049041349711409837679)
    ·
      refine ⟨13633573562024567114756519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089049041349711409837679 13633573562024567114756519)
      ·
        refine ⟨20450360343036850672134779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633573562024567114756519 20450360343036850672134779)
        ·
          refine ⟨30675540514555276008202169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20450360343036850672134779 30675540514555276008202169)
          ·
            refine ⟨23006655385916457006151627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30675540514555276008202169 23006655385916457006151627)
            ·
              refine ⟨34509983078874685509227441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23006655385916457006151627 34509983078874685509227441)
              ·
                refine ⟨25882487309156014131920581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34509983078874685509227441 25882487309156014131920581)
                ·
                  refine ⟨4852966370466752649735109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25882487309156014131920581 4852966370466752649735109)
                  ·
                    refine ⟨909931194462516121825333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4852966370466752649735109 909931194462516121825333)
                    ·
                      rfl

theorem cell23_5316254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_5316254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316254 prefixEnd_5316254 := by exact prefixLift 5316254
  have htrace : WordTrace (prefixWord ++ tailWord_5316254) baseStart_5316254 baseEnd_5316254 := by
    simpa [prefixWord, tailWord_5316254, baseEnd_5316254] using wordTrace_append hprefix tailTrace_5316254
  have hstable : (prefixWord ++ tailWord_5316254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316254).length < 2 ^ (prefixWord ++ tailWord_5316254).sum := by decide
  have hdescent : baseEnd_5316254 < baseStart_5316254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316255 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5316255 : Nat := 118140960795 + 5316255 * 2 ^ 59
def prefixEnd_5316255 : Nat := 4983230072969 + 3 ^ 40 * 5316255 * 2
def baseEnd_5316255 : Nat := 2729794096868202861563495

theorem tailTrace_5316255 : CollatzResearch.WordTrace tailWord_5316255 prefixEnd_5316255 2729794096868202861563495 := by
  unfold tailWord_5316255
  simp only [CollatzResearch.WordTrace]
  refine ⟨193899749355123553913990219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129266499570082369275993479 193899749355123553913990219)
  ·
    refine ⟨290849624032685330870985329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193899749355123553913990219 290849624032685330870985329)
    ·
      refine ⟨218137218024513998153238997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290849624032685330870985329 218137218024513998153238997)
      ·
        refine ⟨5112591047449546831716539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 218137218024513998153238997 5112591047449546831716539)
        ·
          refine ⟨7668886571174320247574809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5112591047449546831716539 7668886571174320247574809)
          ·
            refine ⟨5751664928380740185681107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7668886571174320247574809 5751664928380740185681107)
            ·
              refine ⟨8627497392571110278521661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751664928380740185681107 8627497392571110278521661)
              ·
                refine ⟨3235311522214166354445623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8627497392571110278521661 3235311522214166354445623)
                ·
                  refine ⟨4852967283321249531668435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235311522214166354445623 4852967283321249531668435)
                  ·
                    refine ⟨7279450924981874297502653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852967283321249531668435 7279450924981874297502653)
                    ·
                      refine ⟨2729794096868202861563495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279450924981874297502653 2729794096868202861563495)
                      ·
                        rfl

theorem cell23_5316255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5316255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316255 prefixEnd_5316255 := by exact prefixLift 5316255
  have htrace : WordTrace (prefixWord ++ tailWord_5316255) baseStart_5316255 baseEnd_5316255 := by
    simpa [prefixWord, tailWord_5316255, baseEnd_5316255] using wordTrace_append hprefix tailTrace_5316255
  have hstable : (prefixWord ++ tailWord_5316255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316255).length < 2 ^ (prefixWord ++ tailWord_5316255).sum := by decide
  have hdescent : baseEnd_5316255 < baseStart_5316255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316298 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_5316298 : Nat := 118140960795 + 5316298 * 2 ^ 59
def prefixEnd_5316298 : Nat := 4983230072969 + 3 ^ 40 * 5316298 * 2
def baseEnd_5316298 : Nat := 2729816176536346193325797

theorem tailTrace_5316298 : CollatzResearch.WordTrace tailWord_5316298 prefixEnd_5316298 2729816176536346193325797 := by
  unfold tailWord_5316298
  simp only [CollatzResearch.WordTrace]
  refine ⟨48475329423491943064451387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129267545129311848171870365 48475329423491943064451387)
  ·
    refine ⟨72712994135237914596677081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48475329423491943064451387 72712994135237914596677081)
    ·
      refine ⟨54534745601428435947507811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72712994135237914596677081 54534745601428435947507811)
      ·
        refine ⟨81802118402142653921261717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54534745601428435947507811 81802118402142653921261717)
        ·
          refine ⟨3834474300100436902559143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81802118402142653921261717 3834474300100436902559143)
          ·
            refine ⟨5751711450150655353838715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834474300100436902559143 5751711450150655353838715)
            ·
              refine ⟨8627567175225983030758073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751711450150655353838715 8627567175225983030758073)
              ·
                refine ⟨6470675381419487273068555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8627567175225983030758073 6470675381419487273068555)
                ·
                  refine ⟨9706013072129230909602833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470675381419487273068555 9706013072129230909602833)
                  ·
                    refine ⟨7279509804096923182202125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9706013072129230909602833 7279509804096923182202125)
                    ·
                      refine ⟨2729816176536346193325797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279509804096923182202125 2729816176536346193325797)
                      ·
                        rfl

theorem cell23_5316298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_5316298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316298 prefixEnd_5316298 := by exact prefixLift 5316298
  have htrace : WordTrace (prefixWord ++ tailWord_5316298) baseStart_5316298 baseEnd_5316298 := by
    simpa [prefixWord, tailWord_5316298, baseEnd_5316298] using wordTrace_append hprefix tailTrace_5316298
  have hstable : (prefixWord ++ tailWord_5316298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316298).length < 2 ^ (prefixWord ++ tailWord_5316298).sum := by decide
  have hdescent : baseEnd_5316298 < baseStart_5316298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316304 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 1, 3, 2]
def baseStart_5316304 : Nat := 118140960795 + 5316304 * 2 ^ 59
def prefixEnd_5316304 : Nat := 4983230072969 + 3 ^ 40 * 5316304 * 2
def baseEnd_5316304 : Nat := 2729819257420273169850769

theorem tailTrace_5316304 : CollatzResearch.WordTrace tailWord_5316304 prefixEnd_5316304 2729819257420273169850769 := by
  unfold tailWord_5316304
  simp only [CollatzResearch.WordTrace]
  refine ⟨96950768265973017641261983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129267691021297356855015977 96950768265973017641261983)
  ·
    refine ⟨145426152398959526461892975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96950768265973017641261983 145426152398959526461892975)
    ·
      refine ⟨218139228598439289692839463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145426152398959526461892975 218139228598439289692839463)
      ·
        refine ⟨327208842897658934539259195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218139228598439289692839463 327208842897658934539259195)
        ·
          refine ⟨490813264346488401808888793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327208842897658934539259195 490813264346488401808888793)
          ·
            refine ⟨368109948259866301356666595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490813264346488401808888793 368109948259866301356666595)
            ·
              refine ⟨552164922389799452034999893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368109948259866301356666595 552164922389799452034999893)
              ·
                refine ⟨6470682684255462328535155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 552164922389799452034999893 6470682684255462328535155)
                ·
                  refine ⟨9706024026383193492802733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470682684255462328535155 9706024026383193492802733)
                  ·
                    refine ⟨3639759009893697559801025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9706024026383193492802733 3639759009893697559801025)
                    ·
                      refine ⟨2729819257420273169850769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639759009893697559801025 2729819257420273169850769)
                      ·
                        rfl

theorem cell23_5316304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 3, 2].length) (baseStart_5316304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316304 prefixEnd_5316304 := by exact prefixLift 5316304
  have htrace : WordTrace (prefixWord ++ tailWord_5316304) baseStart_5316304 baseEnd_5316304 := by
    simpa [prefixWord, tailWord_5316304, baseEnd_5316304] using wordTrace_append hprefix tailTrace_5316304
  have hstable : (prefixWord ++ tailWord_5316304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316304).length < 2 ^ (prefixWord ++ tailWord_5316304).sum := by decide
  have hdescent : baseEnd_5316304 < baseStart_5316304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316334 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_5316334 : Nat := 118140960795 + 5316334 * 2 ^ 59
def prefixEnd_5316334 : Nat := 4983230072969 + 3 ^ 40 * 5316334 * 2
def baseEnd_5316334 : Nat := 2729834661839908052475631

theorem tailTrace_5316334 : CollatzResearch.WordTrace tailWord_5316334 prefixEnd_5316334 2729834661839908052475631 := by
  unfold tailWord_5316334
  simp only [CollatzResearch.WordTrace]
  refine ⟨24237828840229668800764507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129268420481224900270744037 24237828840229668800764507)
  ·
    refine ⟨36356743260344503201146761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24237828840229668800764507 36356743260344503201146761)
    ·
      refine ⟨27267557445258377400860071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36356743260344503201146761 27267557445258377400860071)
      ·
        refine ⟨40901336167887566101290107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27267557445258377400860071 40901336167887566101290107)
        ·
          refine ⟨61352004251831349151935161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40901336167887566101290107 61352004251831349151935161)
          ·
            refine ⟨46014003188873511863951371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61352004251831349151935161 46014003188873511863951371)
            ·
              refine ⟨69021004783310267795927057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46014003188873511863951371 69021004783310267795927057)
              ·
                refine ⟨51765753587482700846945293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69021004783310267795927057 51765753587482700846945293)
                ·
                  refine ⟨19412157595306012817604485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51765753587482700846945293 19412157595306012817604485)
                  ·
                    refine ⟨3639779549119877403300841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19412157595306012817604485 3639779549119877403300841)
                    ·
                      refine ⟨2729834661839908052475631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639779549119877403300841 2729834661839908052475631)
                      ·
                        rfl

theorem cell23_5316334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_5316334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316334 prefixEnd_5316334 := by exact prefixLift 5316334
  have htrace : WordTrace (prefixWord ++ tailWord_5316334) baseStart_5316334 baseEnd_5316334 := by
    simpa [prefixWord, tailWord_5316334, baseEnd_5316334] using wordTrace_append hprefix tailTrace_5316334
  have hstable : (prefixWord ++ tailWord_5316334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316334).length < 2 ^ (prefixWord ++ tailWord_5316334).sum := by decide
  have hdescent : baseEnd_5316334 < baseStart_5316334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316337 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_5316337 : Nat := 118140960795 + 5316337 * 2 ^ 59
def prefixEnd_5316337 : Nat := 4983230072969 + 3 ^ 40 * 5316337 * 2
def baseEnd_5316337 : Nat := 2729836202281871540738117

theorem tailTrace_5316337 : CollatzResearch.WordTrace tailWord_5316337 prefixEnd_5316337 2729836202281871540738117 := by
  unfold tailWord_5316337
  simp only [CollatzResearch.WordTrace]
  refine ⟨193902740140826481918475265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129268493427217654612316843 193902740140826481918475265)
  ·
    refine ⟨145427055105619861438856449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193902740140826481918475265 145427055105619861438856449)
    ·
      refine ⟨109070291329214896079142337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145427055105619861438856449 109070291329214896079142337)
      ·
        refine ⟨81802718496911172059356753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109070291329214896079142337 81802718496911172059356753)
        ·
          refine ⟨61352038872683379044517565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81802718496911172059356753 61352038872683379044517565)
          ·
            refine ⟨23007014577256267141694087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61352038872683379044517565 23007014577256267141694087)
            ·
              refine ⟨34510521865884400712541131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23007014577256267141694087 34510521865884400712541131)
              ·
                refine ⟨51765782798826601068811697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34510521865884400712541131 51765782798826601068811697)
                ·
                  refine ⟨38824337099119950801608773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51765782798826601068811697 38824337099119950801608773)
                  ·
                    refine ⟨7279563206084990775301645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38824337099119950801608773 7279563206084990775301645)
                    ·
                      refine ⟨2729836202281871540738117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279563206084990775301645 2729836202281871540738117)
                      ·
                        rfl

theorem cell23_5316337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_5316337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316337 prefixEnd_5316337 := by exact prefixLift 5316337
  have htrace : WordTrace (prefixWord ++ tailWord_5316337) baseStart_5316337 baseEnd_5316337 := by
    simpa [prefixWord, tailWord_5316337, baseEnd_5316337] using wordTrace_append hprefix tailTrace_5316337
  have hstable : (prefixWord ++ tailWord_5316337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316337).length < 2 ^ (prefixWord ++ tailWord_5316337).sum := by decide
  have hdescent : baseEnd_5316337 < baseStart_5316337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316351 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 2, 2, 2]
def baseStart_5316351 : Nat := 118140960795 + 5316351 * 2 ^ 59
def prefixEnd_5316351 : Nat := 4983230072969 + 3 ^ 40 * 5316351 * 2
def baseEnd_5316351 : Nat := 2729843391011034485963053

theorem tailTrace_5316351 : CollatzResearch.WordTrace tailWord_5316351 prefixEnd_5316351 2729843391011034485963053 := by
  unfold tailWord_5316351
  simp only [CollatzResearch.WordTrace]
  refine ⟨193903250762775762309484907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129268833841850508206323271 193903250762775762309484907)
  ·
    refine ⟨290854876144163643464227361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193903250762775762309484907 290854876144163643464227361)
    ·
      refine ⟨218141157108122732598170521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290854876144163643464227361 218141157108122732598170521)
      ·
        refine ⟨163605867831092049448627891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218141157108122732598170521 163605867831092049448627891)
        ·
          refine ⟨245408801746638074172941837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163605867831092049448627891 245408801746638074172941837)
          ·
            refine ⟨92028300654989277814853189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245408801746638074172941837 92028300654989277814853189)
            ·
              refine ⟨17255306372810489590284973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92028300654989277814853189 17255306372810489590284973)
              ·
                refine ⟨6470739889803933596356865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17255306372810489590284973 6470739889803933596356865)
                ·
                  refine ⟨4853054917352950197267649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6470739889803933596356865 4853054917352950197267649)
                  ·
                    refine ⟨3639791188014712647950737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4853054917352950197267649 3639791188014712647950737)
                    ·
                      refine ⟨2729843391011034485963053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639791188014712647950737 2729843391011034485963053)
                      ·
                        rfl

theorem cell23_5316351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_5316351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316351 prefixEnd_5316351 := by exact prefixLift 5316351
  have htrace : WordTrace (prefixWord ++ tailWord_5316351) baseStart_5316351 baseEnd_5316351 := by
    simpa [prefixWord, tailWord_5316351, baseEnd_5316351] using wordTrace_append hprefix tailTrace_5316351
  have hstable : (prefixWord ++ tailWord_5316351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316351).length < 2 ^ (prefixWord ++ tailWord_5316351).sum := by decide
  have hdescent : baseEnd_5316351 < baseStart_5316351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316354 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_5316354 : Nat := 118140960795 + 5316354 * 2 ^ 59
def prefixEnd_5316354 : Nat := 4983230072969 + 3 ^ 40 * 5316354 * 2
def baseEnd_5316354 : Nat := 2729844931452997974225539

theorem tailTrace_5316354 : CollatzResearch.WordTrace tailWord_5316354 prefixEnd_5316354 2729844931452997974225539 := by
  unfold tailWord_5316354
  simp only [CollatzResearch.WordTrace]
  refine ⟨48475840045441223455461029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129268906787843262547896077 48475840045441223455461029)
  ·
    refine ⟨9089220008520229397898943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48475840045441223455461029 9089220008520229397898943)
    ·
      refine ⟨13633830012780344096848415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089220008520229397898943 13633830012780344096848415)
      ·
        refine ⟨20450745019170516145272623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633830012780344096848415 20450745019170516145272623)
        ·
          refine ⟨30676117528755774217908935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20450745019170516145272623 30676117528755774217908935)
          ·
            refine ⟨46014176293133661326863403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30676117528755774217908935 46014176293133661326863403)
            ·
              refine ⟨69021264439700491990295105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46014176293133661326863403 69021264439700491990295105)
              ·
                refine ⟨51765948329775368992721329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69021264439700491990295105 51765948329775368992721329)
                ·
                  refine ⟨38824461247331526744540997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51765948329775368992721329 38824461247331526744540997)
                  ·
                    refine ⟨7279586483874661264601437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38824461247331526744540997 7279586483874661264601437)
                    ·
                      refine ⟨2729844931452997974225539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279586483874661264601437 2729844931452997974225539)
                      ·
                        rfl

theorem cell23_5316354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_5316354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316354 prefixEnd_5316354 := by exact prefixLift 5316354
  have htrace : WordTrace (prefixWord ++ tailWord_5316354) baseStart_5316354 baseEnd_5316354 := by
    simpa [prefixWord, tailWord_5316354, baseEnd_5316354] using wordTrace_append hprefix tailTrace_5316354
  have hstable : (prefixWord ++ tailWord_5316354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316354).length < 2 ^ (prefixWord ++ tailWord_5316354).sum := by decide
  have hdescent : baseEnd_5316354 < baseStart_5316354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316372 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5316372 : Nat := 118140960795 + 5316372 * 2 ^ 59
def prefixEnd_5316372 : Nat := 4983230072969 + 3 ^ 40 * 5316372 * 2
def baseEnd_5316372 : Nat := 2729854174104778903800457

theorem tailTrace_5316372 : CollatzResearch.WordTrace tailWord_5316372 prefixEnd_5316372 2729854174104778903800457 := by
  unfold tailWord_5316372
  simp only [CollatzResearch.WordTrace]
  refine ⟨96952008347849841447999685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129269344463799788597332913 96952008347849841447999685)
  ·
    refine ⟨18178501565221845271499941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96952008347849841447999685 18178501565221845271499941)
    ·
      refine ⟨3408469043479095988406239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18178501565221845271499941 3408469043479095988406239)
      ·
        refine ⟨5112703565218643982609359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408469043479095988406239 5112703565218643982609359)
        ·
          refine ⟨7669055347827965973914039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5112703565218643982609359 7669055347827965973914039)
          ·
            refine ⟨11503583021741948960871059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669055347827965973914039 11503583021741948960871059)
            ·
              refine ⟨17255374532612923441306589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11503583021741948960871059 17255374532612923441306589)
              ·
                refine ⟨6470765449729846290489971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17255374532612923441306589 6470765449729846290489971)
                ·
                  refine ⟨9706148174594769435734957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470765449729846290489971 9706148174594769435734957)
                  ·
                    refine ⟨3639805565473038538400609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9706148174594769435734957 3639805565473038538400609)
                    ·
                      refine ⟨2729854174104778903800457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639805565473038538400609 2729854174104778903800457)
                      ·
                        rfl

theorem cell23_5316372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5316372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316372 prefixEnd_5316372 := by exact prefixLift 5316372
  have htrace : WordTrace (prefixWord ++ tailWord_5316372) baseStart_5316372 baseEnd_5316372 := by
    simpa [prefixWord, tailWord_5316372, baseEnd_5316372] using wordTrace_append hprefix tailTrace_5316372
  have hstable : (prefixWord ++ tailWord_5316372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316372).length < 2 ^ (prefixWord ++ tailWord_5316372).sum := by decide
  have hdescent : baseEnd_5316372 < baseStart_5316372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316387 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 2, 5]
def baseStart_5316387 : Nat := 118140960795 + 5316387 * 2 ^ 59
def prefixEnd_5316387 : Nat := 4983230072969 + 3 ^ 40 * 5316387 * 2
def baseEnd_5316387 : Nat := 909953958771532115037629

theorem tailTrace_5316387 : CollatzResearch.WordTrace tailWord_5316387 prefixEnd_5316387 909953958771532115037629 := by
  unfold tailWord_5316387
  simp only [CollatzResearch.WordTrace]
  refine ⟨193904563790645340457795415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129269709193763560305196943 193904563790645340457795415)
  ·
    refine ⟨290856845685968010686693123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193904563790645340457795415 290856845685968010686693123)
    ·
      refine ⟨436285268528952016030039685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290856845685968010686693123 436285268528952016030039685)
      ·
        refine ⟨81803487849178503005632441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 436285268528952016030039685 81803487849178503005632441)
        ·
          refine ⟨61352615886883877254224331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81803487849178503005632441 61352615886883877254224331)
          ·
            refine ⟨92028923830325815881336497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61352615886883877254224331 92028923830325815881336497)
            ·
              refine ⟨69021692872744361911002373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92028923830325815881336497 69021692872744361911002373)
              ·
                refine ⟨12941567413639567858312945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69021692872744361911002373 12941567413639567858312945)
                ·
                  refine ⟨9706175560229675893734709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12941567413639567858312945 9706175560229675893734709)
                  ·
                    refine ⟨909953958771532115037629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9706175560229675893734709 909953958771532115037629)
                    ·
                      rfl

theorem cell23_5316387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 5].length) (baseStart_5316387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316387 prefixEnd_5316387 := by exact prefixLift 5316387
  have htrace : WordTrace (prefixWord ++ tailWord_5316387) baseStart_5316387 baseEnd_5316387 := by
    simpa [prefixWord, tailWord_5316387, baseEnd_5316387] using wordTrace_append hprefix tailTrace_5316387
  have hstable : (prefixWord ++ tailWord_5316387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316387).length < 2 ^ (prefixWord ++ tailWord_5316387).sum := by decide
  have hdescent : baseEnd_5316387 < baseStart_5316387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316404 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5316404 : Nat := 118140960795 + 5316404 * 2 ^ 59
def prefixEnd_5316404 : Nat := 4983230072969 + 3 ^ 40 * 5316404 * 2
def baseEnd_5316404 : Nat := 909956868495240926200103

theorem tailTrace_5316404 : CollatzResearch.WordTrace tailWord_5316404 prefixEnd_5316404 909956868495240926200103 := by
  unfold tailWord_5316404
  simp only [CollatzResearch.WordTrace]
  refine ⟨96952591915791876180582133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129270122554389168240776177 96952591915791876180582133)
  ·
    refine ⟨9089305492105488391929575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96952591915791876180582133 9089305492105488391929575)
    ·
      refine ⟨13633958238158232587894363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089305492105488391929575 13633958238158232587894363)
      ·
        refine ⟨20450937357237348881841545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633958238158232587894363 20450937357237348881841545)
        ·
          refine ⟨15338203017928011661381159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20450937357237348881841545 15338203017928011661381159)
          ·
            refine ⟨23007304526892017492071739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15338203017928011661381159 23007304526892017492071739)
            ·
              refine ⟨34510956790338026238107609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23007304526892017492071739 34510956790338026238107609)
              ·
                refine ⟨25883217592753519678580707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34510956790338026238107609 25883217592753519678580707)
                ·
                  refine ⟨38824826389130279517871061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25883217592753519678580707 38824826389130279517871061)
                  ·
                    refine ⟨909956868495240926200103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38824826389130279517871061 909956868495240926200103)
                    ·
                      rfl

theorem cell23_5316404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5316404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316404 prefixEnd_5316404 := by exact prefixLift 5316404
  have htrace : WordTrace (prefixWord ++ tailWord_5316404) baseStart_5316404 baseEnd_5316404 := by
    simpa [prefixWord, tailWord_5316404, baseEnd_5316404] using wordTrace_append hprefix tailTrace_5316404
  have hstable : (prefixWord ++ tailWord_5316404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316404).length < 2 ^ (prefixWord ++ tailWord_5316404).sum := by decide
  have hdescent : baseEnd_5316404 < baseStart_5316404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316407 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_5316407 : Nat := 118140960795 + 5316407 * 2 ^ 59
def prefixEnd_5316407 : Nat := 4983230072969 + 3 ^ 40 * 5316407 * 2
def baseEnd_5316407 : Nat := 2729872145927686266862795

theorem tailTrace_5316407 : CollatzResearch.WordTrace tailWord_5316407 prefixEnd_5316407 2729872145927686266862795 := by
  unfold tailWord_5316407
  simp only [CollatzResearch.WordTrace]
  refine ⟨193905293250572883873523475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129270195500381922582348983 193905293250572883873523475)
  ·
    refine ⟨290857939875859325810285213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193905293250572883873523475 290857939875859325810285213)
    ·
      refine ⟨109071727453447247178856955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290857939875859325810285213 109071727453447247178856955)
      ·
        refine ⟨163607591180170870768285433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109071727453447247178856955 163607591180170870768285433)
        ·
          refine ⟨122705693385128153076214075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163607591180170870768285433 122705693385128153076214075)
          ·
            refine ⟨184058540077692229614321113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122705693385128153076214075 184058540077692229614321113)
            ·
              refine ⟨138043905058269172210740835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184058540077692229614321113 138043905058269172210740835)
              ·
                refine ⟨207065857587403758316111253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138043905058269172210740835 207065857587403758316111253)
                ·
                  refine ⟨9706212074409551171067715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207065857587403758316111253 9706212074409551171067715)
                  ·
                    refine ⟨14559318111614326756601573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9706212074409551171067715 14559318111614326756601573)
                    ·
                      refine ⟨2729872145927686266862795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14559318111614326756601573 2729872145927686266862795)
                      ·
                        rfl

theorem cell23_5316407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_5316407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316407 prefixEnd_5316407 := by exact prefixLift 5316407
  have htrace : WordTrace (prefixWord ++ tailWord_5316407) baseStart_5316407 baseEnd_5316407 := by
    simpa [prefixWord, tailWord_5316407, baseEnd_5316407] using wordTrace_append hprefix tailTrace_5316407
  have hstable : (prefixWord ++ tailWord_5316407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316407).length < 2 ^ (prefixWord ++ tailWord_5316407).sum := by decide
  have hdescent : baseEnd_5316407 < baseStart_5316407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316447 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 8]
def baseStart_5316447 : Nat := 118140960795 + 5316447 * 2 ^ 59
def prefixEnd_5316447 : Nat := 4983230072969 + 3 ^ 40 * 5316447 * 2
def baseEnd_5316447 : Nat := 303321409461540678929179

theorem tailTrace_5316447 : CollatzResearch.WordTrace tailWord_5316447 prefixEnd_5316447 303321409461540678929179 := by
  unfold tailWord_5316447
  simp only [CollatzResearch.WordTrace]
  refine ⟨193906752170427970704979595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129271168113618647136653063 193906752170427970704979595)
  ·
    refine ⟨290860128255641956057469393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193906752170427970704979595 290860128255641956057469393)
    ·
      refine ⟨218145096191731467043102045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290860128255641956057469393 218145096191731467043102045)
      ·
        refine ⟨81804411071899300141163267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218145096191731467043102045 81804411071899300141163267)
        ·
          refine ⟨122706616607848950211744901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81804411071899300141163267 122706616607848950211744901)
          ·
            refine ⟨23007490613971678164702169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122706616607848950211744901 23007490613971678164702169)
            ·
              refine ⟨17255617960478758623526627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23007490613971678164702169 17255617960478758623526627)
              ·
                refine ⟨25883426940718137935289941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17255617960478758623526627 25883426940718137935289941)
                ·
                  refine ⟨303321409461540678929179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25883426940718137935289941 303321409461540678929179)
                  ·
                    rfl

theorem cell23_5316447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 8].length) (baseStart_5316447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316447 prefixEnd_5316447 := by exact prefixLift 5316447
  have htrace : WordTrace (prefixWord ++ tailWord_5316447) baseStart_5316447 baseEnd_5316447 := by
    simpa [prefixWord, tailWord_5316447, baseEnd_5316447] using wordTrace_append hprefix tailTrace_5316447
  have hstable : (prefixWord ++ tailWord_5316447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316447).length < 2 ^ (prefixWord ++ tailWord_5316447).sum := by decide
  have hdescent : baseEnd_5316447 < baseStart_5316447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316478 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5316478 : Nat := 118140960795 + 5316478 * 2 ^ 59
def prefixEnd_5316478 : Nat := 4983230072969 + 3 ^ 40 * 5316478 * 2
def baseEnd_5316478 : Nat := 2729908603054155489074969

theorem tailTrace_5316478 : CollatzResearch.WordTrace tailWord_5316478 prefixEnd_5316478 2729908603054155489074969 := by
  unfold tailWord_5316478
  simp only [CollatzResearch.WordTrace]
  refine ⟨24238485354164457874919761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129271921888877108666238725 24238485354164457874919761)
  ·
    refine ⟨18178864015623343406189821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24238485354164457874919761 18178864015623343406189821)
    ·
      refine ⟨6817074005858753777321183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18178864015623343406189821 6817074005858753777321183)
      ·
        refine ⟨10225611008788130665981775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817074005858753777321183 10225611008788130665981775)
        ·
          refine ⟨15338416513182195998972663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10225611008788130665981775 15338416513182195998972663)
          ·
            refine ⟨23007624769773293998458995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15338416513182195998972663 23007624769773293998458995)
            ·
              refine ⟨34511437154659940997688493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23007624769773293998458995 34511437154659940997688493)
              ·
                refine ⟨12941788932997477874133185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34511437154659940997688493 12941788932997477874133185)
                ·
                  refine ⟨9706341699748108405599889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12941788932997477874133185 9706341699748108405599889)
                  ·
                    refine ⟨7279756274811081304199917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9706341699748108405599889 7279756274811081304199917)
                    ·
                      refine ⟨2729908603054155489074969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279756274811081304199917 2729908603054155489074969)
                      ·
                        rfl

theorem cell23_5316478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5316478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316478 prefixEnd_5316478 := by exact prefixLift 5316478
  have htrace : WordTrace (prefixWord ++ tailWord_5316478) baseStart_5316478 baseEnd_5316478 := by
    simpa [prefixWord, tailWord_5316478, baseEnd_5316478] using wordTrace_append hprefix tailTrace_5316478
  have hstable : (prefixWord ++ tailWord_5316478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316478).length < 2 ^ (prefixWord ++ tailWord_5316478).sum := by decide
  have hdescent : baseEnd_5316478 < baseStart_5316478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316501 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_5316501 : Nat := 118140960795 + 5316501 * 2 ^ 59
def prefixEnd_5316501 : Nat := 4983230072969 + 3 ^ 40 * 5316501 * 2
def baseEnd_5316501 : Nat := 2729920413109208899087363

theorem tailTrace_5316501 : CollatzResearch.WordTrace tailWord_5316501 prefixEnd_5316501 2729920413109208899087363 := by
  unfold tailWord_5316501
  simp only [CollatzResearch.WordTrace]
  refine ⟨193908721712232337927445357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129272481141488225284963571 193908721712232337927445357)
  ·
    refine ⟨72715770642087126722792009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193908721712232337927445357 72715770642087126722792009)
    ·
      refine ⟨54536827981565345042094007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72715770642087126722792009 54536827981565345042094007)
      ·
        refine ⟨81805241972348017563141011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54536827981565345042094007 81805241972348017563141011)
        ·
          refine ⟨122707862958522026344711517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81805241972348017563141011 122707862958522026344711517)
          ·
            refine ⟨46015448609445759879266819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122707862958522026344711517 46015448609445759879266819)
            ·
              refine ⟨69023172914168639818900229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46015448609445759879266819 69023172914168639818900229)
              ·
                refine ⟨12941844921406619966043793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69023172914168639818900229 12941844921406619966043793)
                ·
                  refine ⟨9706383691054964974532845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12941844921406619966043793 9706383691054964974532845)
                  ·
                    refine ⟨3639893884145611865449817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9706383691054964974532845 3639893884145611865449817)
                    ·
                      refine ⟨2729920413109208899087363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639893884145611865449817 2729920413109208899087363)
                      ·
                        rfl

theorem cell23_5316501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_5316501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316501 prefixEnd_5316501 := by exact prefixLift 5316501
  have htrace : WordTrace (prefixWord ++ tailWord_5316501) baseStart_5316501 baseEnd_5316501 := by
    simpa [prefixWord, tailWord_5316501, baseEnd_5316501] using wordTrace_append hprefix tailTrace_5316501
  have hstable : (prefixWord ++ tailWord_5316501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316501).length < 2 ^ (prefixWord ++ tailWord_5316501).sum := by decide
  have hdescent : baseEnd_5316501 < baseStart_5316501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316544 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_5316544 : Nat := 118140960795 + 5316544 * 2 ^ 59
def prefixEnd_5316544 : Nat := 4983230072969 + 3 ^ 40 * 5316544 * 2
def baseEnd_5316544 : Nat := 2729942492777352230849665

theorem tailTrace_5316544 : CollatzResearch.WordTrace tailWord_5316544 prefixEnd_5316544 2729942492777352230849665 := by
  unfold tailWord_5316544
  simp only [CollatzResearch.WordTrace]
  refine ⟨96955145025538278135630343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129273526700717704180840457 96955145025538278135630343)
  ·
    refine ⟨145432717538307417203445515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96955145025538278135630343 145432717538307417203445515)
    ·
      refine ⟨218149076307461125805168273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145432717538307417203445515 218149076307461125805168273)
      ·
        refine ⟨163611807230595844353876205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218149076307461125805168273 163611807230595844353876205)
        ·
          refine ⟨61354427711473441632703577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163611807230595844353876205 61354427711473441632703577)
          ·
            refine ⟨46015820783605081224527683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61354427711473441632703577 46015820783605081224527683)
            ·
              refine ⟨69023731175407621836791525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46015820783605081224527683 69023731175407621836791525)
              ·
                refine ⟨12941949595388929094398411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69023731175407621836791525 12941949595388929094398411)
                ·
                  refine ⟨19412924393083393641597617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12941949595388929094398411 19412924393083393641597617)
                  ·
                    refine ⟨14559693294812545231198213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19412924393083393641597617 14559693294812545231198213)
                    ·
                      refine ⟨2729942492777352230849665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14559693294812545231198213 2729942492777352230849665)
                      ·
                        rfl

theorem cell23_5316544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_5316544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316544 prefixEnd_5316544 := by exact prefixLift 5316544
  have htrace : WordTrace (prefixWord ++ tailWord_5316544) baseStart_5316544 baseEnd_5316544 := by
    simpa [prefixWord, tailWord_5316544, baseEnd_5316544] using wordTrace_append hprefix tailTrace_5316544
  have hstable : (prefixWord ++ tailWord_5316544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316544).length < 2 ^ (prefixWord ++ tailWord_5316544).sum := by decide
  have hdescent : baseEnd_5316544 < baseStart_5316544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316565 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5316565 : Nat := 118140960795 + 5316565 * 2 ^ 59
def prefixEnd_5316565 : Nat := 4983230072969 + 3 ^ 40 * 5316565 * 2
def baseEnd_5316565 : Nat := 2729953275871096648687069

theorem tailTrace_5316565 : CollatzResearch.WordTrace tailWord_5316565 prefixEnd_5316565 2729953275871096648687069 := by
  unfold tailWord_5316565
  simp only [CollatzResearch.WordTrace]
  refine ⟨193911055984000476857775149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129274037322666984571850099 193911055984000476857775149)
  ·
    refine ⟨72716645994000178821665681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193911055984000476857775149 72716645994000178821665681)
    ·
      refine ⟨54537484495500134116249261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72716645994000178821665681 54537484495500134116249261)
      ·
        refine ⟨20451556685812550293593473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54537484495500134116249261 20451556685812550293593473)
        ·
          refine ⟨15338667514359412720195105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20451556685812550293593473 15338667514359412720195105)
          ·
            refine ⟨11504000635769559540146329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15338667514359412720195105 11504000635769559540146329)
            ·
              refine ⟨8628000476827169655109747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11504000635769559540146329 8628000476827169655109747)
              ·
                refine ⟨12942000715240754482664621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8628000476827169655109747 12942000715240754482664621)
                ·
                  refine ⟨4853250268215282930999233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12942000715240754482664621 4853250268215282930999233)
                  ·
                    refine ⟨3639937701161462198249425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4853250268215282930999233 3639937701161462198249425)
                    ·
                      refine ⟨2729953275871096648687069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639937701161462198249425 2729953275871096648687069)
                      ·
                        rfl

theorem cell23_5316565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5316565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316565 prefixEnd_5316565 := by exact prefixLift 5316565
  have htrace : WordTrace (prefixWord ++ tailWord_5316565) baseStart_5316565 baseEnd_5316565 := by
    simpa [prefixWord, tailWord_5316565, baseEnd_5316565] using wordTrace_append hprefix tailTrace_5316565
  have hstable : (prefixWord ++ tailWord_5316565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316565).length < 2 ^ (prefixWord ++ tailWord_5316565).sum := by decide
  have hdescent : baseEnd_5316565 < baseStart_5316565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316578 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5316578 : Nat := 118140960795 + 5316578 * 2 ^ 59
def prefixEnd_5316578 : Nat := 4983230072969 + 3 ^ 40 * 5316578 * 2
def baseEnd_5316578 : Nat := 2729959951119605097824509

theorem tailTrace_5316578 : CollatzResearch.WordTrace tailWord_5316578 prefixEnd_5316578 2729959951119605097824509 := by
  unfold tailWord_5316578
  simp only [CollatzResearch.WordTrace]
  refine ⟨48477882533238345019499597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129274353421968920051998925 48477882533238345019499597)
  ·
    refine ⟨18179205949964379382312349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48477882533238345019499597 18179205949964379382312349)
    ·
      refine ⟨6817202231236642268367131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18179205949964379382312349 6817202231236642268367131)
      ·
        refine ⟨10225803346854963402550697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817202231236642268367131 10225803346854963402550697)
        ·
          refine ⟨7669352510141222551913023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10225803346854963402550697 7669352510141222551913023)
          ·
            refine ⟨11504028765211833827869535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669352510141222551913023 11504028765211833827869535)
            ·
              refine ⟨17256043147817750741804303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504028765211833827869535 17256043147817750741804303)
              ·
                refine ⟨25884064721726626112706455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17256043147817750741804303 25884064721726626112706455)
                ·
                  refine ⟨38826097082589939169059683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25884064721726626112706455 38826097082589939169059683)
                  ·
                    refine ⟨58239145623884908753589525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38826097082589939169059683 58239145623884908753589525)
                    ·
                      refine ⟨2729959951119605097824509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58239145623884908753589525 2729959951119605097824509)
                      ·
                        rfl

theorem cell23_5316578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5316578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316578 prefixEnd_5316578 := by exact prefixLift 5316578
  have htrace : WordTrace (prefixWord ++ tailWord_5316578) baseStart_5316578 baseEnd_5316578 := by
    simpa [prefixWord, tailWord_5316578, baseEnd_5316578] using wordTrace_append hprefix tailTrace_5316578
  have hstable : (prefixWord ++ tailWord_5316578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316578).length < 2 ^ (prefixWord ++ tailWord_5316578).sum := by decide
  have hdescent : baseEnd_5316578 < baseStart_5316578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316624 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_5316624 : Nat := 118140960795 + 5316624 * 2 ^ 59
def prefixEnd_5316624 : Nat := 4983230072969 + 3 ^ 40 * 5316624 * 2
def baseEnd_5316624 : Nat := 2729983571229711917849297

theorem tailTrace_5316624 : CollatzResearch.WordTrace tailWord_5316624 prefixEnd_5316624 2729983571229711917849297 := by
  unfold tailWord_5316624
  simp only [CollatzResearch.WordTrace]
  refine ⟨96956603945393364967086463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129275471927191153289448617 96956603945393364967086463)
  ·
    refine ⟨145434905918090047450629695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96956603945393364967086463 145434905918090047450629695)
    ·
      refine ⟨218152358877135071175944543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145434905918090047450629695 218152358877135071175944543)
      ·
        refine ⟨327228538315702606763916815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218152358877135071175944543 327228538315702606763916815)
        ·
          refine ⟨490842807473553910145875223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327228538315702606763916815 490842807473553910145875223)
          ·
            refine ⟨736264211210330865218812835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490842807473553910145875223 736264211210330865218812835)
            ·
              refine ⟨1104396316815496297828219253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736264211210330865218812835 1104396316815496297828219253)
              ·
                refine ⟨103537154701452777921395555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104396316815496297828219253 103537154701452777921395555)
                ·
                  refine ⟨155305732052179166882093333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103537154701452777921395555 155305732052179166882093333)
                  ·
                    refine ⟨7279956189945898447598125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 155305732052179166882093333 7279956189945898447598125)
                    ·
                      refine ⟨2729983571229711917849297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7279956189945898447598125 2729983571229711917849297)
                      ·
                        rfl

theorem cell23_5316624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_5316624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316624 prefixEnd_5316624 := by exact prefixLift 5316624
  have htrace : WordTrace (prefixWord ++ tailWord_5316624) baseStart_5316624 baseEnd_5316624 := by
    simpa [prefixWord, tailWord_5316624, baseEnd_5316624] using wordTrace_append hprefix tailTrace_5316624
  have hstable : (prefixWord ++ tailWord_5316624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316624).length < 2 ^ (prefixWord ++ tailWord_5316624).sum := by decide
  have hdescent : baseEnd_5316624 < baseStart_5316624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316678 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_5316678 : Nat := 118140960795 + 5316678 * 2 ^ 59
def prefixEnd_5316678 : Nat := 4983230072969 + 3 ^ 40 * 5316678 * 2
def baseEnd_5316678 : Nat := 303334588798339411841561

theorem tailTrace_5316678 : CollatzResearch.WordTrace tailWord_5316678 prefixEnd_5316678 303334588798339411841561 := by
  unfold tailWord_5316678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6059849294768471786144959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129276784955060731437759125 6059849294768471786144959)
  ·
    refine ⟨9089773942152707679217439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6059849294768471786144959 9089773942152707679217439)
    ·
      refine ⟨13634660913229061518826159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089773942152707679217439 13634660913229061518826159)
      ·
        refine ⟨20451991369843592278239239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13634660913229061518826159 20451991369843592278239239)
        ·
          refine ⟨30677987054765388417358859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20451991369843592278239239 30677987054765388417358859)
          ·
            refine ⟨46016980582148082626038289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30677987054765388417358859 46016980582148082626038289)
            ·
              refine ⟨34512735436611061969528717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46016980582148082626038289 34512735436611061969528717)
              ·
                refine ⟨12942275788729148238573269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34512735436611061969528717 12942275788729148238573269)
                ·
                  refine ⟨303334588798339411841561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12942275788729148238573269 303334588798339411841561)
                  ·
                    rfl

theorem cell23_5316678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_5316678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316678 prefixEnd_5316678 := by exact prefixLift 5316678
  have htrace : WordTrace (prefixWord ++ tailWord_5316678) baseStart_5316678 baseEnd_5316678 := by
    simpa [prefixWord, tailWord_5316678, baseEnd_5316678] using wordTrace_append hprefix tailTrace_5316678
  have hstable : (prefixWord ++ tailWord_5316678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316678).length < 2 ^ (prefixWord ++ tailWord_5316678).sum := by decide
  have hdescent : baseEnd_5316678 < baseStart_5316678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316681 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 7, 2]
def baseStart_5316681 : Nat := 118140960795 + 5316681 * 2 ^ 59
def prefixEnd_5316681 : Nat := 4983230072969 + 3 ^ 40 * 5316681 * 2
def baseEnd_5316681 : Nat := 2730012839627018194836535

theorem tailTrace_5316681 : CollatzResearch.WordTrace tailWord_5316681 prefixEnd_5316681 2730012839627018194836535 := by
  unfold tailWord_5316681
  simp only [CollatzResearch.WordTrace]
  refine ⟨193915286851580228668997897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129276857901053485779331931 193915286851580228668997897)
  ·
    refine ⟨145436465138685171501748423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193915286851580228668997897 145436465138685171501748423)
    ·
      refine ⟨218154697708027757252622635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145436465138685171501748423 218154697708027757252622635)
      ·
        refine ⟨327232046562041635878933953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218154697708027757252622635 327232046562041635878933953)
        ·
          refine ⟨245424034921531226909200465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327232046562041635878933953 245424034921531226909200465)
          ·
            refine ⟨184068026191148420181900349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245424034921531226909200465 184068026191148420181900349)
            ·
              refine ⟨69025509821680657568212631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184068026191148420181900349 69025509821680657568212631)
              ·
                refine ⟨103538264732520986352318947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69025509821680657568212631 103538264732520986352318947)
                ·
                  refine ⟨155307397098781479528478421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103538264732520986352318947 155307397098781479528478421)
                  ·
                    refine ⟨3640017119502690926448713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155307397098781479528478421 3640017119502690926448713)
                    ·
                      refine ⟨2730012839627018194836535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640017119502690926448713 2730012839627018194836535)
                      ·
                        rfl

theorem cell23_5316681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 7, 2].length) (baseStart_5316681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316681 prefixEnd_5316681 := by exact prefixLift 5316681
  have htrace : WordTrace (prefixWord ++ tailWord_5316681) baseStart_5316681 baseEnd_5316681 := by
    simpa [prefixWord, tailWord_5316681, baseEnd_5316681] using wordTrace_append hprefix tailTrace_5316681
  have hstable : (prefixWord ++ tailWord_5316681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316681).length < 2 ^ (prefixWord ++ tailWord_5316681).sum := by decide
  have hdescent : baseEnd_5316681 < baseStart_5316681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316711 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5316711 : Nat := 118140960795 + 5316711 * 2 ^ 59
def prefixEnd_5316711 : Nat := 4983230072969 + 3 ^ 40 * 5316711 * 2
def baseEnd_5316711 : Nat := 2730028244046653077461397

theorem tailTrace_5316711 : CollatzResearch.WordTrace tailWord_5316711 prefixEnd_5316711 2730028244046653077461397 := by
  unfold tailWord_5316711
  simp only [CollatzResearch.WordTrace]
  refine ⟨193916381041471543792589987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129277587360981029195059991 193916381041471543792589987)
  ·
    refine ⟨290874571562207315688884981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193916381041471543792589987 290874571562207315688884981)
    ·
      refine ⟨27269491083956935845832967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 290874571562207315688884981 27269491083956935845832967)
      ·
        refine ⟨40904236625935403768749451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27269491083956935845832967 40904236625935403768749451)
        ·
          refine ⟨61356354938903105653124177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40904236625935403768749451 61356354938903105653124177)
          ·
            refine ⟨46017266204177329239843133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61356354938903105653124177 46017266204177329239843133)
            ·
              refine ⟨17256474826566498464941175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46017266204177329239843133 17256474826566498464941175)
              ·
                refine ⟨25884712239849747697411763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17256474826566498464941175 25884712239849747697411763)
                ·
                  refine ⟨38827068359774621546117645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25884712239849747697411763 38827068359774621546117645)
                  ·
                    refine ⟨14560150634915483079794117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38827068359774621546117645 14560150634915483079794117)
                    ·
                      refine ⟨2730028244046653077461397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14560150634915483079794117 2730028244046653077461397)
                      ·
                        rfl

theorem cell23_5316711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5316711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316711 prefixEnd_5316711 := by exact prefixLift 5316711
  have htrace : WordTrace (prefixWord ++ tailWord_5316711) baseStart_5316711 baseEnd_5316711 := by
    simpa [prefixWord, tailWord_5316711, baseEnd_5316711] using wordTrace_append hprefix tailTrace_5316711
  have hstable : (prefixWord ++ tailWord_5316711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316711).length < 2 ^ (prefixWord ++ tailWord_5316711).sum := by decide
  have hdescent : baseEnd_5316711 < baseStart_5316711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316721 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 5, 4]
def baseStart_5316721 : Nat := 118140960795 + 5316721 * 2 ^ 59
def prefixEnd_5316721 : Nat := 4983230072969 + 3 ^ 40 * 5316721 * 2
def baseEnd_5316721 : Nat := 910011126284399346112117

theorem tailTrace_5316721 : CollatzResearch.WordTrace tailWord_5316721 prefixEnd_5316721 910011126284399346112117 := by
  unfold tailWord_5316721
  simp only [CollatzResearch.WordTrace]
  refine ⟨193916745771435315500454017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129277830514290210333636011 193916745771435315500454017)
  ·
    refine ⟨145437559328576486625340513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193916745771435315500454017 145437559328576486625340513)
    ·
      refine ⟨109078169496432364969005385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145437559328576486625340513 109078169496432364969005385)
      ·
        refine ⟨81808627122324273726754039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109078169496432364969005385 81808627122324273726754039)
        ·
          refine ⟨122712940683486410590131059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81808627122324273726754039 122712940683486410590131059)
          ·
            refine ⟨184069411025229615885196589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122712940683486410590131059 184069411025229615885196589)
            ·
              refine ⟨69026029134461105956948721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184069411025229615885196589 69026029134461105956948721)
              ·
                refine ⟨51769521850845829467711541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69026029134461105956948721 51769521850845829467711541)
                ·
                  refine ⟨4853392673516796512597957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51769521850845829467711541 4853392673516796512597957)
                  ·
                    refine ⟨910011126284399346112117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4853392673516796512597957 910011126284399346112117)
                    ·
                      rfl

theorem cell23_5316721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_5316721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316721 prefixEnd_5316721 := by exact prefixLift 5316721
  have htrace : WordTrace (prefixWord ++ tailWord_5316721) baseStart_5316721 baseEnd_5316721 := by
    simpa [prefixWord, tailWord_5316721, baseEnd_5316721] using wordTrace_append hprefix tailTrace_5316721
  have hstable : (prefixWord ++ tailWord_5316721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316721).length < 2 ^ (prefixWord ++ tailWord_5316721).sum := by decide
  have hdescent : baseEnd_5316721 < baseStart_5316721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316789 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_5316789 : Nat := 118140960795 + 5316789 * 2 ^ 59
def prefixEnd_5316789 : Nat := 4983230072969 + 3 ^ 40 * 5316789 * 2
def baseEnd_5316789 : Nat := 910022765179234590762013

theorem tailTrace_5316789 : CollatzResearch.WordTrace tailWord_5316789 prefixEnd_5316789 910022765179234590762013 := by
  unfold tailWord_5316789
  simp only [CollatzResearch.WordTrace]
  refine ⟨193919225935188963113929421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129279483956792642075952947 193919225935188963113929421)
  ·
    refine ⟨72719709725695861167723533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193919225935188963113929421 72719709725695861167723533)
    ·
      refine ⟨27269891147135947937896325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72719709725695861167723533 27269891147135947937896325)
      ·
        refine ⟨5113104590087990238355561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27269891147135947937896325 5113104590087990238355561)
        ·
          refine ⟨3834828442565992678766671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5113104590087990238355561 3834828442565992678766671)
          ·
            refine ⟨5752242663848989018150007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834828442565992678766671 5752242663848989018150007)
            ·
              refine ⟨8628363995773483527225011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752242663848989018150007 8628363995773483527225011)
              ·
                refine ⟨12942545993660225290837517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8628363995773483527225011 12942545993660225290837517)
                ·
                  refine ⟨4853454747622584484064069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12942545993660225290837517 4853454747622584484064069)
                  ·
                    refine ⟨910022765179234590762013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4853454747622584484064069 910022765179234590762013)
                    ·
                      rfl

theorem cell23_5316789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_5316789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316789 prefixEnd_5316789 := by exact prefixLift 5316789
  have htrace : WordTrace (prefixWord ++ tailWord_5316789) baseStart_5316789 baseEnd_5316789 := by
    simpa [prefixWord, tailWord_5316789, baseEnd_5316789] using wordTrace_append hprefix tailTrace_5316789
  have hstable : (prefixWord ++ tailWord_5316789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316789).length < 2 ^ (prefixWord ++ tailWord_5316789).sum := by decide
  have hdescent : baseEnd_5316789 < baseStart_5316789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316802 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_5316802 : Nat := 118140960795 + 5316802 * 2 ^ 59
def prefixEnd_5316802 : Nat := 4983230072969 + 3 ^ 40 * 5316802 * 2
def baseEnd_5316802 : Nat := 303341663420690246824831

theorem tailTrace_5316802 : CollatzResearch.WordTrace tailWord_5316802 prefixEnd_5316802 303341663420690246824831 := by
  unfold tailWord_5316802
  simp only [CollatzResearch.WordTrace]
  refine ⟨48479925021035466583538165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129279800056094577556101773 48479925021035466583538165)
  ·
    refine ⟨4544992970722074992206703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48479925021035466583538165 4544992970722074992206703)
    ·
      refine ⟨6817489456083112488310055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4544992970722074992206703 6817489456083112488310055)
      ·
        refine ⟨10226234184124668732465083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817489456083112488310055 10226234184124668732465083)
        ·
          refine ⟨15339351276187003098697625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226234184124668732465083 15339351276187003098697625)
          ·
            refine ⟨11504513457140252324023219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15339351276187003098697625 11504513457140252324023219)
            ·
              refine ⟨17256770185710378486034829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504513457140252324023219 17256770185710378486034829)
              ·
                refine ⟨6471288819641391932263061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17256770185710378486034829 6471288819641391932263061)
                ·
                  refine ⟨303341663420690246824831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6471288819641391932263061 303341663420690246824831)
                  ·
                    rfl

theorem cell23_5316802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_5316802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316802 prefixEnd_5316802 := by exact prefixLift 5316802
  have htrace : WordTrace (prefixWord ++ tailWord_5316802) baseStart_5316802 baseEnd_5316802 := by
    simpa [prefixWord, tailWord_5316802, baseEnd_5316802] using wordTrace_append hprefix tailTrace_5316802
  have hstable : (prefixWord ++ tailWord_5316802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316802).length < 2 ^ (prefixWord ++ tailWord_5316802).sum := by decide
  have hdescent : baseEnd_5316802 < baseStart_5316802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316811 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 1, 6]
def baseStart_5316811 : Nat := 118140960795 + 5316811 * 2 ^ 59
def prefixEnd_5316811 : Nat := 4983230072969 + 3 ^ 40 * 5316811 * 2
def baseEnd_5316811 : Nat := 910026530704034228736979

theorem tailTrace_5316811 : CollatzResearch.WordTrace tailWord_5316811 prefixEnd_5316811 910026530704034228736979 := by
  unfold tailWord_5316811
  simp only [CollatzResearch.WordTrace]
  refine ⟨193920028341109260871230287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129280018894072840580820191 193920028341109260871230287)
  ·
    refine ⟨290880042511663891306845431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193920028341109260871230287 290880042511663891306845431)
    ·
      refine ⟨436320063767495836960268147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290880042511663891306845431 436320063767495836960268147)
      ·
        refine ⟨654480095651243755440402221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436320063767495836960268147 654480095651243755440402221)
        ·
          refine ⟨245430035869216408290150833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 654480095651243755440402221 245430035869216408290150833)
          ·
            refine ⟨184072526901912306217613125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245430035869216408290150833 184072526901912306217613125)
            ·
              refine ⟨34513598794108557415802461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184072526901912306217613125 34513598794108557415802461)
              ·
                refine ⟨12942599547790709030925923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34513598794108557415802461 12942599547790709030925923)
                ·
                  refine ⟨19413899321686063546388885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12942599547790709030925923 19413899321686063546388885)
                  ·
                    refine ⟨910026530704034228736979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19413899321686063546388885 910026530704034228736979)
                    ·
                      rfl

theorem cell23_5316811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 6].length) (baseStart_5316811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316811 prefixEnd_5316811 := by exact prefixLift 5316811
  have htrace : WordTrace (prefixWord ++ tailWord_5316811) baseStart_5316811 baseEnd_5316811 := by
    simpa [prefixWord, tailWord_5316811, baseEnd_5316811] using wordTrace_append hprefix tailTrace_5316811
  have hstable : (prefixWord ++ tailWord_5316811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316811).length < 2 ^ (prefixWord ++ tailWord_5316811).sum := by decide
  have hdescent : baseEnd_5316811 < baseStart_5316811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316858 : List Nat := [3, 1, 1, 1, 1, 7, 1, 8]
def baseStart_5316858 : Nat := 118140960795 + 5316858 * 2 ^ 59
def prefixEnd_5316858 : Nat := 4983230072969 + 3 ^ 40 * 5316858 * 2
def baseEnd_5316858 : Nat := 101114952803809777863823

theorem tailTrace_5316858 : CollatzResearch.WordTrace tailWord_5316858 prefixEnd_5316858 101114952803809777863823 := by
  unfold tailWord_5316858
  simp only [CollatzResearch.WordTrace]
  refine ⟨48480435642984746974547807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129281161714625991932127485 48480435642984746974547807)
  ·
    refine ⟨72720653464477120461821711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48480435642984746974547807 72720653464477120461821711)
    ·
      refine ⟨109080980196715680692732567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72720653464477120461821711 109080980196715680692732567)
      ·
        refine ⟨163621470295073521039098851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109080980196715680692732567 163621470295073521039098851)
        ·
          refine ⟨245432205442610281558648277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163621470295073521039098851 245432205442610281558648277)
          ·
            refine ⟨5752317315061178474030819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 245432205442610281558648277 5752317315061178474030819)
            ·
              refine ⟨8628475972591767711046229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752317315061178474030819 8628475972591767711046229)
              ·
                refine ⟨101114952803809777863823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8628475972591767711046229 101114952803809777863823)
                ·
                  rfl

theorem cell23_5316858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_5316858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316858 prefixEnd_5316858 := by exact prefixLift 5316858
  have htrace : WordTrace (prefixWord ++ tailWord_5316858) baseStart_5316858 baseEnd_5316858 := by
    simpa [prefixWord, tailWord_5316858, baseEnd_5316858] using wordTrace_append hprefix tailTrace_5316858
  have hstable : (prefixWord ++ tailWord_5316858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316858).length < 2 ^ (prefixWord ++ tailWord_5316858).sum := by decide
  have hdescent : baseEnd_5316858 < baseStart_5316858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316861 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_5316861 : Nat := 118140960795 + 5316861 * 2 ^ 59
def prefixEnd_5316861 : Nat := 4983230072969 + 3 ^ 40 * 5316861 * 2
def baseEnd_5316861 : Nat := 2730105266144827490585707

theorem tailTrace_5316861 : CollatzResearch.WordTrace tailWord_5316861 prefixEnd_5316861 2730105266144827490585707 := by
  unfold tailWord_5316861
  simp only [CollatzResearch.WordTrace]
  refine ⟨193921851990928119410550437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129281234660618746273700291 193921851990928119410550437)
  ·
    refine ⟨36360347248299022389478207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193921851990928119410550437 36360347248299022389478207)
    ·
      refine ⟨54540520872448533584217311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36360347248299022389478207 54540520872448533584217311)
      ·
        refine ⟨81810781308672800376325967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54540520872448533584217311 81810781308672800376325967)
        ·
          refine ⟨122716171963009200564488951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81810781308672800376325967 122716171963009200564488951)
          ·
            refine ⟨184074257944513800846733427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122716171963009200564488951 184074257944513800846733427)
            ·
              refine ⟨276111386916770701270100141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184074257944513800846733427 276111386916770701270100141)
              ·
                refine ⟨103541770093789012976287553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276111386916770701270100141 103541770093789012976287553)
                ·
                  refine ⟨77656327570341759732215665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103541770093789012976287553 77656327570341759732215665)
                  ·
                    refine ⟨58242245677756319799161749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77656327570341759732215665 58242245677756319799161749)
                    ·
                      refine ⟨2730105266144827490585707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58242245677756319799161749 2730105266144827490585707)
                      ·
                        rfl

theorem cell23_5316861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_5316861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316861 prefixEnd_5316861 := by exact prefixLift 5316861
  have htrace : WordTrace (prefixWord ++ tailWord_5316861) baseStart_5316861 baseEnd_5316861 := by
    simpa [prefixWord, tailWord_5316861, baseEnd_5316861] using wordTrace_append hprefix tailTrace_5316861
  have hstable : (prefixWord ++ tailWord_5316861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316861).length < 2 ^ (prefixWord ++ tailWord_5316861).sum := by decide
  have hdescent : baseEnd_5316861 < baseStart_5316861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316903 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5316903 : Nat := 118140960795 + 5316903 * 2 ^ 59
def prefixEnd_5316903 : Nat := 4983230072969 + 3 ^ 40 * 5316903 * 2
def baseEnd_5316903 : Nat := 2730126832332316326260515

theorem tailTrace_5316903 : CollatzResearch.WordTrace tailWord_5316903 prefixEnd_5316903 2730126832332316326260515 := by
  unfold tailWord_5316903
  simp only [CollatzResearch.WordTrace]
  refine ⟨193923383856775960583579363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129282255904517307055719575 193923383856775960583579363)
  ·
    refine ⟨290885075785163940875369045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193923383856775960583579363 290885075785163940875369045)
    ·
      refine ⟨3408809481857389932133231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 290885075785163940875369045 3408809481857389932133231)
      ·
        refine ⟨5113214222786084898199847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408809481857389932133231 5113214222786084898199847)
        ·
          refine ⟨7669821334179127347299771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113214222786084898199847 7669821334179127347299771)
          ·
            refine ⟨11504732001268691020949657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669821334179127347299771 11504732001268691020949657)
            ·
              refine ⟨8628549000951518265712243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11504732001268691020949657 8628549000951518265712243)
              ·
                refine ⟨12942823501427277398568365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8628549000951518265712243 12942823501427277398568365)
                ·
                  refine ⟨4853558813035229024463137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12942823501427277398568365 4853558813035229024463137)
                  ·
                    refine ⟨3640169109776421768347353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4853558813035229024463137 3640169109776421768347353)
                    ·
                      refine ⟨2730126832332316326260515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640169109776421768347353 2730126832332316326260515)
                      ·
                        rfl

theorem cell23_5316903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5316903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316903 prefixEnd_5316903 := by exact prefixLift 5316903
  have htrace : WordTrace (prefixWord ++ tailWord_5316903) baseStart_5316903 baseEnd_5316903 := by
    simpa [prefixWord, tailWord_5316903, baseEnd_5316903] using wordTrace_append hprefix tailTrace_5316903
  have hstable : (prefixWord ++ tailWord_5316903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316903).length < 2 ^ (prefixWord ++ tailWord_5316903).sum := by decide
  have hdescent : baseEnd_5316903 < baseStart_5316903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316965 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 7]
def baseStart_5316965 : Nat := 118140960795 + 5316965 * 2 ^ 59
def prefixEnd_5316965 : Nat := 4983230072969 + 3 ^ 40 * 5316965 * 2
def baseEnd_5316965 : Nat := 303350963125877231520581

theorem tailTrace_5316965 : CollatzResearch.WordTrace tailWord_5316965 prefixEnd_5316965 303350963125877231520581 := by
  unfold tailWord_5316965
  simp only [CollatzResearch.WordTrace]
  refine ⟨193925645182551345172336349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129283763455034230114890899 193925645182551345172336349)
  ·
    refine ⟨72722116943456754439626131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193925645182551345172336349 72722116943456754439626131)
    ·
      refine ⟨109083175415185131659439197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72722116943456754439626131 109083175415185131659439197)
      ·
        refine ⟨40906190780694424372289699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109083175415185131659439197 40906190780694424372289699)
        ·
          refine ⟨61359286171041636558434549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40906190780694424372289699 61359286171041636558434549)
          ·
            refine ⟨5752433078535153427353239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61359286171041636558434549 5752433078535153427353239)
            ·
              refine ⟨8628649617802730141029859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752433078535153427353239 8628649617802730141029859)
              ·
                refine ⟨12942974426704095211544789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8628649617802730141029859 12942974426704095211544789)
                ·
                  refine ⟨303350963125877231520581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12942974426704095211544789 303350963125877231520581)
                  ·
                    rfl

theorem cell23_5316965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_5316965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316965 prefixEnd_5316965 := by exact prefixLift 5316965
  have htrace : WordTrace (prefixWord ++ tailWord_5316965) baseStart_5316965 baseEnd_5316965 := by
    simpa [prefixWord, tailWord_5316965, baseEnd_5316965] using wordTrace_append hprefix tailTrace_5316965
  have hstable : (prefixWord ++ tailWord_5316965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316965).length < 2 ^ (prefixWord ++ tailWord_5316965).sum := by decide
  have hdescent : baseEnd_5316965 < baseStart_5316965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5316976 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 2, 2, 2]
def baseStart_5316976 : Nat := 118140960795 + 5316976 * 2 ^ 59
def prefixEnd_5316976 : Nat := 4983230072969 + 3 ^ 40 * 5316976 * 2
def baseEnd_5316976 : Nat := 2730164316420094540647679

theorem tailTrace_5316976 : CollatzResearch.WordTrace tailWord_5316976 prefixEnd_5316976 2730164316420094540647679 := by
  unfold tailWord_5316976
  simp only [CollatzResearch.WordTrace]
  refine ⟨96963023192755747025493391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129284030923674329367324521 96963023192755747025493391)
  ·
    refine ⟨145444534789133620538240087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96963023192755747025493391 145444534789133620538240087)
    ·
      refine ⟨218166802183700430807360131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145444534789133620538240087 218166802183700430807360131)
      ·
        refine ⟨327250203275550646211040197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218166802183700430807360131 327250203275550646211040197)
        ·
          refine ⟨61359413114165746164570037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327250203275550646211040197 61359413114165746164570037)
          ·
            refine ⟨5752444979453038702928441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61359413114165746164570037 5752444979453038702928441)
            ·
              refine ⟨4314333734589779027196331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5752444979453038702928441 4314333734589779027196331)
              ·
                refine ⟨6471500601884668540794497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4314333734589779027196331 6471500601884668540794497)
                ·
                  refine ⟨4853625451413501405595873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6471500601884668540794497 4853625451413501405595873)
                  ·
                    refine ⟨3640219088560126054196905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4853625451413501405595873 3640219088560126054196905)
                    ·
                      refine ⟨2730164316420094540647679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640219088560126054196905 2730164316420094540647679)
                      ·
                        rfl

theorem cell23_5316976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 2, 2].length) (baseStart_5316976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5316976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5316976 prefixEnd_5316976 := by exact prefixLift 5316976
  have htrace : WordTrace (prefixWord ++ tailWord_5316976) baseStart_5316976 baseEnd_5316976 := by
    simpa [prefixWord, tailWord_5316976, baseEnd_5316976] using wordTrace_append hprefix tailTrace_5316976
  have hstable : (prefixWord ++ tailWord_5316976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5316976).length < 2 ^ (prefixWord ++ tailWord_5316976).sum := by decide
  have hdescent : baseEnd_5316976 < baseStart_5316976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5316976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317015 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5317015 : Nat := 118140960795 + 5317015 * 2 ^ 59
def prefixEnd_5317015 : Nat := 4983230072969 + 3 ^ 40 * 5317015 * 2
def baseEnd_5317015 : Nat := 2730184342165619888059999

theorem tailTrace_5317015 : CollatzResearch.WordTrace tailWord_5317015 prefixEnd_5317015 2730184342165619888059999 := by
  unfold tailWord_5317015
  simp only [CollatzResearch.WordTrace]
  refine ⟨193927468832370203711656499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129284979221580135807770999 193927468832370203711656499)
  ·
    refine ⟨290891203248555305567484749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193927468832370203711656499 290891203248555305567484749)
    ·
      refine ⟨109084201218208239587806781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290891203248555305567484749 109084201218208239587806781)
      ·
        refine ⟨40906575456828089845427543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109084201218208239587806781 40906575456828089845427543)
        ·
          refine ⟨61359863185242134768141315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40906575456828089845427543 61359863185242134768141315)
          ·
            refine ⟨92039794777863202152211973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61359863185242134768141315 92039794777863202152211973)
            ·
              refine ⟨17257461520849350403539745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92039794777863202152211973 17257461520849350403539745)
              ·
                refine ⟨12943096140637012802654809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17257461520849350403539745 12943096140637012802654809)
                ·
                  refine ⟨9707322105477759601991107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12943096140637012802654809 9707322105477759601991107)
                  ·
                    refine ⟨14560983158216639402986661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9707322105477759601991107 14560983158216639402986661)
                    ·
                      refine ⟨2730184342165619888059999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14560983158216639402986661 2730184342165619888059999)
                      ·
                        rfl

theorem cell23_5317015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5317015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317015 prefixEnd_5317015 := by exact prefixLift 5317015
  have htrace : WordTrace (prefixWord ++ tailWord_5317015) baseStart_5317015 baseEnd_5317015 := by
    simpa [prefixWord, tailWord_5317015, baseEnd_5317015] using wordTrace_append hprefix tailTrace_5317015
  have hstable : (prefixWord ++ tailWord_5317015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317015).length < 2 ^ (prefixWord ++ tailWord_5317015).sum := by decide
  have hdescent : baseEnd_5317015 < baseStart_5317015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317022 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5317022 : Nat := 118140960795 + 5317022 * 2 ^ 59
def prefixEnd_5317022 : Nat := 4983230072969 + 3 ^ 40 * 5317022 * 2
def baseEnd_5317022 : Nat := 2730187936530201360672467

theorem tailTrace_5317022 : CollatzResearch.WordTrace tailWord_5317022 prefixEnd_5317022 2730187936530201360672467 := by
  unfold tailWord_5317022
  simp only [CollatzResearch.WordTrace]
  refine ⟨24240965517918105488395165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129285149428896562604774213 24240965517918105488395165)
  ·
    refine ⟨9090362069219289558148187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24240965517918105488395165 9090362069219289558148187)
    ·
      refine ⟨13635543103828934337222281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9090362069219289558148187 13635543103828934337222281)
      ·
        refine ⟨10226657327871700752916711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13635543103828934337222281 10226657327871700752916711)
        ·
          refine ⟨15339985991807551129375067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226657327871700752916711 15339985991807551129375067)
          ·
            refine ⟨23009978987711326694062601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15339985991807551129375067 23009978987711326694062601)
            ·
              refine ⟨17257484240783495020546951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23009978987711326694062601 17257484240783495020546951)
              ·
                refine ⟨25886226361175242530820427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17257484240783495020546951 25886226361175242530820427)
                ·
                  refine ⟨38829339541762863796230641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25886226361175242530820427 38829339541762863796230641)
                  ·
                    refine ⟨29122004656322147847172981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38829339541762863796230641 29122004656322147847172981)
                    ·
                      refine ⟨2730187936530201360672467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29122004656322147847172981 2730187936530201360672467)
                      ·
                        rfl

theorem cell23_5317022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5317022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317022 prefixEnd_5317022 := by exact prefixLift 5317022
  have htrace : WordTrace (prefixWord ++ tailWord_5317022) baseStart_5317022 baseEnd_5317022 := by
    simpa [prefixWord, tailWord_5317022, baseEnd_5317022] using wordTrace_append hprefix tailTrace_5317022
  have hstable : (prefixWord ++ tailWord_5317022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317022).length < 2 ^ (prefixWord ++ tailWord_5317022).sum := by decide
  have hdescent : baseEnd_5317022 < baseStart_5317022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317052 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5317052 : Nat := 118140960795 + 5317052 * 2 ^ 59
def prefixEnd_5317052 : Nat := 4983230072969 + 3 ^ 40 * 5317052 * 2
def baseEnd_5317052 : Nat := 2730203340949836243297329

theorem tailTrace_5317052 : CollatzResearch.WordTrace tailWord_5317052 prefixEnd_5317052 2730203340949836243297329 := by
  unfold tailWord_5317052
  simp only [CollatzResearch.WordTrace]
  refine ⟨96964409166618079515376705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129285878888824106020502273 96964409166618079515376705)
  ·
    refine ⟨72723306874963559636532529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96964409166618079515376705 72723306874963559636532529)
    ·
      refine ⟨54542480156222669727399397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72723306874963559636532529 54542480156222669727399397)
      ·
        refine ⟨10226715029291750573887387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54542480156222669727399397 10226715029291750573887387)
        ·
          refine ⟨15340072543937625860831081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226715029291750573887387 15340072543937625860831081)
          ·
            refine ⟨11505054407953219395623311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15340072543937625860831081 11505054407953219395623311)
            ·
              refine ⟨17257581611929829093434967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505054407953219395623311 17257581611929829093434967)
              ·
                refine ⟨25886372417894743640152451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17257581611929829093434967 25886372417894743640152451)
                ·
                  refine ⟨38829558626842115460228677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25886372417894743640152451 38829558626842115460228677)
                  ·
                    refine ⟨7280542242532896648792877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38829558626842115460228677 7280542242532896648792877)
                    ·
                      refine ⟨2730203340949836243297329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7280542242532896648792877 2730203340949836243297329)
                      ·
                        rfl

theorem cell23_5317052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5317052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317052 prefixEnd_5317052 := by exact prefixLift 5317052
  have htrace : WordTrace (prefixWord ++ tailWord_5317052) baseStart_5317052 baseEnd_5317052 := by
    simpa [prefixWord, tailWord_5317052, baseEnd_5317052] using wordTrace_append hprefix tailTrace_5317052
  have hstable : (prefixWord ++ tailWord_5317052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317052).length < 2 ^ (prefixWord ++ tailWord_5317052).sum := by decide
  have hdescent : baseEnd_5317052 < baseStart_5317052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317102 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_5317102 : Nat := 118140960795 + 5317102 * 2 ^ 59
def prefixEnd_5317102 : Nat := 4983230072969 + 3 ^ 40 * 5317102 * 2
def baseEnd_5317102 : Nat := 910076338327520349224033

theorem tailTrace_5317102 : CollatzResearch.WordTrace tailWord_5317102 prefixEnd_5317102 910076338327520349224033 := by
  unfold tailWord_5317102
  simp only [CollatzResearch.WordTrace]
  refine ⟨24241330247881877196259195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129287094655370011713382373 24241330247881877196259195)
  ·
    refine ⟨36361995371822815794388793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24241330247881877196259195 36361995371822815794388793)
    ·
      refine ⟨27271496528867111845791595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36361995371822815794388793 27271496528867111845791595)
      ·
        refine ⟨40907244793300667768687393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27271496528867111845791595 40907244793300667768687393)
        ·
          refine ⟨30680433594975500826515545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40907244793300667768687393 30680433594975500826515545)
          ·
            refine ⟨23010325196231625619886659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30680433594975500826515545 23010325196231625619886659)
            ·
              refine ⟨34515487794347438429829989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23010325196231625619886659 34515487794347438429829989)
              ·
                refine ⟨6471653961440144705593123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34515487794347438429829989 6471653961440144705593123)
                ·
                  refine ⟨9707480942160217058389685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6471653961440144705593123 9707480942160217058389685)
                  ·
                    refine ⟨910076338327520349224033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9707480942160217058389685 910076338327520349224033)
                    ·
                      rfl

theorem cell23_5317102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_5317102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317102 prefixEnd_5317102 := by exact prefixLift 5317102
  have htrace : WordTrace (prefixWord ++ tailWord_5317102) baseStart_5317102 baseEnd_5317102 := by
    simpa [prefixWord, tailWord_5317102, baseEnd_5317102] using wordTrace_append hprefix tailTrace_5317102
  have hstable : (prefixWord ++ tailWord_5317102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317102).length < 2 ^ (prefixWord ++ tailWord_5317102).sum := by decide
  have hdescent : baseEnd_5317102 < baseStart_5317102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317125 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_5317125 : Nat := 118140960795 + 5317125 * 2 ^ 59
def prefixEnd_5317125 : Nat := 4983230072969 + 3 ^ 40 * 5317125 * 2
def baseEnd_5317125 : Nat := 2730240825037614457684493

theorem tailTrace_5317125 : CollatzResearch.WordTrace tailWord_5317125 prefixEnd_5317125 2730240825037614457684493 := by
  unfold tailWord_5317125
  simp only [CollatzResearch.WordTrace]
  refine ⟨193931480861971692498160829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129287653907981128332107219 193931480861971692498160829)
  ·
    refine ⟨72724305323239384686810311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193931480861971692498160829 72724305323239384686810311)
    ·
      refine ⟨109086457984859077030215467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72724305323239384686810311 109086457984859077030215467)
      ·
        refine ⟨163629686977288615545323201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109086457984859077030215467 163629686977288615545323201)
        ·
          refine ⟨122722265232966461658992401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163629686977288615545323201 122722265232966461658992401)
          ·
            refine ⟨92041698924724846244244301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122722265232966461658992401 92041698924724846244244301)
            ·
              refine ⟨34515637096771817341591613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92041698924724846244244301 34515637096771817341591613)
              ·
                refine ⟨12943363911289431503096855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34515637096771817341591613 12943363911289431503096855)
                ·
                  refine ⟨19415045866934147254645283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12943363911289431503096855 19415045866934147254645283)
                  ·
                    refine ⟨29122568800401220881967925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19415045866934147254645283 29122568800401220881967925)
                    ·
                      refine ⟨2730240825037614457684493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29122568800401220881967925 2730240825037614457684493)
                      ·
                        rfl

theorem cell23_5317125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_5317125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317125 prefixEnd_5317125 := by exact prefixLift 5317125
  have htrace : WordTrace (prefixWord ++ tailWord_5317125) baseStart_5317125 baseEnd_5317125 := by
    simpa [prefixWord, tailWord_5317125, baseEnd_5317125] using wordTrace_append hprefix tailTrace_5317125
  have hstable : (prefixWord ++ tailWord_5317125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317125).length < 2 ^ (prefixWord ++ tailWord_5317125).sum := by decide
  have hdescent : baseEnd_5317125 < baseStart_5317125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317132 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_5317132 : Nat := 118140960795 + 5317132 * 2 ^ 59
def prefixEnd_5317132 : Nat := 4983230072969 + 3 ^ 40 * 5317132 * 2
def baseEnd_5317132 : Nat := 910081473134065310098987

theorem tailTrace_5317132 : CollatzResearch.WordTrace tailWord_5317132 prefixEnd_5317132 910081473134065310098987 := by
  unfold tailWord_5317132
  simp only [CollatzResearch.WordTrace]
  refine ⟨96965868086473166346832825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129287824115297555129110433 96965868086473166346832825)
  ·
    refine ⟨72724401064854874760124619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96965868086473166346832825 72724401064854874760124619)
    ·
      refine ⟨109086601597282312140186929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72724401064854874760124619 109086601597282312140186929)
      ·
        refine ⟨81814951197961734105140197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109086601597282312140186929 81814951197961734105140197)
        ·
          refine ⟨15340303349617825144713787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81814951197961734105140197 15340303349617825144713787)
          ·
            refine ⟨23010455024426737717070681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15340303349617825144713787 23010455024426737717070681)
            ·
              refine ⟨17257841268320053287803011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23010455024426737717070681 17257841268320053287803011)
              ·
                refine ⟨25886761902480079931704517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17257841268320053287803011 25886761902480079931704517)
                ·
                  refine ⟨4853767856715014987194597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25886761902480079931704517 4853767856715014987194597)
                  ·
                    refine ⟨910081473134065310098987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4853767856715014987194597 910081473134065310098987)
                    ·
                      rfl

theorem cell23_5317132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_5317132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317132 prefixEnd_5317132 := by exact prefixLift 5317132
  have htrace : WordTrace (prefixWord ++ tailWord_5317132) baseStart_5317132 baseEnd_5317132 := by
    simpa [prefixWord, tailWord_5317132, baseEnd_5317132] using wordTrace_append hprefix tailTrace_5317132
  have hstable : (prefixWord ++ tailWord_5317132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317132).length < 2 ^ (prefixWord ++ tailWord_5317132).sum := by decide
  have hdescent : baseEnd_5317132 < baseStart_5317132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317133 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5317133 : Nat := 118140960795 + 5317133 * 2 ^ 59
def prefixEnd_5317133 : Nat := 4983230072969 + 3 ^ 40 * 5317133 * 2
def baseEnd_5317133 : Nat := 2730244932882850426384457

theorem tailTrace_5317133 : CollatzResearch.WordTrace tailWord_5317133 prefixEnd_5317133 2730244932882850426384457 := by
  unfold tailWord_5317133
  simp only [CollatzResearch.WordTrace]
  refine ⟨193931772645942709864452053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129287848430628473242968035 193931772645942709864452053)
  ·
    refine ⟨4545275921389282262448095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 193931772645942709864452053 4545275921389282262448095)
    ·
      refine ⟨6817913882083923393672143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4545275921389282262448095 6817913882083923393672143)
      ·
        refine ⟨10226870823125885090508215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817913882083923393672143 10226870823125885090508215)
        ·
          refine ⟨15340306234688827635762323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226870823125885090508215 15340306234688827635762323)
          ·
            refine ⟨23010459352033241453643485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15340306234688827635762323 23010459352033241453643485)
            ·
              refine ⟨8628922257012465545116307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23010459352033241453643485 8628922257012465545116307)
              ·
                refine ⟨12943383385518698317674461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8628922257012465545116307 12943383385518698317674461)
                ·
                  refine ⟨4853768769569511869127923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12943383385518698317674461 4853768769569511869127923)
                  ·
                    refine ⟨7280653154354267803691885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4853768769569511869127923 7280653154354267803691885)
                    ·
                      refine ⟨2730244932882850426384457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7280653154354267803691885 2730244932882850426384457)
                      ·
                        rfl

theorem cell23_5317133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5317133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317133 prefixEnd_5317133 := by exact prefixLift 5317133
  have htrace : WordTrace (prefixWord ++ tailWord_5317133) baseStart_5317133 baseEnd_5317133 := by
    simpa [prefixWord, tailWord_5317133, baseEnd_5317133] using wordTrace_append hprefix tailTrace_5317133
  have hstable : (prefixWord ++ tailWord_5317133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317133).length < 2 ^ (prefixWord ++ tailWord_5317133).sum := by decide
  have hdescent : baseEnd_5317133 < baseStart_5317133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317149 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_5317149 : Nat := 118140960795 + 5317149 * 2 ^ 59
def prefixEnd_5317149 : Nat := 4983230072969 + 3 ^ 40 * 5317149 * 2
def baseEnd_5317149 : Nat := 910084382857774121261461

theorem tailTrace_5317149 : CollatzResearch.WordTrace tailWord_5317149 prefixEnd_5317149 910084382857774121261461 := by
  unfold tailWord_5317149
  simp only [CollatzResearch.WordTrace]
  refine ⟨193932356213884744597034501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129288237475923163064689667 193932356213884744597034501)
  ·
    refine ⟨36362316790103389611943969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193932356213884744597034501 36362316790103389611943969)
    ·
      refine ⟨27271737592577542208957977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36362316790103389611943969 27271737592577542208957977)
      ·
        refine ⟨20453803194433156656718483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27271737592577542208957977 20453803194433156656718483)
        ·
          refine ⟨30680704791649734985077725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20453803194433156656718483 30680704791649734985077725)
          ·
            refine ⟨11505264296868650619404147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30680704791649734985077725 11505264296868650619404147)
            ·
              refine ⟨17257896445302975929106221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505264296868650619404147 17257896445302975929106221)
              ·
                refine ⟨6471711166988615973414833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17257896445302975929106221 6471711166988615973414833)
                ·
                  refine ⟨4853783375241461980061125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6471711166988615973414833 4853783375241461980061125)
                  ·
                    refine ⟨910084382857774121261461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4853783375241461980061125 910084382857774121261461)
                    ·
                      rfl

theorem cell23_5317149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_5317149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317149 prefixEnd_5317149 := by exact prefixLift 5317149
  have htrace : WordTrace (prefixWord ++ tailWord_5317149) baseStart_5317149 baseEnd_5317149 := by
    simpa [prefixWord, tailWord_5317149, baseEnd_5317149] using wordTrace_append hprefix tailTrace_5317149
  have hstable : (prefixWord ++ tailWord_5317149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317149).length < 2 ^ (prefixWord ++ tailWord_5317149).sum := by decide
  have hdescent : baseEnd_5317149 < baseStart_5317149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317189 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_5317189 : Nat := 118140960795 + 5317189 * 2 ^ 59
def prefixEnd_5317189 : Nat := 4983230072969 + 3 ^ 40 * 5317189 * 2
def baseEnd_5317189 : Nat := 2730273687799502207284199

theorem tailTrace_5317189 : CollatzResearch.WordTrace tailWord_5317189 prefixEnd_5317189 2730273687799502207284199 := by
  unfold tailWord_5317189
  simp only [CollatzResearch.WordTrace]
  refine ⟨193933815133739831428490621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129289210089159887618993747 193933815133739831428490621)
  ·
    refine ⟨72725180675152436785683983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193933815133739831428490621 72725180675152436785683983)
    ·
      refine ⟨109087771012728655178525975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72725180675152436785683983 109087771012728655178525975)
      ·
        refine ⟨163631656519092982767788963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109087771012728655178525975 163631656519092982767788963)
        ·
          refine ⟨245447484778639474151683445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163631656519092982767788963 245447484778639474151683445)
          ·
            refine ⟨23010701697997450701720323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245447484778639474151683445 23010701697997450701720323)
            ·
              refine ⟨34516052546996176052580485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23010701697997450701720323 34516052546996176052580485)
              ·
                refine ⟨6471759852561783009858841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34516052546996176052580485 6471759852561783009858841)
                ·
                  refine ⟨4853819889421337257394131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6471759852561783009858841 4853819889421337257394131)
                  ·
                    refine ⟨7280729834132005886091197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4853819889421337257394131 7280729834132005886091197)
                    ·
                      refine ⟨2730273687799502207284199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7280729834132005886091197 2730273687799502207284199)
                      ·
                        rfl

theorem cell23_5317189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_5317189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317189 prefixEnd_5317189 := by exact prefixLift 5317189
  have htrace : WordTrace (prefixWord ++ tailWord_5317189) baseStart_5317189 baseEnd_5317189 := by
    simpa [prefixWord, tailWord_5317189, baseEnd_5317189] using wordTrace_append hprefix tailTrace_5317189
  have hstable : (prefixWord ++ tailWord_5317189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317189).length < 2 ^ (prefixWord ++ tailWord_5317189).sum := by decide
  have hdescent : baseEnd_5317189 < baseStart_5317189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317195 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4]
def baseStart_5317195 : Nat := 118140960795 + 5317195 * 2 ^ 59
def prefixEnd_5317195 : Nat := 4983230072969 + 3 ^ 40 * 5317195 * 2
def baseEnd_5317195 : Nat := 2730276768683429183809171

theorem tailTrace_5317195 : CollatzResearch.WordTrace tailWord_5317195 prefixEnd_5317195 2730276768683429183809171 := by
  unfold tailWord_5317195
  simp only [CollatzResearch.WordTrace]
  refine ⟨193934033971718094453209039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129289355981145396302139359 193934033971718094453209039)
  ·
    refine ⟨290901050957577141679813559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193934033971718094453209039 290901050957577141679813559)
    ·
      refine ⟨436351576436365712519720339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290901050957577141679813559 436351576436365712519720339)
      ·
        refine ⟨654527364654548568779580509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436351576436365712519720339 654527364654548568779580509)
        ·
          refine ⟨245447761745455713292342691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 654527364654548568779580509 245447761745455713292342691)
          ·
            refine ⟨368171642618183569938514037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245447761745455713292342691 368171642618183569938514037)
            ·
              refine ⟨34516091495454709681735691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 368171642618183569938514037 34516091495454709681735691)
              ·
                refine ⟨51774137243182064522603537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34516091495454709681735691 51774137243182064522603537)
                ·
                  refine ⟨38830602932386548391952653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51774137243182064522603537 38830602932386548391952653)
                  ·
                    refine ⟨14561476099644955646982245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38830602932386548391952653 14561476099644955646982245)
                    ·
                      refine ⟨2730276768683429183809171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14561476099644955646982245 2730276768683429183809171)
                      ·
                        rfl

theorem cell23_5317195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_5317195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317195 prefixEnd_5317195 := by exact prefixLift 5317195
  have htrace : WordTrace (prefixWord ++ tailWord_5317195) baseStart_5317195 baseEnd_5317195 := by
    simpa [prefixWord, tailWord_5317195, baseEnd_5317195] using wordTrace_append hprefix tailTrace_5317195
  have hstable : (prefixWord ++ tailWord_5317195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317195).length < 2 ^ (prefixWord ++ tailWord_5317195).sum := by decide
  have hdescent : baseEnd_5317195 < baseStart_5317195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317205 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_5317205 : Nat := 118140960795 + 5317205 * 2 ^ 59
def prefixEnd_5317205 : Nat := 4983230072969 + 3 ^ 40 * 5317205 * 2
def baseEnd_5317205 : Nat := 910093967829991381561375

theorem tailTrace_5317205 : CollatzResearch.WordTrace tailWord_5317205 prefixEnd_5317205 910093967829991381561375 := by
  unfold tailWord_5317205
  simp only [CollatzResearch.WordTrace]
  refine ⟨193934398701681866161073069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129289599134454577440715379 193934398701681866161073069)
  ·
    refine ⟨72725399513130699810402401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193934398701681866161073069 72725399513130699810402401)
    ·
      refine ⟨54544049634848024857801801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72725399513130699810402401 54544049634848024857801801)
      ·
        refine ⟨40908037226136018643351351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54544049634848024857801801 40908037226136018643351351)
        ·
          refine ⟨61362055839204027965027027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40908037226136018643351351 61362055839204027965027027)
          ·
            refine ⟨92043083758806041947540541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61362055839204027965027027 92043083758806041947540541)
            ·
              refine ⟨34516156409552265730327703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92043083758806041947540541 34516156409552265730327703)
              ·
                refine ⟨51774234614328398595491555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34516156409552265730327703 51774234614328398595491555)
                ·
                  refine ⟨77661351921492597893237333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51774234614328398595491555 77661351921492597893237333)
                  ·
                    refine ⟨910093967829991381561375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77661351921492597893237333 910093967829991381561375)
                    ·
                      rfl

theorem cell23_5317205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_5317205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317205 prefixEnd_5317205 := by exact prefixLift 5317205
  have htrace : WordTrace (prefixWord ++ tailWord_5317205) baseStart_5317205 baseEnd_5317205 := by
    simpa [prefixWord, tailWord_5317205, baseEnd_5317205] using wordTrace_append hprefix tailTrace_5317205
  have hstable : (prefixWord ++ tailWord_5317205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317205).length < 2 ^ (prefixWord ++ tailWord_5317205).sum := by decide
  have hdescent : baseEnd_5317205 < baseStart_5317205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317215 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_5317215 : Nat := 118140960795 + 5317215 * 2 ^ 59
def prefixEnd_5317215 : Nat := 4983230072969 + 3 ^ 40 * 5317215 * 2
def baseEnd_5317215 : Nat := 2730287038296519105559079

theorem tailTrace_5317215 : CollatzResearch.WordTrace tailWord_5317215 prefixEnd_5317215 2730287038296519105559079 := by
  unfold tailWord_5317215
  simp only [CollatzResearch.WordTrace]
  refine ⟨193934763431645637868937099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129289842287763758579291399 193934763431645637868937099)
  ·
    refine ⟨290902145147468456803405649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193934763431645637868937099 290902145147468456803405649)
    ·
      refine ⟨218176608860601342602554237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290902145147468456803405649 218176608860601342602554237)
      ·
        refine ⟨81816228322725503475957839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218176608860601342602554237 81816228322725503475957839)
        ·
          refine ⟨122724342484088255213936759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81816228322725503475957839 122724342484088255213936759)
          ·
            refine ⟨184086513726132382820905139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122724342484088255213936759 184086513726132382820905139)
            ·
              refine ⟨276129770589198574231357709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184086513726132382820905139 276129770589198574231357709)
              ·
                refine ⟨103548663970949465336759141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276129770589198574231357709 103548663970949465336759141)
                ·
                  refine ⟨19415374494553024750642339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103548663970949465336759141 19415374494553024750642339)
                  ·
                    refine ⟨29123061741829537125963509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19415374494553024750642339 29123061741829537125963509)
                    ·
                      refine ⟨2730287038296519105559079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29123061741829537125963509 2730287038296519105559079)
                      ·
                        rfl

theorem cell23_5317215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_5317215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317215 prefixEnd_5317215 := by exact prefixLift 5317215
  have htrace : WordTrace (prefixWord ++ tailWord_5317215) baseStart_5317215 baseEnd_5317215 := by
    simpa [prefixWord, tailWord_5317215, baseEnd_5317215] using wordTrace_append hprefix tailTrace_5317215
  have hstable : (prefixWord ++ tailWord_5317215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317215).length < 2 ^ (prefixWord ++ tailWord_5317215).sum := by decide
  have hdescent : baseEnd_5317215 < baseStart_5317215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317225 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_5317225 : Nat := 118140960795 + 5317225 * 2 ^ 59
def prefixEnd_5317225 : Nat := 4983230072969 + 3 ^ 40 * 5317225 * 2
def baseEnd_5317225 : Nat := 2730292173103064066434033

theorem tailTrace_5317225 : CollatzResearch.WordTrace tailWord_5317225 prefixEnd_5317225 2730292173103064066434033 := by
  unfold tailWord_5317225
  simp only [CollatzResearch.WordTrace]
  refine ⟨193935128161609409576801129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129290085441072939717867419 193935128161609409576801129)
  ·
    refine ⟨145451346121207057182600847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193935128161609409576801129 145451346121207057182600847)
    ·
      refine ⟨218177019181810585773901271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145451346121207057182600847 218177019181810585773901271)
      ·
        refine ⟨327265528772715878660851907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218177019181810585773901271 327265528772715878660851907)
        ·
          refine ⟨490898293159073817991277861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327265528772715878660851907 490898293159073817991277861)
          ·
            refine ⟨92043429967326340873364599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 490898293159073817991277861 92043429967326340873364599)
            ·
              refine ⟨138065144950989511310046899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92043429967326340873364599 138065144950989511310046899)
              ·
                refine ⟨207097717426484266965070349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138065144950989511310046899 207097717426484266965070349)
                ·
                  refine ⟨77661644034931600111901381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207097717426484266965070349 77661644034931600111901381)
                  ·
                    refine ⟨14561558256549675020981509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77661644034931600111901381 14561558256549675020981509)
                    ·
                      refine ⟨2730292173103064066434033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14561558256549675020981509 2730292173103064066434033)
                      ·
                        rfl

theorem cell23_5317225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_5317225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317225 prefixEnd_5317225 := by exact prefixLift 5317225
  have htrace : WordTrace (prefixWord ++ tailWord_5317225) baseStart_5317225 baseEnd_5317225 := by
    simpa [prefixWord, tailWord_5317225, baseEnd_5317225] using wordTrace_append hprefix tailTrace_5317225
  have hstable : (prefixWord ++ tailWord_5317225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317225).length < 2 ^ (prefixWord ++ tailWord_5317225).sum := by decide
  have hdescent : baseEnd_5317225 < baseStart_5317225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317252 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 7]
def baseStart_5317252 : Nat := 118140960795 + 5317252 * 2 ^ 59
def prefixEnd_5317252 : Nat := 4983230072969 + 3 ^ 40 * 5317252 * 2
def baseEnd_5317252 : Nat := 303367337453415051199601

theorem tailTrace_5317252 : CollatzResearch.WordTrace tailWord_5317252 prefixEnd_5317252 303367337453415051199601 := by
  unfold tailWord_5317252
  simp only [CollatzResearch.WordTrace]
  refine ⟨96968056466255796594017005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129290741955007728792022673 96968056466255796594017005)
  ·
    refine ⟨36363021174845923722756377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96968056466255796594017005 36363021174845923722756377)
    ·
      refine ⟨27272265881134442792067283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36363021174845923722756377 27272265881134442792067283)
      ·
        refine ⟨40908398821701664188100925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27272265881134442792067283 40908398821701664188100925)
        ·
          refine ⟨15340649558138124070537847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40908398821701664188100925 15340649558138124070537847)
          ·
            refine ⟨23010974337207186105806771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15340649558138124070537847 23010974337207186105806771)
            ·
              refine ⟨34516461505810779158710157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23010974337207186105806771 34516461505810779158710157)
              ·
                refine ⟨12943673064679042184516309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34516461505810779158710157 12943673064679042184516309)
                ·
                  refine ⟨303367337453415051199601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12943673064679042184516309 303367337453415051199601)
                  ·
                    rfl

theorem cell23_5317252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_5317252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317252 prefixEnd_5317252 := by exact prefixLift 5317252
  have htrace : WordTrace (prefixWord ++ tailWord_5317252) baseStart_5317252 baseEnd_5317252 := by
    simpa [prefixWord, tailWord_5317252, baseEnd_5317252] using wordTrace_append hprefix tailTrace_5317252
  have hstable : (prefixWord ++ tailWord_5317252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317252).length < 2 ^ (prefixWord ++ tailWord_5317252).sum := by decide
  have hdescent : baseEnd_5317252 < baseStart_5317252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317359 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 6]
def baseStart_5317359 : Nat := 118140960795 + 5317359 * 2 ^ 59
def prefixEnd_5317359 : Nat := 4983230072969 + 3 ^ 40 * 5317359 * 2
def baseEnd_5317359 : Nat := 303373442167862949128713

theorem tailTrace_5317359 : CollatzResearch.WordTrace tailWord_5317359 prefixEnd_5317359 303373442167862949128713 := by
  unfold tailWord_5317359
  simp only [CollatzResearch.WordTrace]
  refine ⟨193940015543123950462179131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129293343695415966974786087 193940015543123950462179131)
  ·
    refine ⟨290910023314685925693268697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193940015543123950462179131 290910023314685925693268697)
    ·
      refine ⟨218182517486014444269951523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290910023314685925693268697 218182517486014444269951523)
      ·
        refine ⟨327273776229021666404927285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218182517486014444269951523 327273776229021666404927285)
        ·
          refine ⟨30681916521470781225461933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327273776229021666404927285 30681916521470781225461933)
          ·
            refine ⟨11505718695551542959548225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30681916521470781225461933 11505718695551542959548225)
            ·
              refine ⟨8629289021663657219661169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11505718695551542959548225 8629289021663657219661169)
              ·
                refine ⟨6471966766247742914745877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8629289021663657219661169 6471966766247742914745877)
                ·
                  refine ⟨303373442167862949128713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6471966766247742914745877 303373442167862949128713)
                  ·
                    rfl

theorem cell23_5317359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 6].length) (baseStart_5317359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317359 prefixEnd_5317359 := by exact prefixLift 5317359
  have htrace : WordTrace (prefixWord ++ tailWord_5317359) baseStart_5317359 baseEnd_5317359 := by
    simpa [prefixWord, tailWord_5317359, baseEnd_5317359] using wordTrace_append hprefix tailTrace_5317359
  have hstable : (prefixWord ++ tailWord_5317359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317359).length < 2 ^ (prefixWord ++ tailWord_5317359).sum := by decide
  have hdescent : baseEnd_5317359 < baseStart_5317359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317369 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 3]
def baseStart_5317369 : Nat := 118140960795 + 5317369 * 2 ^ 59
def prefixEnd_5317369 : Nat := 4983230072969 + 3 ^ 40 * 5317369 * 2
def baseEnd_5317369 : Nat := 2730366114317311503033371

theorem tailTrace_5317369 : CollatzResearch.WordTrace tailWord_5317369 prefixEnd_5317369 2730366114317311503033371 := by
  unfold tailWord_5317369
  simp only [CollatzResearch.WordTrace]
  refine ⟨193940380273087722170043161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129293586848725148113362107 193940380273087722170043161)
  ·
    refine ⟨145455285204815791627532371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193940380273087722170043161 145455285204815791627532371)
    ·
      refine ⟨218182927807223687441298557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145455285204815791627532371 218182927807223687441298557)
      ·
        refine ⟨81818597927708882790486959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218182927807223687441298557 81818597927708882790486959)
        ·
          refine ⟨122727896891563324185730439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81818597927708882790486959 122727896891563324185730439)
          ·
            refine ⟨184091845337344986278595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122727896891563324185730439 184091845337344986278595659)
            ·
              refine ⟨276137768006017479417893489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184091845337344986278595659 276137768006017479417893489)
              ·
                refine ⟨207103326004513109563420117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276137768006017479417893489 207103326004513109563420117)
                ·
                  refine ⟨4853984203230776005392659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 207103326004513109563420117 4853984203230776005392659)
                  ·
                    refine ⟨7280976304846164008088989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4853984203230776005392659 7280976304846164008088989)
                    ·
                      refine ⟨2730366114317311503033371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7280976304846164008088989 2730366114317311503033371)
                      ·
                        rfl

theorem cell23_5317369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_5317369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317369 prefixEnd_5317369 := by exact prefixLift 5317369
  have htrace : WordTrace (prefixWord ++ tailWord_5317369) baseStart_5317369 baseEnd_5317369 := by
    simpa [prefixWord, tailWord_5317369, baseEnd_5317369] using wordTrace_append hprefix tailTrace_5317369
  have hstable : (prefixWord ++ tailWord_5317369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317369).length < 2 ^ (prefixWord ++ tailWord_5317369).sum := by decide
  have hdescent : baseEnd_5317369 < baseStart_5317369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317379 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 1, 5, 2]
def baseStart_5317379 : Nat := 118140960795 + 5317379 * 2 ^ 59
def prefixEnd_5317379 : Nat := 4983230072969 + 3 ^ 40 * 5317379 * 2
def baseEnd_5317379 : Nat := 2730371249123856463908325

theorem tailTrace_5317379 : CollatzResearch.WordTrace tailWord_5317379 prefixEnd_5317379 2730371249123856463908325 := by
  unfold tailWord_5317379
  simp only [CollatzResearch.WordTrace]
  refine ⟨193940745003051493877907191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129293830002034329251938127 193940745003051493877907191)
  ·
    refine ⟨290911117504577240816860787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193940745003051493877907191 290911117504577240816860787)
    ·
      refine ⟨436366676256865861225291181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290911117504577240816860787 436366676256865861225291181)
      ·
        refine ⟨163637503596324697959484193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436366676256865861225291181 163637503596324697959484193)
        ·
          refine ⟨122728127697243523469613145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163637503596324697959484193 122728127697243523469613145)
          ·
            refine ⟨92046095772932642602209859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122728127697243523469613145 92046095772932642602209859)
            ·
              refine ⟨138069143659398963903314789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92046095772932642602209859 138069143659398963903314789)
              ·
                refine ⟨25887964436137305731871523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138069143659398963903314789 25887964436137305731871523)
                ·
                  refine ⟨38831946654205958597807285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25887964436137305731871523 38831946654205958597807285)
                  ·
                    refine ⟨3640494998831808618544433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38831946654205958597807285 3640494998831808618544433)
                    ·
                      refine ⟨2730371249123856463908325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640494998831808618544433 2730371249123856463908325)
                      ·
                        rfl

theorem cell23_5317379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_5317379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317379 prefixEnd_5317379 := by exact prefixLift 5317379
  have htrace : WordTrace (prefixWord ++ tailWord_5317379) baseStart_5317379 baseEnd_5317379 := by
    simpa [prefixWord, tailWord_5317379, baseEnd_5317379] using wordTrace_append hprefix tailTrace_5317379
  have hstable : (prefixWord ++ tailWord_5317379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317379).length < 2 ^ (prefixWord ++ tailWord_5317379).sum := by decide
  have hdescent : baseEnd_5317379 < baseStart_5317379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317386 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_5317386 : Nat := 118140960795 + 5317386 * 2 ^ 59
def prefixEnd_5317386 : Nat := 4983230072969 + 3 ^ 40 * 5317386 * 2
def baseEnd_5317386 : Nat := 2730374843488437936520793

theorem tailTrace_5317386 : CollatzResearch.WordTrace tailWord_5317386 prefixEnd_5317386 2730374843488437936520793 := by
  unfold tailWord_5317386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48485250078506533518353003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129294000209350756048941341 48485250078506533518353003)
  ·
    refine ⟨72727875117759800277529505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48485250078506533518353003 72727875117759800277529505)
    ·
      refine ⟨54545906338319850208147129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72727875117759800277529505 54545906338319850208147129)
      ·
        refine ⟨40909429753739887656110347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54545906338319850208147129 40909429753739887656110347)
        ·
          refine ⟨61364144630609831484165521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40909429753739887656110347 61364144630609831484165521)
          ·
            refine ⟨46023108472957373613124141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61364144630609831484165521 46023108472957373613124141)
            ·
              refine ⟨17258665677359015104921553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46023108472957373613124141 17258665677359015104921553)
              ·
                refine ⟨12943999258019261328691165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17258665677359015104921553 12943999258019261328691165)
                ·
                  refine ⟨4853999721757222998259187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12943999258019261328691165 4853999721757222998259187)
                  ·
                    refine ⟨7280999582635834497388781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4853999721757222998259187 7280999582635834497388781)
                    ·
                      refine ⟨2730374843488437936520793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7280999582635834497388781 2730374843488437936520793)
                      ·
                        rfl

theorem cell23_5317386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_5317386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317386 prefixEnd_5317386 := by exact prefixLift 5317386
  have htrace : WordTrace (prefixWord ++ tailWord_5317386) baseStart_5317386 baseEnd_5317386 := by
    simpa [prefixWord, tailWord_5317386, baseEnd_5317386] using wordTrace_append hprefix tailTrace_5317386
  have hstable : (prefixWord ++ tailWord_5317386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317386).length < 2 ^ (prefixWord ++ tailWord_5317386).sum := by decide
  have hdescent : baseEnd_5317386 < baseStart_5317386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317429 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5317429 : Nat := 118140960795 + 5317429 * 2 ^ 59
def prefixEnd_5317429 : Nat := 4983230072969 + 3 ^ 40 * 5317429 * 2
def baseEnd_5317429 : Nat := 2730396923156581268283095

theorem tailTrace_5317429 : CollatzResearch.WordTrace tailWord_5317429 prefixEnd_5317429 2730396923156581268283095 := by
  unfold tailWord_5317429
  simp only [CollatzResearch.WordTrace]
  refine ⟨193942568652870352417227341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129295045768580234944818227 193942568652870352417227341)
  ·
    refine ⟨72728463244826382156460253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193942568652870352417227341 72728463244826382156460253)
    ·
      refine ⟨27273173716809893308672595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72728463244826382156460253 27273173716809893308672595)
      ·
        refine ⟨40909760575214839963008893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27273173716809893308672595 40909760575214839963008893)
        ·
          refine ⟨15341160215705564986128335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40909760575214839963008893 15341160215705564986128335)
          ·
            refine ⟨23011740323558347479192503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15341160215705564986128335 23011740323558347479192503)
            ·
              refine ⟨34517610485337521218788755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23011740323558347479192503 34517610485337521218788755)
              ·
                refine ⟨51776415728006281828183133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34517610485337521218788755 51776415728006281828183133)
                ·
                  refine ⟨19416155898002355685568675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51776415728006281828183133 19416155898002355685568675)
                  ·
                    refine ⟨29124233847003533528353013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19416155898002355685568675 29124233847003533528353013)
                    ·
                      refine ⟨2730396923156581268283095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29124233847003533528353013 2730396923156581268283095)
                      ·
                        rfl

theorem cell23_5317429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5317429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317429 prefixEnd_5317429 := by exact prefixLift 5317429
  have htrace : WordTrace (prefixWord ++ tailWord_5317429) baseStart_5317429 baseEnd_5317429 := by
    simpa [prefixWord, tailWord_5317429, baseEnd_5317429] using wordTrace_append hprefix tailTrace_5317429
  have hstable : (prefixWord ++ tailWord_5317429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317429).length < 2 ^ (prefixWord ++ tailWord_5317429).sum := by decide
  have hdescent : baseEnd_5317429 < baseStart_5317429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317432 : List Nat := [2, 1, 2, 1, 3, 2, 2, 10]
def baseStart_5317432 : Nat := 118140960795 + 5317432 * 2 ^ 59
def prefixEnd_5317432 : Nat := 4983230072969 + 3 ^ 40 * 5317432 * 2
def baseEnd_5317432 : Nat := 101125869022168324316503

theorem tailTrace_5317432 : CollatzResearch.WordTrace tailWord_5317432 prefixEnd_5317432 101125869022168324316503 := by
  unfold tailWord_5317432
  simp only [CollatzResearch.WordTrace]
  refine ⟨96971339035929741964793275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129295118714572989286391033 96971339035929741964793275)
  ·
    refine ⟨145457008553894612947189913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96971339035929741964793275 145457008553894612947189913)
    ·
      refine ⟨109092756415420959710392435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145457008553894612947189913 109092756415420959710392435)
      ·
        refine ⟨163639134623131439565588653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109092756415420959710392435 163639134623131439565588653)
        ·
          refine ⟨61364675483674289837095745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163639134623131439565588653 61364675483674289837095745)
          ·
            refine ⟨46023506612755717377821809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61364675483674289837095745 46023506612755717377821809)
            ·
              refine ⟨34517629959566788033366357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46023506612755717377821809 34517629959566788033366357)
              ·
                refine ⟨101125869022168324316503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34517629959566788033366357 101125869022168324316503)
                ·
                  rfl

theorem cell23_5317432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 10].length) (baseStart_5317432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317432 prefixEnd_5317432 := by exact prefixLift 5317432
  have htrace : WordTrace (prefixWord ++ tailWord_5317432) baseStart_5317432 baseEnd_5317432 := by
    simpa [prefixWord, tailWord_5317432, baseEnd_5317432] using wordTrace_append hprefix tailTrace_5317432
  have hstable : (prefixWord ++ tailWord_5317432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317432).length < 2 ^ (prefixWord ++ tailWord_5317432).sum := by decide
  have hdescent : baseEnd_5317432 < baseStart_5317432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317439 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_5317439 : Nat := 118140960795 + 5317439 * 2 ^ 59
def prefixEnd_5317439 : Nat := 4983230072969 + 3 ^ 40 * 5317439 * 2
def baseEnd_5317439 : Nat := 2730402057963126229158049

theorem tailTrace_5317439 : CollatzResearch.WordTrace tailWord_5317439 prefixEnd_5317439 2730402057963126229158049 := by
  unfold tailWord_5317439
  simp only [CollatzResearch.WordTrace]
  refine ⟨193942933382834124125091371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129295288921889416083394247 193942933382834124125091371)
  ·
    refine ⟨290914400074251186187637057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193942933382834124125091371 290914400074251186187637057)
    ·
      refine ⟨218185800055688389640727793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290914400074251186187637057 218185800055688389640727793)
      ·
        refine ⟨163639350041766292230545845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218185800055688389640727793 163639350041766292230545845)
        ·
          refine ⟨15341189066415589896613673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163639350041766292230545845 15341189066415589896613673)
          ·
            refine ⟨11505891799811692422460255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15341189066415589896613673 11505891799811692422460255)
            ·
              refine ⟨17258837699717538633690383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505891799811692422460255 17258837699717538633690383)
              ·
                refine ⟨25888256549576307950535575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17258837699717538633690383 25888256549576307950535575)
                ·
                  refine ⟨38832384824364461925803363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25888256549576307950535575 38832384824364461925803363)
                  ·
                    refine ⟨58248577236546692888705045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38832384824364461925803363 58248577236546692888705045)
                    ·
                      refine ⟨2730402057963126229158049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58248577236546692888705045 2730402057963126229158049)
                      ·
                        rfl

theorem cell23_5317439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_5317439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317439 prefixEnd_5317439 := by exact prefixLift 5317439
  have htrace : WordTrace (prefixWord ++ tailWord_5317439) baseStart_5317439 baseEnd_5317439 := by
    simpa [prefixWord, tailWord_5317439, baseEnd_5317439] using wordTrace_append hprefix tailTrace_5317439
  have hstable : (prefixWord ++ tailWord_5317439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317439).length < 2 ^ (prefixWord ++ tailWord_5317439).sum := by decide
  have hdescent : baseEnd_5317439 < baseStart_5317439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317449 : List Nat := [1, 2, 1, 1, 2, 5, 4, 7]
def baseStart_5317449 : Nat := 118140960795 + 5317449 * 2 ^ 59
def prefixEnd_5317449 : Nat := 4983230072969 + 3 ^ 40 * 5317449 * 2
def baseEnd_5317449 : Nat := 101126192324802636667889

theorem tailTrace_5317449 : CollatzResearch.WordTrace tailWord_5317449 prefixEnd_5317449 101126192324802636667889 := by
  unfold tailWord_5317449
  simp only [CollatzResearch.WordTrace]
  refine ⟨193943298112797895832955401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129295532075198597221970267 193943298112797895832955401)
  ·
    refine ⟨145457473584598421874716551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193943298112797895832955401 145457473584598421874716551)
    ·
      refine ⟨218186210376897632812074827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145457473584598421874716551 218186210376897632812074827)
      ·
        refine ⟨327279315565346449218112241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218186210376897632812074827 327279315565346449218112241)
        ·
          refine ⟨245459486674009836913584181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327279315565346449218112241 245459486674009836913584181)
          ·
            refine ⟨23011826875688422210648517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245459486674009836913584181 23011826875688422210648517)
            ·
              refine ⟨4314717539191579164496597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23011826875688422210648517 4314717539191579164496597)
              ·
                refine ⟨101126192324802636667889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4314717539191579164496597 101126192324802636667889)
                ·
                  rfl

theorem cell23_5317449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 7].length) (baseStart_5317449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317449 prefixEnd_5317449 := by exact prefixLift 5317449
  have htrace : WordTrace (prefixWord ++ tailWord_5317449) baseStart_5317449 baseEnd_5317449 := by
    simpa [prefixWord, tailWord_5317449, baseEnd_5317449] using wordTrace_append hprefix tailTrace_5317449
  have hstable : (prefixWord ++ tailWord_5317449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317449).length < 2 ^ (prefixWord ++ tailWord_5317449).sum := by decide
  have hdescent : baseEnd_5317449 < baseStart_5317449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317459 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 3]
def baseStart_5317459 : Nat := 118140960795 + 5317459 * 2 ^ 59
def prefixEnd_5317459 : Nat := 4983230072969 + 3 ^ 40 * 5317459 * 2
def baseEnd_5317459 : Nat := 2730412327576216150907957

theorem tailTrace_5317459 : CollatzResearch.WordTrace tailWord_5317459 prefixEnd_5317459 2730412327576216150907957 := by
  unfold tailWord_5317459
  simp only [CollatzResearch.WordTrace]
  refine ⟨193943662842761667540819431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129295775228507778360546287 193943662842761667540819431)
  ·
    refine ⟨290915494264142501311229147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193943662842761667540819431 290915494264142501311229147)
    ·
      refine ⟨436373241396213751966843721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290915494264142501311229147 436373241396213751966843721)
      ·
        refine ⟨327279931047160313975132791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436373241396213751966843721 327279931047160313975132791)
        ·
          refine ⟨490919896570740470962699187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327279931047160313975132791 490919896570740470962699187)
          ·
            refine ⟨736379844856110706444048781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490919896570740470962699187 736379844856110706444048781)
            ·
              refine ⟨276142441821041514916518293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 736379844856110706444048781 276142441821041514916518293)
              ·
                refine ⟨12944176960361321011711795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 276142441821041514916518293 12944176960361321011711795)
                ·
                  refine ⟨19416265440541981517567693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12944176960361321011711795 19416265440541981517567693)
                  ·
                    refine ⟨7281099540203243069087885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19416265440541981517567693 7281099540203243069087885)
                    ·
                      refine ⟨2730412327576216150907957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7281099540203243069087885 2730412327576216150907957)
                      ·
                        rfl

theorem cell23_5317459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_5317459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317459 prefixEnd_5317459 := by exact prefixLift 5317459
  have htrace : WordTrace (prefixWord ++ tailWord_5317459) baseStart_5317459 baseEnd_5317459 := by
    simpa [prefixWord, tailWord_5317459, baseEnd_5317459] using wordTrace_append hprefix tailTrace_5317459
  have hstable : (prefixWord ++ tailWord_5317459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317459).length < 2 ^ (prefixWord ++ tailWord_5317459).sum := by decide
  have hdescent : baseEnd_5317459 < baseStart_5317459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317503 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 1, 3, 2]
def baseStart_5317503 : Nat := 118140960795 + 5317503 * 2 ^ 59
def prefixEnd_5317503 : Nat := 4983230072969 + 3 ^ 40 * 5317503 * 2
def baseEnd_5317503 : Nat := 2730434920725013978757755

theorem tailTrace_5317503 : CollatzResearch.WordTrace tailWord_5317503 prefixEnd_5317503 2730434920725013978757755 := by
  unfold tailWord_5317503
  simp only [CollatzResearch.WordTrace]
  refine ⟨193945267654602263055421163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129296845103068175370280775 193945267654602263055421163)
  ·
    refine ⟨290917901481903394583131745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193945267654602263055421163 290917901481903394583131745)
    ·
      refine ⟨218188426111427545937348809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290917901481903394583131745 218188426111427545937348809)
      ·
        refine ⟨163641319583570659453011607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218188426111427545937348809 163641319583570659453011607)
        ·
          refine ⟨245461979375355989179517411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163641319583570659453011607 245461979375355989179517411)
          ·
            refine ⟨368192969063033983769276117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245461979375355989179517411 368192969063033983769276117)
            ·
              refine ⟨8629522712414858994592409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 368192969063033983769276117 8629522712414858994592409)
              ·
                refine ⟨6472142034311144245944307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8629522712414858994592409 6472142034311144245944307)
                ·
                  refine ⟨9708213051466716368916461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472142034311144245944307 9708213051466716368916461)
                  ·
                    refine ⟨3640579894300018638343673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9708213051466716368916461 3640579894300018638343673)
                    ·
                      refine ⟨2730434920725013978757755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640579894300018638343673 2730434920725013978757755)
                      ·
                        rfl

theorem cell23_5317503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_5317503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317503 prefixEnd_5317503 := by exact prefixLift 5317503
  have htrace : WordTrace (prefixWord ++ tailWord_5317503) baseStart_5317503 baseEnd_5317503 := by
    simpa [prefixWord, tailWord_5317503, baseEnd_5317503] using wordTrace_append hprefix tailTrace_5317503
  have hstable : (prefixWord ++ tailWord_5317503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317503).length < 2 ^ (prefixWord ++ tailWord_5317503).sum := by decide
  have hdescent : baseEnd_5317503 < baseStart_5317503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317516 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 3, 4, 2]
def baseStart_5317516 : Nat := 118140960795 + 5317516 * 2 ^ 59
def prefixEnd_5317516 : Nat := 4983230072969 + 3 ^ 40 * 5317516 * 2
def baseEnd_5317516 : Nat := 2730441595973522427895195

theorem tailTrace_5317516 : CollatzResearch.WordTrace tailWord_5317516 prefixEnd_5317516 2730441595973522427895195 := by
  unfold tailWord_5317516
  simp only [CollatzResearch.WordTrace]
  refine ⟨96972870901777583137822201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129297161202370110850429601 96972870901777583137822201)
  ·
    refine ⟨72729653176333187353366651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96972870901777583137822201 72729653176333187353366651)
    ·
      refine ⟨109094479764499781030049977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72729653176333187353366651 109094479764499781030049977)
      ·
        refine ⟨81820859823374835772537483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109094479764499781030049977 81820859823374835772537483)
        ·
          refine ⟨122731289735062253658806225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81820859823374835772537483 122731289735062253658806225)
          ·
            refine ⟨92048467301296690244104669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122731289735062253658806225 92048467301296690244104669)
            ·
              refine ⟨34518175237986258841539251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92048467301296690244104669 34518175237986258841539251)
              ·
                refine ⟨51777262856979388262308877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34518175237986258841539251 51777262856979388262308877)
                ·
                  refine ⟨19416473571367270598365829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51777262856979388262308877 19416473571367270598365829)
                  ·
                    refine ⟨3640588794631363237193593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19416473571367270598365829 3640588794631363237193593)
                    ·
                      refine ⟨2730441595973522427895195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640588794631363237193593 2730441595973522427895195)
                      ·
                        rfl

theorem cell23_5317516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_5317516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317516 prefixEnd_5317516 := by exact prefixLift 5317516
  have htrace : WordTrace (prefixWord ++ tailWord_5317516) baseStart_5317516 baseEnd_5317516 := by
    simpa [prefixWord, tailWord_5317516, baseEnd_5317516] using wordTrace_append hprefix tailTrace_5317516
  have hstable : (prefixWord ++ tailWord_5317516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317516).length < 2 ^ (prefixWord ++ tailWord_5317516).sum := by decide
  have hdescent : baseEnd_5317516 < baseStart_5317516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317529 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_5317529 : Nat := 118140960795 + 5317529 * 2 ^ 59
def prefixEnd_5317529 : Nat := 4983230072969 + 3 ^ 40 * 5317529 * 2
def baseEnd_5317529 : Nat := 2730448271222030877032635

theorem tailTrace_5317529 : CollatzResearch.WordTrace tailWord_5317529 prefixEnd_5317529 2730448271222030877032635 := by
  unfold tailWord_5317529
  simp only [CollatzResearch.WordTrace]
  refine ⟨193946215952508069495867641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129297477301672046330578427 193946215952508069495867641)
  ·
    refine ⟨145459661964381052121900731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193946215952508069495867641 145459661964381052121900731)
    ·
      refine ⟨218189492946571578182851097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145459661964381052121900731 218189492946571578182851097)
      ·
        refine ⟨163642119709928683637138323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218189492946571578182851097 163642119709928683637138323)
        ·
          refine ⟨245463179564893025455707485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163642119709928683637138323 245463179564893025455707485)
          ·
            refine ⟨92048692336834884545890307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245463179564893025455707485 92048692336834884545890307)
            ·
              refine ⟨138073038505252326818835461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92048692336834884545890307 138073038505252326818835461)
              ·
                refine ⟨25888694719734811278531649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138073038505252326818835461 25888694719734811278531649)
                ·
                  refine ⟨19416521039801108458898737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25888694719734811278531649 19416521039801108458898737)
                  ·
                    refine ⟨14562390779850831344174053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19416521039801108458898737 14562390779850831344174053)
                    ·
                      refine ⟨2730448271222030877032635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14562390779850831344174053 2730448271222030877032635)
                      ·
                        rfl

theorem cell23_5317529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_5317529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317529 prefixEnd_5317529 := by exact prefixLift 5317529
  have htrace : WordTrace (prefixWord ++ tailWord_5317529) baseStart_5317529 baseEnd_5317529 := by
    simpa [prefixWord, tailWord_5317529, baseEnd_5317529] using wordTrace_append hprefix tailTrace_5317529
  have hstable : (prefixWord ++ tailWord_5317529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317529).length < 2 ^ (prefixWord ++ tailWord_5317529).sum := by decide
  have hdescent : baseEnd_5317529 < baseStart_5317529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317566 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_5317566 : Nat := 118140960795 + 5317566 * 2 ^ 59
def prefixEnd_5317566 : Nat := 4983230072969 + 3 ^ 40 * 5317566 * 2
def baseEnd_5317566 : Nat := 2730467270006247232269965

theorem tailTrace_5317566 : CollatzResearch.WordTrace tailWord_5317566 prefixEnd_5317566 2730467270006247232269965 := by
  unfold tailWord_5317566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24243445681671753101870569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129298376968916016543309701 24243445681671753101870569)
  ·
    refine ⟨18182584261253814826402927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24243445681671753101870569 18182584261253814826402927)
    ·
      refine ⟨27273876391880722239604391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18182584261253814826402927 27273876391880722239604391)
      ·
        refine ⟨40910814587821083359406587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27273876391880722239604391 40910814587821083359406587)
        ·
          refine ⟨61366221881731625039109881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40910814587821083359406587 61366221881731625039109881)
          ·
            refine ⟨46024666411298718779332411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61366221881731625039109881 46024666411298718779332411)
            ·
              refine ⟨69036999616948078168998617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46024666411298718779332411 69036999616948078168998617)
              ·
                refine ⟨51777749712711058626748963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69036999616948078168998617 51777749712711058626748963)
                ·
                  refine ⟨77666624569066587940123445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51777749712711058626748963 77666624569066587940123445)
                  ·
                    refine ⟨7281246053349992619386573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77666624569066587940123445 7281246053349992619386573)
                    ·
                      refine ⟨2730467270006247232269965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7281246053349992619386573 2730467270006247232269965)
                      ·
                        rfl

theorem cell23_5317566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_5317566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317566 prefixEnd_5317566 := by exact prefixLift 5317566
  have htrace : WordTrace (prefixWord ++ tailWord_5317566) baseStart_5317566 baseEnd_5317566 := by
    simpa [prefixWord, tailWord_5317566, baseEnd_5317566] using wordTrace_append hprefix tailTrace_5317566
  have hstable : (prefixWord ++ tailWord_5317566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317566).length < 2 ^ (prefixWord ++ tailWord_5317566).sum := by decide
  have hdescent : baseEnd_5317566 < baseStart_5317566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317590 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_5317590 : Nat := 118140960795 + 5317590 * 2 ^ 59
def prefixEnd_5317590 : Nat := 4983230072969 + 3 ^ 40 * 5317590 * 2
def baseEnd_5317590 : Nat := 303386621504661682041095

theorem tailTrace_5317590 : CollatzResearch.WordTrace tailWord_5317590 prefixEnd_5317590 303386621504661682041095 := by
  unfold tailWord_5317590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121777550330442307114889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129298960536858051275892149 12121777550330442307114889)
  ·
    refine ⟨9091333162747831730336167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12121777550330442307114889 9091333162747831730336167)
    ·
      refine ⟨13636999744121747595504251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9091333162747831730336167 13636999744121747595504251)
      ·
        refine ⟨20455499616182621393256377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13636999744121747595504251 20455499616182621393256377)
        ·
          refine ⟨15341624712136966044942283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20455499616182621393256377 15341624712136966044942283)
          ·
            refine ⟨23012437068205449067413425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15341624712136966044942283 23012437068205449067413425)
            ·
              refine ⟨17259327801154086800560069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23012437068205449067413425 17259327801154086800560069)
              ·
                refine ⟨3236123962716391275105013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17259327801154086800560069 3236123962716391275105013)
                ·
                  refine ⟨303386621504661682041095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3236123962716391275105013 303386621504661682041095)
                  ·
                    rfl

theorem cell23_5317590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_5317590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317590 prefixEnd_5317590 := by exact prefixLift 5317590
  have htrace : WordTrace (prefixWord ++ tailWord_5317590) baseStart_5317590 baseEnd_5317590 := by
    simpa [prefixWord, tailWord_5317590, baseEnd_5317590] using wordTrace_append hprefix tailTrace_5317590
  have hstable : (prefixWord ++ tailWord_5317590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317590).length < 2 ^ (prefixWord ++ tailWord_5317590).sum := by decide
  have hdescent : baseEnd_5317590 < baseStart_5317590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317626 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_5317626 : Nat := 118140960795 + 5317626 * 2 ^ 59
def prefixEnd_5317626 : Nat := 4983230072969 + 3 ^ 40 * 5317626 * 2
def baseEnd_5317626 : Nat := 2730498078845516997519689

theorem tailTrace_5317626 : CollatzResearch.WordTrace tailWord_5317626 prefixEnd_5317626 2730498078845516997519689 := by
  unfold tailWord_5317626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48487438458289163765537183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129299835888771103374765821 48487438458289163765537183)
  ·
    refine ⟨72731157687433745648305775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48487438458289163765537183 72731157687433745648305775)
    ·
      refine ⟨109096736531150618472458663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72731157687433745648305775 109096736531150618472458663)
      ·
        refine ⟨163645104796725927708687995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109096736531150618472458663 163645104796725927708687995)
        ·
          refine ⟨245467657195088891563031993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163645104796725927708687995 245467657195088891563031993)
          ·
            refine ⟨184100742896316668672273995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245467657195088891563031993 184100742896316668672273995)
            ·
              refine ⟨276151114344475003008410993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184100742896316668672273995 276151114344475003008410993)
              ·
                refine ⟨207113335758356252256308245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276151114344475003008410993 207113335758356252256308245)
                ·
                  refine ⟨9708437613672949324514449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207113335758356252256308245 9708437613672949324514449)
                  ·
                    refine ⟨7281328210254711993385837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9708437613672949324514449 7281328210254711993385837)
                    ·
                      refine ⟨2730498078845516997519689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7281328210254711993385837 2730498078845516997519689)
                      ·
                        rfl

theorem cell23_5317626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_5317626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317626 prefixEnd_5317626 := by exact prefixLift 5317626
  have htrace : WordTrace (prefixWord ++ tailWord_5317626) baseStart_5317626 baseEnd_5317626 := by
    simpa [prefixWord, tailWord_5317626, baseEnd_5317626] using wordTrace_append hprefix tailTrace_5317626
  have hstable : (prefixWord ++ tailWord_5317626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317626).length < 2 ^ (prefixWord ++ tailWord_5317626).sum := by decide
  have hdescent : baseEnd_5317626 < baseStart_5317626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317643 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 3]
def baseStart_5317643 : Nat := 118140960795 + 5317643 * 2 ^ 59
def prefixEnd_5317643 : Nat := 4983230072969 + 3 ^ 40 * 5317643 * 2
def baseEnd_5317643 : Nat := 2730506808016643431007111

theorem tailTrace_5317643 : CollatzResearch.WordTrace tailWord_5317643 prefixEnd_5317643 2730506808016643431007111 := by
  unfold tailWord_5317643
  simp only [CollatzResearch.WordTrace]
  refine ⟨193950373874095066965517583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129300249249396711310345055 193950373874095066965517583)
  ·
    refine ⟨290925560811142600448276375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193950373874095066965517583 290925560811142600448276375)
    ·
      refine ⟨436388341216713900672414563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290925560811142600448276375 436388341216713900672414563)
      ·
        refine ⟨654582511825070851008621845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436388341216713900672414563 654582511825070851008621845)
        ·
          refine ⟨30683555241800196141029149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 654582511825070851008621845 30683555241800196141029149)
          ·
            refine ⟨11506333215675073552885931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30683555241800196141029149 11506333215675073552885931)
            ·
              refine ⟨17259499823512610329328897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11506333215675073552885931 17259499823512610329328897)
              ·
                refine ⟨12944624867634457746996673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17259499823512610329328897 12944624867634457746996673)
                ·
                  refine ⟨9708468650725843310247505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12944624867634457746996673 9708468650725843310247505)
                  ·
                    refine ⟨7281351488044382482685629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9708468650725843310247505 7281351488044382482685629)
                    ·
                      refine ⟨2730506808016643431007111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7281351488044382482685629 2730506808016643431007111)
                      ·
                        rfl

theorem cell23_5317643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 3].length) (baseStart_5317643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317643 prefixEnd_5317643 := by exact prefixLift 5317643
  have htrace : WordTrace (prefixWord ++ tailWord_5317643) baseStart_5317643 baseEnd_5317643 := by
    simpa [prefixWord, tailWord_5317643, baseEnd_5317643] using wordTrace_append hprefix tailTrace_5317643
  have hstable : (prefixWord ++ tailWord_5317643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317643).length < 2 ^ (prefixWord ++ tailWord_5317643).sum := by decide
  have hdescent : baseEnd_5317643 < baseStart_5317643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317646 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_5317646 : Nat := 118140960795 + 5317646 * 2 ^ 59
def prefixEnd_5317646 : Nat := 4983230072969 + 3 ^ 40 * 5317646 * 2
def baseEnd_5317646 : Nat := 303389816495400768807733

theorem tailTrace_5317646 : CollatzResearch.WordTrace tailWord_5317646 prefixEnd_5317646 303389816495400768807733 := by
  unfold tailWord_5317646
  simp only [CollatzResearch.WordTrace]
  refine ⟨24243810411635524809734599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129300322195389465651917861 24243810411635524809734599)
  ·
    refine ⟨36365715617453287214601899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24243810411635524809734599 36365715617453287214601899)
    ·
      refine ⟨54548573426179930821902849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36365715617453287214601899 54548573426179930821902849)
      ·
        refine ⟨40911430069634948116427137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54548573426179930821902849 40911430069634948116427137)
        ·
          refine ⟨30683572552226211087320353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40911430069634948116427137 30683572552226211087320353)
          ·
            refine ⟨23012679414169658315490265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30683572552226211087320353 23012679414169658315490265)
            ·
              refine ⟨17259509560627243736617699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23012679414169658315490265 17259509560627243736617699)
              ·
                refine ⟨25889264340940865604926549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17259509560627243736617699 25889264340940865604926549)
                ·
                  refine ⟨303389816495400768807733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25889264340940865604926549 303389816495400768807733)
                  ·
                    rfl

theorem cell23_5317646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_5317646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317646 prefixEnd_5317646 := by exact prefixLift 5317646
  have htrace : WordTrace (prefixWord ++ tailWord_5317646) baseStart_5317646 baseEnd_5317646 := by
    simpa [prefixWord, tailWord_5317646, baseEnd_5317646] using wordTrace_append hprefix tailTrace_5317646
  have hstable : (prefixWord ++ tailWord_5317646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317646).length < 2 ^ (prefixWord ++ tailWord_5317646).sum := by decide
  have hdescent : baseEnd_5317646 < baseStart_5317646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317649 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_5317649 : Nat := 118140960795 + 5317649 * 2 ^ 59
def prefixEnd_5317649 : Nat := 4983230072969 + 3 ^ 40 * 5317649 * 2
def baseEnd_5317649 : Nat := 2730509888900570407532083

theorem tailTrace_5317649 : CollatzResearch.WordTrace tailWord_5317649 prefixEnd_5317649 2730509888900570407532083 := by
  unfold tailWord_5317649
  simp only [CollatzResearch.WordTrace]
  refine ⟨193950592712073329990236001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129300395141382219993490667 193950592712073329990236001)
  ·
    refine ⟨145462944534054997492677001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193950592712073329990236001 145462944534054997492677001)
    ·
      refine ⟨109097208400541248119507751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145462944534054997492677001 109097208400541248119507751)
      ·
        refine ⟨163645812600811872179261627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109097208400541248119507751 163645812600811872179261627)
        ·
          refine ⟨245468718901217808268892441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163645812600811872179261627 245468718901217808268892441)
          ·
            refine ⟨184101539175913356201669331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245468718901217808268892441 184101539175913356201669331)
            ·
              refine ⟨276152308763870034302503997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184101539175913356201669331 276152308763870034302503997)
              ·
                refine ⟨103557115786451262863438999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276152308763870034302503997 103557115786451262863438999)
                ·
                  refine ⟨155335673679676894295158499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103557115786451262863438999 155335673679676894295158499)
                  ·
                    refine ⟨233003510519515341442737749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155335673679676894295158499 233003510519515341442737749)
                    ·
                      refine ⟨2730509888900570407532083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 233003510519515341442737749 2730509888900570407532083)
                      ·
                        rfl

theorem cell23_5317649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_5317649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317649 prefixEnd_5317649 := by exact prefixLift 5317649
  have htrace : WordTrace (prefixWord ++ tailWord_5317649) baseStart_5317649 baseEnd_5317649 := by
    simpa [prefixWord, tailWord_5317649, baseEnd_5317649] using wordTrace_append hprefix tailTrace_5317649
  have hstable : (prefixWord ++ tailWord_5317649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317649).length < 2 ^ (prefixWord ++ tailWord_5317649).sum := by decide
  have hdescent : baseEnd_5317649 < baseStart_5317649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317663 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 6]
def baseStart_5317663 : Nat := 118140960795 + 5317663 * 2 ^ 59
def prefixEnd_5317663 : Nat := 4983230072969 + 3 ^ 40 * 5317663 * 2
def baseEnd_5317663 : Nat := 303390786403303705861891

theorem tailTrace_5317663 : CollatzResearch.WordTrace tailWord_5317663 prefixEnd_5317663 303390786403303705861891 := by
  unfold tailWord_5317663
  simp only [CollatzResearch.WordTrace]
  refine ⟨193951103334022610381245643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129300735556015073587497095 193951103334022610381245643)
  ·
    refine ⟨290926655001033915571868465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193951103334022610381245643 290926655001033915571868465)
    ·
      refine ⟨218194991250775436678901349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290926655001033915571868465 218194991250775436678901349)
      ·
        refine ⟨40911560859520394377294003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218194991250775436678901349 40911560859520394377294003)
        ·
          refine ⟨61367341289280591565941005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40911560859520394377294003 61367341289280591565941005)
          ·
            refine ⟨23012752983480221837227877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61367341289280591565941005 23012752983480221837227877)
            ·
              refine ⟨4314891184402541594480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23012752983480221837227877 4314891184402541594480227)
              ·
                refine ⟨6472336776603812391720341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4314891184402541594480227 6472336776603812391720341)
                ·
                  refine ⟨303390786403303705861891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6472336776603812391720341 303390786403303705861891)
                  ·
                    rfl

theorem cell23_5317663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 6].length) (baseStart_5317663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317663 prefixEnd_5317663 := by exact prefixLift 5317663
  have htrace : WordTrace (prefixWord ++ tailWord_5317663) baseStart_5317663 baseEnd_5317663 := by
    simpa [prefixWord, tailWord_5317663, baseEnd_5317663] using wordTrace_append hprefix tailTrace_5317663
  have hstable : (prefixWord ++ tailWord_5317663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317663).length < 2 ^ (prefixWord ++ tailWord_5317663).sum := by decide
  have hdescent : baseEnd_5317663 < baseStart_5317663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317676 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_5317676 : Nat := 118140960795 + 5317676 * 2 ^ 59
def prefixEnd_5317676 : Nat := 4983230072969 + 3 ^ 40 * 5317676 * 2
def baseEnd_5317676 : Nat := 910174584292747267298153

theorem tailTrace_5317676 : CollatzResearch.WordTrace tailWord_5317676 prefixEnd_5317676 910174584292747267298153 := by
  unfold tailWord_5317676
  simp only [CollatzResearch.WordTrace]
  refine ⟨96975788741487756800734441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129301051655317009067645921 96975788741487756800734441)
  ·
    refine ⟨72731841556115817600550831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96975788741487756800734441 72731841556115817600550831)
    ·
      refine ⟨109097762334173726400826247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72731841556115817600550831 109097762334173726400826247)
      ·
        refine ⟨163646643501260589601239371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109097762334173726400826247 163646643501260589601239371)
        ·
          refine ⟨245469965251890884401859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163646643501260589601239371 245469965251890884401859057)
          ·
            refine ⟨184102473938918163301394293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245469965251890884401859057 184102473938918163301394293)
            ·
              refine ⟨17259606931773577809505715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184102473938918163301394293 17259606931773577809505715)
              ·
                refine ⟨25889410397660366714258573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17259606931773577809505715 25889410397660366714258573)
                ·
                  refine ⟨9708528899122637517846965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25889410397660366714258573 9708528899122637517846965)
                  ·
                    refine ⟨910174584292747267298153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9708528899122637517846965 910174584292747267298153)
                    ·
                      rfl

theorem cell23_5317676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_5317676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317676 prefixEnd_5317676 := by exact prefixLift 5317676
  have htrace : WordTrace (prefixWord ++ tailWord_5317676) baseStart_5317676 baseEnd_5317676 := by
    simpa [prefixWord, tailWord_5317676, baseEnd_5317676] using wordTrace_append hprefix tailTrace_5317676
  have hstable : (prefixWord ++ tailWord_5317676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317676).length < 2 ^ (prefixWord ++ tailWord_5317676).sum := by decide
  have hdescent : baseEnd_5317676 < baseStart_5317676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317730 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5317730 : Nat := 118140960795 + 5317730 * 2 ^ 59
def prefixEnd_5317730 : Nat := 4983230072969 + 3 ^ 40 * 5317730 * 2
def baseEnd_5317730 : Nat := 2730551480833584590619211

theorem tailTrace_5317730 : CollatzResearch.WordTrace tailWord_5317730 prefixEnd_5317730 2730551480833584590619211 := by
  unfold tailWord_5317730
  simp only [CollatzResearch.WordTrace]
  refine ⟨48488386756194970205983661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129302364683186587215956429 48488386756194970205983661)
  ·
    refine ⟨18183145033573113827243873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48488386756194970205983661 18183145033573113827243873)
    ·
      refine ⟨13637358775179835370432905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18183145033573113827243873 13637358775179835370432905)
      ·
        refine ⟨10228019081384876527824679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13637358775179835370432905 10228019081384876527824679)
        ·
          refine ⟨15342028622077314791737019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10228019081384876527824679 15342028622077314791737019)
          ·
            refine ⟨23013042933115972187605529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15342028622077314791737019 23013042933115972187605529)
            ·
              refine ⟨17259782199836979140704147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23013042933115972187605529 17259782199836979140704147)
              ·
                refine ⟨25889673299755468711056221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17259782199836979140704147 25889673299755468711056221)
                ·
                  refine ⟨9708627487408300766646083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25889673299755468711056221 9708627487408300766646083)
                  ·
                    refine ⟨14562941231112451149969125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9708627487408300766646083 14562941231112451149969125)
                    ·
                      refine ⟨2730551480833584590619211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14562941231112451149969125 2730551480833584590619211)
                      ·
                        rfl

theorem cell23_5317730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5317730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317730 prefixEnd_5317730 := by exact prefixLift 5317730
  have htrace : WordTrace (prefixWord ++ tailWord_5317730) baseStart_5317730 baseEnd_5317730 := by
    simpa [prefixWord, tailWord_5317730, baseEnd_5317730] using wordTrace_append hprefix tailTrace_5317730
  have hstable : (prefixWord ++ tailWord_5317730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317730).length < 2 ^ (prefixWord ++ tailWord_5317730).sum := by decide
  have hdescent : baseEnd_5317730 < baseStart_5317730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317733 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_5317733 : Nat := 118140960795 + 5317733 * 2 ^ 59
def prefixEnd_5317733 : Nat := 4983230072969 + 3 ^ 40 * 5317733 * 2
def baseEnd_5317733 : Nat := 2730553021275548078881697

theorem tailTrace_5317733 : CollatzResearch.WordTrace tailWord_5317733 prefixEnd_5317733 2730553021275548078881697 := by
  unfold tailWord_5317733
  simp only [CollatzResearch.WordTrace]
  refine ⟨193953656443769012336293853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129302437629179341557529235 193953656443769012336293853)
  ·
    refine ⟨72732621166413379626110195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193953656443769012336293853 72732621166413379626110195)
    ·
      refine ⟨109098931749620069439165293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72732621166413379626110195 109098931749620069439165293)
      ·
        refine ⟨40912099406107526039686985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109098931749620069439165293 40912099406107526039686985)
        ·
          refine ⟨30684074554580644529765239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40912099406107526039686985 30684074554580644529765239)
          ·
            refine ⟨46026111831870966794647859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30684074554580644529765239 46026111831870966794647859)
            ·
              refine ⟨69039167747806450191971789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46026111831870966794647859 69039167747806450191971789)
              ·
                refine ⟨25889687905427418821989421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69039167747806450191971789 25889687905427418821989421)
                ·
                  refine ⟨9708632964535282058246033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25889687905427418821989421 9708632964535282058246033)
                  ·
                    refine ⟨7281474723401461543684525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9708632964535282058246033 7281474723401461543684525)
                    ·
                      refine ⟨2730553021275548078881697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7281474723401461543684525 2730553021275548078881697)
                      ·
                        rfl

theorem cell23_5317733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_5317733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317733 prefixEnd_5317733 := by exact prefixLift 5317733
  have htrace : WordTrace (prefixWord ++ tailWord_5317733) baseStart_5317733 baseEnd_5317733 := by
    simpa [prefixWord, tailWord_5317733, baseEnd_5317733] using wordTrace_append hprefix tailTrace_5317733
  have hstable : (prefixWord ++ tailWord_5317733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317733).length < 2 ^ (prefixWord ++ tailWord_5317733).sum := by decide
  have hdescent : baseEnd_5317733 < baseStart_5317733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317764 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_5317764 : Nat := 118140960795 + 5317764 * 2 ^ 59
def prefixEnd_5317764 : Nat := 4983230072969 + 3 ^ 40 * 5317764 * 2
def baseEnd_5317764 : Nat := 2730568939175837457594055

theorem tailTrace_5317764 : CollatzResearch.WordTrace tailWord_5317764 prefixEnd_5317764 2730568939175837457594055 := by
  unfold tailWord_5317764
  simp only [CollatzResearch.WordTrace]
  refine ⟨96977393553328352315336173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129303191404437803087114897 96977393553328352315336173)
  ·
    refine ⟨36366522582498132118251065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96977393553328352315336173 36366522582498132118251065)
    ·
      refine ⟨27274891936873599088688299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36366522582498132118251065 27274891936873599088688299)
      ·
        refine ⟨40912337905310398633032449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27274891936873599088688299 40912337905310398633032449)
        ·
          refine ⟨30684253428982798974774337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40912337905310398633032449 30684253428982798974774337)
          ·
            refine ⟨23013190071737099231080753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30684253428982798974774337 23013190071737099231080753)
            ·
              refine ⟨17259892553802824423310565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23013190071737099231080753 17259892553802824423310565)
              ·
                refine ⟨3236229853838029579370731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17259892553802824423310565 3236229853838029579370731)
                ·
                  refine ⟨4854344780757044369056097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236229853838029579370731 4854344780757044369056097)
                  ·
                    refine ⟨3640758585567783276792073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4854344780757044369056097 3640758585567783276792073)
                    ·
                      refine ⟨2730568939175837457594055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640758585567783276792073 2730568939175837457594055)
                      ·
                        rfl

theorem cell23_5317764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_5317764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317764 prefixEnd_5317764 := by exact prefixLift 5317764
  have htrace : WordTrace (prefixWord ++ tailWord_5317764) baseStart_5317764 baseEnd_5317764 := by
    simpa [prefixWord, tailWord_5317764, baseEnd_5317764] using wordTrace_append hprefix tailTrace_5317764
  have hstable : (prefixWord ++ tailWord_5317764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317764).length < 2 ^ (prefixWord ++ tailWord_5317764).sum := by decide
  have hdescent : baseEnd_5317764 < baseStart_5317764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317816 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_5317816 : Nat := 118140960795 + 5317816 * 2 ^ 59
def prefixEnd_5317816 : Nat := 4983230072969 + 3 ^ 40 * 5317816 * 2
def baseEnd_5317816 : Nat := 2730595640169871254143815

theorem tailTrace_5317816 : CollatzResearch.WordTrace tailWord_5317816 prefixEnd_5317816 2730595640169871254143815 := by
  unfold tailWord_5317816
  simp only [CollatzResearch.WordTrace]
  refine ⟨96978341851234158755782651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129304455801645545007710201 96978341851234158755782651)
  ·
    refine ⟨145467512776851238133673977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96978341851234158755782651 145467512776851238133673977)
    ·
      refine ⟨109100634582638428600255483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145467512776851238133673977 109100634582638428600255483)
      ·
        refine ⟨163650951873957642900383225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109100634582638428600255483 163650951873957642900383225)
        ·
          refine ⟨122738213905468232175287419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163650951873957642900383225 122738213905468232175287419)
          ·
            refine ⟨184107320858202348262931129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122738213905468232175287419 184107320858202348262931129)
            ·
              refine ⟨138080490643651761197198347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184107320858202348262931129 138080490643651761197198347)
              ·
                refine ⟨207120735965477641795797521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138080490643651761197198347 207120735965477641795797521)
                ·
                  refine ⟨155340551974108231346848141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207120735965477641795797521 155340551974108231346848141)
                  ·
                    refine ⟨58252706990290586755068053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155340551974108231346848141 58252706990290586755068053)
                    ·
                      refine ⟨2730595640169871254143815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58252706990290586755068053 2730595640169871254143815)
                      ·
                        rfl

theorem cell23_5317816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_5317816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317816 prefixEnd_5317816 := by exact prefixLift 5317816
  have htrace : WordTrace (prefixWord ++ tailWord_5317816) baseStart_5317816 baseEnd_5317816 := by
    simpa [prefixWord, tailWord_5317816, baseEnd_5317816] using wordTrace_append hprefix tailTrace_5317816
  have hstable : (prefixWord ++ tailWord_5317816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317816).length < 2 ^ (prefixWord ++ tailWord_5317816).sum := by decide
  have hdescent : baseEnd_5317816 < baseStart_5317816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317893 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_5317893 : Nat := 118140960795 + 5317893 * 2 ^ 59
def prefixEnd_5317893 : Nat := 4983230072969 + 3 ^ 40 * 5317893 * 2
def baseEnd_5317893 : Nat := 2730635178180267452880961

theorem tailTrace_5317893 : CollatzResearch.WordTrace tailWord_5317893 prefixEnd_5317893 2730635178180267452880961 := by
  unfold tailWord_5317893
  simp only [CollatzResearch.WordTrace]
  refine ⟨193959492123189359662118333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129306328082126239774745555 193959492123189359662118333)
  ·
    refine ⟨72734809546196009873294375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193959492123189359662118333 72734809546196009873294375)
    ·
      refine ⟨109102214319294014809941563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72734809546196009873294375 109102214319294014809941563)
      ·
        refine ⟨163653321478941022214912345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109102214319294014809941563 163653321478941022214912345)
        ·
          refine ⟨122739991109205766661184259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163653321478941022214912345 122739991109205766661184259)
          ·
            refine ⟨184109986663808649991776389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122739991109205766661184259 184109986663808649991776389)
            ·
              refine ⟨34520622499464121873458073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184109986663808649991776389 34520622499464121873458073)
              ·
                refine ⟨25890466874598091405093555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34520622499464121873458073 25890466874598091405093555)
                ·
                  refine ⟨38835700311897137107640333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25890466874598091405093555 38835700311897137107640333)
                  ·
                    refine ⟨14563387616961426415365125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38835700311897137107640333 14563387616961426415365125)
                    ·
                      refine ⟨2730635178180267452880961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14563387616961426415365125 2730635178180267452880961)
                      ·
                        rfl

theorem cell23_5317893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_5317893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317893 prefixEnd_5317893 := by exact prefixLift 5317893
  have htrace : WordTrace (prefixWord ++ tailWord_5317893) baseStart_5317893 baseEnd_5317893 := by
    simpa [prefixWord, tailWord_5317893, baseEnd_5317893] using wordTrace_append hprefix tailTrace_5317893
  have hstable : (prefixWord ++ tailWord_5317893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317893).length < 2 ^ (prefixWord ++ tailWord_5317893).sum := by decide
  have hdescent : baseEnd_5317893 < baseStart_5317893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317923 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6]
def baseStart_5317923 : Nat := 118140960795 + 5317923 * 2 ^ 59
def prefixEnd_5317923 : Nat := 4983230072969 + 3 ^ 40 * 5317923 * 2
def baseEnd_5317923 : Nat := 2730650582599902335505823

theorem tailTrace_5317923 : CollatzResearch.WordTrace tailWord_5317923 prefixEnd_5317923 2730650582599902335505823 := by
  unfold tailWord_5317923
  simp only [CollatzResearch.WordTrace]
  refine ⟨193960586313080674785710423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129307057542053783190473615 193960586313080674785710423)
  ·
    refine ⟨290940879469621012178565635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193960586313080674785710423 290940879469621012178565635)
    ·
      refine ⟨436411319204431518267848453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290940879469621012178565635 436411319204431518267848453)
      ·
        refine ⟨81827122350830909675221585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 436411319204431518267848453 81827122350830909675221585)
        ·
          refine ⟨61370341763123182256416189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81827122350830909675221585 61370341763123182256416189)
          ·
            refine ⟨23013878161171193346156071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61370341763123182256416189 23013878161171193346156071)
            ·
              refine ⟨34520817241756790019234107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23013878161171193346156071 34520817241756790019234107)
              ·
                refine ⟨51781225862635185028851161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34520817241756790019234107 51781225862635185028851161)
                ·
                  refine ⟨38835919396976388771638371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51781225862635185028851161 38835919396976388771638371)
                  ·
                    refine ⟨58253879095464583157457557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38835919396976388771638371 58253879095464583157457557)
                    ·
                      refine ⟨2730650582599902335505823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58253879095464583157457557 2730650582599902335505823)
                      ·
                        rfl

theorem cell23_5317923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_5317923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317923 prefixEnd_5317923 := by exact prefixLift 5317923
  have htrace : WordTrace (prefixWord ++ tailWord_5317923) baseStart_5317923 baseEnd_5317923 := by
    simpa [prefixWord, tailWord_5317923, baseEnd_5317923] using wordTrace_append hprefix tailTrace_5317923
  have hstable : (prefixWord ++ tailWord_5317923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317923).length < 2 ^ (prefixWord ++ tailWord_5317923).sum := by decide
  have hdescent : baseEnd_5317923 < baseStart_5317923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317937 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 3, 4]
def baseStart_5317937 : Nat := 118140960795 + 5317937 * 2 ^ 59
def prefixEnd_5317937 : Nat := 4983230072969 + 3 ^ 40 * 5317937 * 2
def baseEnd_5317937 : Nat := 910219257109688426910253

theorem tailTrace_5317937 : CollatzResearch.WordTrace tailWord_5317937 prefixEnd_5317937 910219257109688426910253 := by
  unfold tailWord_5317937
  simp only [CollatzResearch.WordTrace]
  refine ⟨193961096935029955176720065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129307397956686636784480043 193961096935029955176720065)
  ·
    refine ⟨145470822701272466382540049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193961096935029955176720065 145470822701272466382540049)
    ·
      refine ⟨109103117025954349786905037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145470822701272466382540049 109103117025954349786905037)
      ·
        refine ⟨40913668884732881170089389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109103117025954349786905037 40913668884732881170089389)
        ·
          refine ⟨15342625831774830438783521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40913668884732881170089389 15342625831774830438783521)
          ·
            refine ⟨11506969373831122829087641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15342625831774830438783521 11506969373831122829087641)
            ·
              refine ⟨8630227030373342121815731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11506969373831122829087641 8630227030373342121815731)
              ·
                refine ⟨12945340545560013182723597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8630227030373342121815731 12945340545560013182723597)
                ·
                  refine ⟨4854502704585004943521349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12945340545560013182723597 4854502704585004943521349)
                  ·
                    refine ⟨910219257109688426910253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4854502704585004943521349 910219257109688426910253)
                    ·
                      rfl

theorem cell23_5317937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_5317937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317937 prefixEnd_5317937 := by exact prefixLift 5317937
  have htrace : WordTrace (prefixWord ++ tailWord_5317937) baseStart_5317937 baseEnd_5317937 := by
    simpa [prefixWord, tailWord_5317937, baseEnd_5317937] using wordTrace_append hprefix tailTrace_5317937
  have hstable : (prefixWord ++ tailWord_5317937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317937).length < 2 ^ (prefixWord ++ tailWord_5317937).sum := by decide
  have hdescent : baseEnd_5317937 < baseStart_5317937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317940 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5317940 : Nat := 118140960795 + 5317940 * 2 ^ 59
def prefixEnd_5317940 : Nat := 4983230072969 + 3 ^ 40 * 5317940 * 2
def baseEnd_5317940 : Nat := 2730659311771028768993245

theorem tailTrace_5317940 : CollatzResearch.WordTrace tailWord_5317940 prefixEnd_5317940 2730659311771028768993245 := by
  unfold tailWord_5317940
  simp only [CollatzResearch.WordTrace]
  refine ⟨96980603177009543344539637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129307470902679391126052849 96980603177009543344539637)
  ·
    refine ⟨9091931547844644688550591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96980603177009543344539637 9091931547844644688550591)
    ·
      refine ⟨13637897321766967032825887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9091931547844644688550591 13637897321766967032825887)
      ·
        refine ⟨20456845982650450549238831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637897321766967032825887 20456845982650450549238831)
        ·
          refine ⟨30685268973975675823858247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20456845982650450549238831 30685268973975675823858247)
          ·
            refine ⟨46027903460963513735787371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30685268973975675823858247 46027903460963513735787371)
            ·
              refine ⟨69041855191445270603681057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46027903460963513735787371 69041855191445270603681057)
              ·
                refine ⟨51781391393583952952760793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69041855191445270603681057 51781391393583952952760793)
                ·
                  refine ⟨38836043545187964714570595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51781391393583952952760793 38836043545187964714570595)
                  ·
                    refine ⟨58254065317781947071855893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38836043545187964714570595 58254065317781947071855893)
                    ·
                      refine ⟨2730659311771028768993245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58254065317781947071855893 2730659311771028768993245)
                      ·
                        rfl

theorem cell23_5317940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5317940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317940 prefixEnd_5317940 := by exact prefixLift 5317940
  have htrace : WordTrace (prefixWord ++ tailWord_5317940) baseStart_5317940 baseEnd_5317940 := by
    simpa [prefixWord, tailWord_5317940, baseEnd_5317940] using wordTrace_append hprefix tailTrace_5317940
  have hstable : (prefixWord ++ tailWord_5317940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317940).length < 2 ^ (prefixWord ++ tailWord_5317940).sum := by decide
  have hdescent : baseEnd_5317940 < baseStart_5317940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317963 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 7, 5]
def baseStart_5317963 : Nat := 118140960795 + 5317963 * 2 ^ 59
def prefixEnd_5317963 : Nat := 4983230072969 + 3 ^ 40 * 5317963 * 2
def baseEnd_5317963 : Nat := 910223707275360726335213

theorem tailTrace_5317963 : CollatzResearch.WordTrace tailWord_5317963 prefixEnd_5317963 910223707275360726335213 := by
  unfold tailWord_5317963
  simp only [CollatzResearch.WordTrace]
  refine ⟨193962045232935761617166543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129308030155290507744777695 193962045232935761617166543)
  ·
    refine ⟨290943067849403642425749815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193962045232935761617166543 290943067849403642425749815)
    ·
      refine ⟨436414601774105463638624723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290943067849403642425749815 436414601774105463638624723)
      ·
        refine ⟨654621902661158195457937085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436414601774105463638624723 654621902661158195457937085)
        ·
          refine ⟨245483213497934323296726407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 654621902661158195457937085 245483213497934323296726407)
          ·
            refine ⟨368224820246901484945089611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245483213497934323296726407 368224820246901484945089611)
            ·
              refine ⟨552337230370352227417634417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368224820246901484945089611 552337230370352227417634417)
              ·
                refine ⟨414252922777764170563225813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552337230370352227417634417 414252922777764170563225813)
                ·
                  refine ⟨9709052877603847747575605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 414252922777764170563225813 9709052877603847747575605)
                  ·
                    refine ⟨910223707275360726335213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9709052877603847747575605 910223707275360726335213)
                    ·
                      rfl

theorem cell23_5317963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 5].length) (baseStart_5317963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317963 prefixEnd_5317963 := by exact prefixLift 5317963
  have htrace : WordTrace (prefixWord ++ tailWord_5317963) baseStart_5317963 baseEnd_5317963 := by
    simpa [prefixWord, tailWord_5317963, baseEnd_5317963] using wordTrace_append hprefix tailTrace_5317963
  have hstable : (prefixWord ++ tailWord_5317963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317963).length < 2 ^ (prefixWord ++ tailWord_5317963).sum := by decide
  have hdescent : baseEnd_5317963 < baseStart_5317963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317987 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 4, 3, 2]
def baseStart_5317987 : Nat := 118140960795 + 5317987 * 2 ^ 59
def prefixEnd_5317987 : Nat := 4983230072969 + 3 ^ 40 * 5317987 * 2
def baseEnd_5317987 : Nat := 2730683445361790085105529

theorem tailTrace_5317987 : CollatzResearch.WordTrace tailWord_5317987 prefixEnd_5317987 2730683445361790085105529 := by
  unfold tailWord_5317987
  simp only [CollatzResearch.WordTrace]
  refine ⟨193962920584848813716040215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129308613723232542477360143 193962920584848813716040215)
  ·
    refine ⟨290944380877273220574060323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193962920584848813716040215 290944380877273220574060323)
    ·
      refine ⟨436416571315909830861090485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290944380877273220574060323 436416571315909830861090485)
      ·
        refine ⟨40914053560866546643227233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 436416571315909830861090485 40914053560866546643227233)
        ·
          refine ⟨30685540170649909982420425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40914053560866546643227233 30685540170649909982420425)
          ·
            refine ⟨23014155127987432486815319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30685540170649909982420425 23014155127987432486815319)
            ·
              refine ⟨34521232691981148730222979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23014155127987432486815319 34521232691981148730222979)
              ·
                refine ⟨51781849037971723095334469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34521232691981148730222979 51781849037971723095334469)
                ·
                  refine ⟨9709096694619698080375213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51781849037971723095334469 9709096694619698080375213)
                  ·
                    refine ⟨3640911260482386780140705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9709096694619698080375213 3640911260482386780140705)
                    ·
                      refine ⟨2730683445361790085105529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640911260482386780140705 2730683445361790085105529)
                      ·
                        rfl

theorem cell23_5317987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_5317987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317987 prefixEnd_5317987 := by exact prefixLift 5317987
  have htrace : WordTrace (prefixWord ++ tailWord_5317987) baseStart_5317987 baseEnd_5317987 := by
    simpa [prefixWord, tailWord_5317987, baseEnd_5317987] using wordTrace_append hprefix tailTrace_5317987
  have hstable : (prefixWord ++ tailWord_5317987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317987).length < 2 ^ (prefixWord ++ tailWord_5317987).sum := by decide
  have hdescent : baseEnd_5317987 < baseStart_5317987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5317993 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_5317993 : Nat := 118140960795 + 5317993 * 2 ^ 59
def prefixEnd_5317993 : Nat := 4983230072969 + 3 ^ 40 * 5317993 * 2
def baseEnd_5317993 : Nat := 910228842081905687210167

theorem tailTrace_5317993 : CollatzResearch.WordTrace tailWord_5317993 prefixEnd_5317993 910228842081905687210167 := by
  unfold tailWord_5317993
  simp only [CollatzResearch.WordTrace]
  refine ⟨193963139422827076740758633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129308759615218051160505755 193963139422827076740758633)
  ·
    refine ⟨145472354567120307555568975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193963139422827076740758633 145472354567120307555568975)
    ·
      refine ⟨218208531850680461333353463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145472354567120307555568975 218208531850680461333353463)
      ·
        refine ⟨327312797776020692000030195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218208531850680461333353463 327312797776020692000030195)
        ·
          refine ⟨490969196664031038000045293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327312797776020692000030195 490969196664031038000045293)
          ·
            refine ⟨184113448749011639250016985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 490969196664031038000045293 184113448749011639250016985)
            ·
              refine ⟨138085086561758729437512739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184113448749011639250016985 138085086561758729437512739)
              ·
                refine ⟨207127629842638094156269109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138085086561758729437512739 207127629842638094156269109)
                ·
                  refine ⟨19418215297747321327150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207127629842638094156269109 19418215297747321327150229)
                  ·
                    refine ⟨910228842081905687210167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19418215297747321327150229 910228842081905687210167)
                    ·
                      rfl

theorem cell23_5317993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_5317993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5317993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5317993 prefixEnd_5317993 := by exact prefixLift 5317993
  have htrace : WordTrace (prefixWord ++ tailWord_5317993) baseStart_5317993 baseEnd_5317993 := by
    simpa [prefixWord, tailWord_5317993, baseEnd_5317993] using wordTrace_append hprefix tailTrace_5317993
  have hstable : (prefixWord ++ tailWord_5317993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5317993).length < 2 ^ (prefixWord ++ tailWord_5317993).sum := by decide
  have hdescent : baseEnd_5317993 < baseStart_5317993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5317993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318000 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_5318000 : Nat := 118140960795 + 5318000 * 2 ^ 59
def prefixEnd_5318000 : Nat := 4983230072969 + 3 ^ 40 * 5318000 * 2
def baseEnd_5318000 : Nat := 2730690120610298534242969

theorem tailTrace_5318000 : CollatzResearch.WordTrace tailWord_5318000 prefixEnd_5318000 2730690120610298534242969 := by
  unfold tailWord_5318000
  simp only [CollatzResearch.WordTrace]
  refine ⟨96981697366900858468131727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129308929822534477957508969 96981697366900858468131727)
  ·
    refine ⟨145472546050351287702197591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96981697366900858468131727 145472546050351287702197591)
    ·
      refine ⟨218208819075526931553296387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145472546050351287702197591 218208819075526931553296387)
      ·
        refine ⟨327313228613290397329944581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218208819075526931553296387 327313228613290397329944581)
        ·
          refine ⟨61371230364991949499364609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327313228613290397329944581 61371230364991949499364609)
          ·
            refine ⟨46028422773743962124523457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61371230364991949499364609 46028422773743962124523457)
            ·
              refine ⟨34521317080307971593392593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46028422773743962124523457 34521317080307971593392593)
              ·
                refine ⟨25890987810230978695044445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34521317080307971593392593 25890987810230978695044445)
                ·
                  refine ⟨9709120428836617010641667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25890987810230978695044445 9709120428836617010641667)
                  ·
                    refine ⟨14563680643254925515962501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9709120428836617010641667 14563680643254925515962501)
                    ·
                      refine ⟨2730690120610298534242969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14563680643254925515962501 2730690120610298534242969)
                      ·
                        rfl

theorem cell23_5318000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_5318000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318000 prefixEnd_5318000 := by exact prefixLift 5318000
  have htrace : WordTrace (prefixWord ++ tailWord_5318000) baseStart_5318000 baseEnd_5318000 := by
    simpa [prefixWord, tailWord_5318000, baseEnd_5318000] using wordTrace_append hprefix tailTrace_5318000
  have hstable : (prefixWord ++ tailWord_5318000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318000).length < 2 ^ (prefixWord ++ tailWord_5318000).sum := by decide
  have hdescent : baseEnd_5318000 < baseStart_5318000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318037 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_5318037 : Nat := 118140960795 + 5318037 * 2 ^ 59
def prefixEnd_5318037 : Nat := 4983230072969 + 3 ^ 40 * 5318037 * 2
def baseEnd_5318037 : Nat := 2730709119394514889480299

theorem tailTrace_5318037 : CollatzResearch.WordTrace tailWord_5318037 prefixEnd_5318037 2730709119394514889480299 := by
  unfold tailWord_5318037
  simp only [CollatzResearch.WordTrace]
  refine ⟨193964744234667672255360365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129309829489778448170240243 193964744234667672255360365)
  ·
    refine ⟨72736779088000377095760137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193964744234667672255360365 72736779088000377095760137)
    ·
      refine ⟨54552584316000282821820103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72736779088000377095760137 54552584316000282821820103)
      ·
        refine ⟨81828876474000424232730155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54552584316000282821820103 81828876474000424232730155)
        ·
          refine ⟨122743314711000636349095233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81828876474000424232730155 122743314711000636349095233)
          ·
            refine ⟨92057486033250477261821425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122743314711000636349095233 92057486033250477261821425)
            ·
              refine ⟨69043114524937857946366069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92057486033250477261821425 69043114524937857946366069)
              ·
                refine ⟨6472791986712924182471819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69043114524937857946366069 6472791986712924182471819)
                ·
                  refine ⟨9709187980069386273707729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472791986712924182471819 9709187980069386273707729)
                  ·
                    refine ⟨7281890985052039705280797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9709187980069386273707729 7281890985052039705280797)
                    ·
                      refine ⟨2730709119394514889480299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7281890985052039705280797 2730709119394514889480299)
                      ·
                        rfl

theorem cell23_5318037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_5318037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318037 prefixEnd_5318037 := by exact prefixLift 5318037
  have htrace : WordTrace (prefixWord ++ tailWord_5318037) baseStart_5318037 baseEnd_5318037 := by
    simpa [prefixWord, tailWord_5318037, baseEnd_5318037] using wordTrace_append hprefix tailTrace_5318037
  have hstable : (prefixWord ++ tailWord_5318037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318037).length < 2 ^ (prefixWord ++ tailWord_5318037).sum := by decide
  have hdescent : baseEnd_5318037 < baseStart_5318037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318040 : List Nat := [2, 1, 2, 5, 2, 11]
def baseStart_5318040 : Nat := 118140960795 + 5318040 * 2 ^ 59
def prefixEnd_5318040 : Nat := 4983230072969 + 3 ^ 40 * 5318040 * 2
def baseEnd_5318040 : Nat := 11237492427310610607995

theorem tailTrace_5318040 : CollatzResearch.WordTrace tailWord_5318040 prefixEnd_5318040 11237492427310610607995 := by
  unfold tailWord_5318040
  simp only [CollatzResearch.WordTrace]
  refine ⟨96982426826828401883859787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129309902435771202511813049 96982426826828401883859787)
  ·
    refine ⟨145473640240242602825789681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96982426826828401883859787 145473640240242602825789681)
    ·
      refine ⟨109105230180181952119342261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145473640240242602825789681 109105230180181952119342261)
      ·
        refine ⟨10228615329392058011188337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109105230180181952119342261 10228615329392058011188337)
        ·
          refine ⟨7671461497044043508391253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10228615329392058011188337 7671461497044043508391253)
          ·
            refine ⟨11237492427310610607995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7671461497044043508391253 11237492427310610607995)
            ·
              rfl

theorem cell23_5318040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 11].length) (baseStart_5318040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318040 prefixEnd_5318040 := by exact prefixLift 5318040
  have htrace : WordTrace (prefixWord ++ tailWord_5318040) baseStart_5318040 baseEnd_5318040 := by
    simpa [prefixWord, tailWord_5318040, baseEnd_5318040] using wordTrace_append hprefix tailTrace_5318040
  have hstable : (prefixWord ++ tailWord_5318040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318040).length < 2 ^ (prefixWord ++ tailWord_5318040).sum := by decide
  have hdescent : baseEnd_5318040 < baseStart_5318040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318051 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 1, 2, 2]
def baseStart_5318051 : Nat := 118140960795 + 5318051 * 2 ^ 59
def prefixEnd_5318051 : Nat := 4983230072969 + 3 ^ 40 * 5318051 * 2
def baseEnd_5318051 : Nat := 2730716308123677834705235

theorem tailTrace_5318051 : CollatzResearch.WordTrace tailWord_5318051 prefixEnd_5318051 2730716308123677834705235 := by
  unfold tailWord_5318051
  simp only [CollatzResearch.WordTrace]
  refine ⟨193965254856616952646370007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129310169904411301764246671 193965254856616952646370007)
  ·
    refine ⟨290947882284925428969555011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193965254856616952646370007 290947882284925428969555011)
    ·
      refine ⟨436421823427388143454332517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290947882284925428969555011 436421823427388143454332517)
      ·
        refine ⟨81829091892635276897687347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 436421823427388143454332517 81829091892635276897687347)
        ·
          refine ⟨122743637838952915346531021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81829091892635276897687347 122743637838952915346531021)
          ·
            refine ⟨46028864189607343254949133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122743637838952915346531021 46028864189607343254949133)
            ·
              refine ⟨17260824071102753720605925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46028864189607343254949133 17260824071102753720605925)
              ·
                refine ⟨3236404513331766322613611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17260824071102753720605925 3236404513331766322613611)
                ·
                  refine ⟨4854606769997649483920417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236404513331766322613611 4854606769997649483920417)
                  ·
                    refine ⟨3640955077498237112940313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4854606769997649483920417 3640955077498237112940313)
                    ·
                      refine ⟨2730716308123677834705235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3640955077498237112940313 2730716308123677834705235)
                      ·
                        rfl

theorem cell23_5318051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_5318051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318051 prefixEnd_5318051 := by exact prefixLift 5318051
  have htrace : WordTrace (prefixWord ++ tailWord_5318051) baseStart_5318051 baseEnd_5318051 := by
    simpa [prefixWord, tailWord_5318051, baseEnd_5318051] using wordTrace_append hprefix tailTrace_5318051
  have hstable : (prefixWord ++ tailWord_5318051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318051).length < 2 ^ (prefixWord ++ tailWord_5318051).sum := by decide
  have hdescent : baseEnd_5318051 < baseStart_5318051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318082 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5318082 : Nat := 118140960795 + 5318082 * 2 ^ 59
def prefixEnd_5318082 : Nat := 4983230072969 + 3 ^ 40 * 5318082 * 2
def baseEnd_5318082 : Nat := 910244075341322404472531

theorem tailTrace_5318082 : CollatzResearch.WordTrace tailWord_5318082 prefixEnd_5318082 910244075341322404472531 := by
  unfold tailWord_5318082
  simp only [CollatzResearch.WordTrace]
  refine ⟨48491596379876161235187125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129310923679669763293832333 48491596379876161235187125)
  ·
    refine ⟨4546087160613390115798793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48491596379876161235187125 4546087160613390115798793)
    ·
      refine ⟨3409565370460042586849095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4546087160613390115798793 3409565370460042586849095)
      ·
        refine ⟨5114348055690063880273643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409565370460042586849095 5114348055690063880273643)
        ·
          refine ⟨7671522083535095820410465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5114348055690063880273643 7671522083535095820410465)
          ·
            refine ⟨5753641562651321865307849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7671522083535095820410465 5753641562651321865307849)
            ·
              refine ⟨4315231171988491398980887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5753641562651321865307849 4315231171988491398980887)
              ·
                refine ⟨6472846757982737098471331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315231171988491398980887 6472846757982737098471331)
                ·
                  refine ⟨9709270136974105647706997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472846757982737098471331 9709270136974105647706997)
                  ·
                    refine ⟨910244075341322404472531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9709270136974105647706997 910244075341322404472531)
                    ·
                      rfl

theorem cell23_5318082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5318082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318082 prefixEnd_5318082 := by exact prefixLift 5318082
  have htrace : WordTrace (prefixWord ++ tailWord_5318082) baseStart_5318082 baseEnd_5318082 := by
    simpa [prefixWord, tailWord_5318082, baseEnd_5318082] using wordTrace_append hprefix tailTrace_5318082
  have hstable : (prefixWord ++ tailWord_5318082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318082).length < 2 ^ (prefixWord ++ tailWord_5318082).sum := by decide
  have hdescent : baseEnd_5318082 < baseStart_5318082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318084 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5318084 : Nat := 118140960795 + 5318084 * 2 ^ 59
def prefixEnd_5318084 : Nat := 4983230072969 + 3 ^ 40 * 5318084 * 2
def baseEnd_5318084 : Nat := 2730733252985276205592583

theorem tailTrace_5318084 : CollatzResearch.WordTrace tailWord_5318084 prefixEnd_5318084 2730733252985276205592583 := by
  unfold tailWord_5318084
  simp only [CollatzResearch.WordTrace]
  refine ⟨96983229232748699641160653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129310972310331599521547537 96983229232748699641160653)
  ·
    refine ⟨36368710962280762365435245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96983229232748699641160653 36368710962280762365435245)
    ·
      refine ⟨13638266610855285887038217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36368710962280762365435245 13638266610855285887038217)
      ·
        refine ⟨10228699958141464415278663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13638266610855285887038217 10228699958141464415278663)
        ·
          refine ⟨15343049937212196622917995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10228699958141464415278663 15343049937212196622917995)
          ·
            refine ⟨23014574905818294934376993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15343049937212196622917995 23014574905818294934376993)
            ·
              refine ⟨17260931179363721200782745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23014574905818294934376993 17260931179363721200782745)
              ·
                refine ⟨12945698384522790900587059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17260931179363721200782745 12945698384522790900587059)
                ·
                  refine ⟨19418547576784186350880589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12945698384522790900587059 19418547576784186350880589)
                  ·
                    refine ⟨7281955341294069881580221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19418547576784186350880589 7281955341294069881580221)
                    ·
                      refine ⟨2730733252985276205592583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7281955341294069881580221 2730733252985276205592583)
                      ·
                        rfl

theorem cell23_5318084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5318084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318084 prefixEnd_5318084 := by exact prefixLift 5318084
  have htrace : WordTrace (prefixWord ++ tailWord_5318084) baseStart_5318084 baseEnd_5318084 := by
    simpa [prefixWord, tailWord_5318084, baseEnd_5318084] using wordTrace_append hprefix tailTrace_5318084
  have hstable : (prefixWord ++ tailWord_5318084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318084).length < 2 ^ (prefixWord ++ tailWord_5318084).sum := by decide
  have hdescent : baseEnd_5318084 < baseStart_5318084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318117 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_5318117 : Nat := 118140960795 + 5318117 * 2 ^ 59
def prefixEnd_5318117 : Nat := 4983230072969 + 3 ^ 40 * 5318117 * 2
def baseEnd_5318117 : Nat := 910250065948958192159977

theorem tailTrace_5318117 : CollatzResearch.WordTrace tailWord_5318117 prefixEnd_5318117 910250065948958192159977 := by
  unfold tailWord_5318117
  simp only [CollatzResearch.WordTrace]
  refine ⟨193967662074377845918272605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129311774716251897278848403 193967662074377845918272605)
  ·
    refine ⟨72737873277891692219352227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193967662074377845918272605 72737873277891692219352227)
    ·
      refine ⟨109106809916837538329028341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72737873277891692219352227 109106809916837538329028341)
      ·
        refine ⟨10228763429703519218346407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109106809916837538329028341 10228763429703519218346407)
        ·
          refine ⟨15343145144555278827519611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10228763429703519218346407 15343145144555278827519611)
          ·
            refine ⟨23014717716832918241279417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15343145144555278827519611 23014717716832918241279417)
            ·
              refine ⟨17261038287624688680959563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23014717716832918241279417 17261038287624688680959563)
              ·
                refine ⟨25891557431437033021439345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17261038287624688680959563 25891557431437033021439345)
                ·
                  refine ⟨19418668073577774766079509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25891557431437033021439345 19418668073577774766079509)
                  ·
                    refine ⟨910250065948958192159977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19418668073577774766079509 910250065948958192159977)
                    ·
                      rfl

theorem cell23_5318117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_5318117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318117 prefixEnd_5318117 := by exact prefixLift 5318117
  have htrace : WordTrace (prefixWord ++ tailWord_5318117) baseStart_5318117 baseEnd_5318117 := by
    simpa [prefixWord, tailWord_5318117, baseEnd_5318117] using wordTrace_append hprefix tailTrace_5318117
  have hstable : (prefixWord ++ tailWord_5318117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318117).length < 2 ^ (prefixWord ++ tailWord_5318117).sum := by decide
  have hdescent : baseEnd_5318117 < baseStart_5318117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318147 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 5]
def baseStart_5318147 : Nat := 118140960795 + 5318147 * 2 ^ 59
def prefixEnd_5318147 : Nat := 4983230072969 + 3 ^ 40 * 5318147 * 2
def baseEnd_5318147 : Nat := 303418400251834384344977

theorem tailTrace_5318147 : CollatzResearch.WordTrace tailWord_5318147 prefixEnd_5318147 303418400251834384344977 := by
  unfold tailWord_5318147
  simp only [CollatzResearch.WordTrace]
  refine ⟨193968756264269161041864695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129312504176179440694576463 193968756264269161041864695)
  ·
    refine ⟨290953134396403741562797043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193968756264269161041864695 290953134396403741562797043)
    ·
      refine ⟨436429701594605612344195565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290953134396403741562797043 436429701594605612344195565)
      ·
        refine ⟨163661138097977104629073337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436429701594605612344195565 163661138097977104629073337)
        ·
          refine ⟨122745853573482828471805003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163661138097977104629073337 122745853573482828471805003)
          ·
            refine ⟨184118780360224242707707505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122745853573482828471805003 184118780360224242707707505)
            ·
              refine ⟨138089085270168182030780629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184118780360224242707707505 138089085270168182030780629)
              ·
                refine ⟨3236462936019566766346421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138089085270168182030780629 3236462936019566766346421)
                ·
                  refine ⟨303418400251834384344977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3236462936019566766346421 303418400251834384344977)
                  ·
                    rfl

theorem cell23_5318147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 5].length) (baseStart_5318147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318147 prefixEnd_5318147 := by exact prefixLift 5318147
  have htrace : WordTrace (prefixWord ++ tailWord_5318147) baseStart_5318147 baseEnd_5318147 := by
    simpa [prefixWord, tailWord_5318147, baseEnd_5318147] using wordTrace_append hprefix tailTrace_5318147
  have hstable : (prefixWord ++ tailWord_5318147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318147).length < 2 ^ (prefixWord ++ tailWord_5318147).sum := by decide
  have hdescent : baseEnd_5318147 < baseStart_5318147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318258 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_5318258 : Nat := 118140960795 + 5318258 * 2 ^ 59
def prefixEnd_5318258 : Nat := 4983230072969 + 3 ^ 40 * 5318258 * 2
def baseEnd_5318258 : Nat := 910274199539719508272261

theorem tailTrace_5318258 : CollatzResearch.WordTrace tailWord_5318258 prefixEnd_5318258 910274199539719508272261 := by
  unfold tailWord_5318258
  simp only [CollatzResearch.WordTrace]
  refine ⟨48493201191716756749788857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129315203177911351332770285 48493201191716756749788857)
  ·
    refine ⟨36369900893787567562341643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48493201191716756749788857 36369900893787567562341643)
    ·
      refine ⟨54554851340681351343512465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36369900893787567562341643 54554851340681351343512465)
      ·
        refine ⟨40916138505511013507634349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54554851340681351343512465 40916138505511013507634349)
        ·
          refine ⟨15343551939566630065362881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40916138505511013507634349 15343551939566630065362881)
          ·
            refine ⟨11507663954674972549022161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15343551939566630065362881 11507663954674972549022161)
            ·
              refine ⟨8630747966006229411766621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11507663954674972549022161 8630747966006229411766621)
              ·
                refine ⟨3236530487252336029412483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8630747966006229411766621 3236530487252336029412483)
                ·
                  refine ⟨4854795730878504044118725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236530487252336029412483 4854795730878504044118725)
                  ·
                    refine ⟨910274199539719508272261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4854795730878504044118725 910274199539719508272261)
                    ·
                      rfl

theorem cell23_5318258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_5318258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318258 prefixEnd_5318258 := by exact prefixLift 5318258
  have htrace : WordTrace (prefixWord ++ tailWord_5318258) baseStart_5318258 baseEnd_5318258 := by
    simpa [prefixWord, tailWord_5318258, baseEnd_5318258] using wordTrace_append hprefix tailTrace_5318258
  have hstable : (prefixWord ++ tailWord_5318258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318258).length < 2 ^ (prefixWord ++ tailWord_5318258).sum := by decide
  have hdescent : baseEnd_5318258 < baseStart_5318258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318297 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_5318297 : Nat := 118140960795 + 5318297 * 2 ^ 59
def prefixEnd_5318297 : Nat := 4983230072969 + 3 ^ 40 * 5318297 * 2
def baseEnd_5318297 : Nat := 910280874788227957409701

theorem tailTrace_5318297 : CollatzResearch.WordTrace tailWord_5318297 prefixEnd_5318297 910280874788227957409701 := by
  unfold tailWord_5318297
  simp only [CollatzResearch.WordTrace]
  refine ⟨193974227213725736659825145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129316151475817157773216763 193974227213725736659825145)
  ·
    refine ⟨145480670410294302494868859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193974227213725736659825145 145480670410294302494868859)
    ·
      refine ⟨218221005615441453742303289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145480670410294302494868859 218221005615441453742303289)
      ·
        refine ⟨163665754211581090306727467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218221005615441453742303289 163665754211581090306727467)
        ·
          refine ⟨245498631317371635460091201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163665754211581090306727467 245498631317371635460091201)
          ·
            refine ⟨184123973488028726595068401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245498631317371635460091201 184123973488028726595068401)
            ·
              refine ⟨138092980116021544946301301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184123973488028726595068401 138092980116021544946301301)
              ·
                refine ⟨12946216885877019838715747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138092980116021544946301301 12946216885877019838715747)
                ·
                  refine ⟨19419325328815529758073621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12946216885877019838715747 19419325328815529758073621)
                  ·
                    refine ⟨910280874788227957409701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19419325328815529758073621 910280874788227957409701)
                    ·
                      rfl

theorem cell23_5318297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_5318297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318297 prefixEnd_5318297 := by exact prefixLift 5318297
  have htrace : WordTrace (prefixWord ++ tailWord_5318297) baseStart_5318297 baseEnd_5318297 := by
    simpa [prefixWord, tailWord_5318297, baseEnd_5318297] using wordTrace_append hprefix tailTrace_5318297
  have hstable : (prefixWord ++ tailWord_5318297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318297).length < 2 ^ (prefixWord ++ tailWord_5318297).sum := by decide
  have hdescent : baseEnd_5318297 < baseStart_5318297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318307 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5]
def baseStart_5318307 : Nat := 118140960795 + 5318307 * 2 ^ 59
def prefixEnd_5318307 : Nat := 4983230072969 + 3 ^ 40 * 5318307 * 2
def baseEnd_5318307 : Nat := 2730847759171228833104057

theorem tailTrace_5318307 : CollatzResearch.WordTrace tailWord_5318307 prefixEnd_5318307 2730847759171228833104057 := by
  unfold tailWord_5318307
  simp only [CollatzResearch.WordTrace]
  refine ⟨193974591943689508367689175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129316394629126338911792783 193974591943689508367689175)
  ·
    refine ⟨290961887915534262551533763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193974591943689508367689175 290961887915534262551533763)
    ·
      refine ⟨436442831873301393827300645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290961887915534262551533763 436442831873301393827300645)
      ·
        refine ⟨81833030976244011342618871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 436442831873301393827300645 81833030976244011342618871)
        ·
          refine ⟨122749546464366017013928307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81833030976244011342618871 122749546464366017013928307)
          ·
            refine ⟨184124319696549025520892461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122749546464366017013928307 184124319696549025520892461)
            ·
              refine ⟨69046619886205884570334673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184124319696549025520892461 69046619886205884570334673)
              ·
                refine ⟨51784964914654413427751005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69046619886205884570334673 51784964914654413427751005)
                ·
                  refine ⟨19419361842995405035406627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51784964914654413427751005 19419361842995405035406627)
                  ·
                    refine ⟨29129042764493107553109941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19419361842995405035406627 29129042764493107553109941)
                    ·
                      refine ⟨2730847759171228833104057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29129042764493107553109941 2730847759171228833104057)
                      ·
                        rfl

theorem cell23_5318307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_5318307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318307 prefixEnd_5318307 := by exact prefixLift 5318307
  have htrace : WordTrace (prefixWord ++ tailWord_5318307) baseStart_5318307 baseEnd_5318307 := by
    simpa [prefixWord, tailWord_5318307, baseEnd_5318307] using wordTrace_append hprefix tailTrace_5318307
  have hstable : (prefixWord ++ tailWord_5318307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318307).length < 2 ^ (prefixWord ++ tailWord_5318307).sum := by decide
  have hdescent : baseEnd_5318307 < baseStart_5318307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318327 : List Nat := [1, 1, 3, 1, 5, 1, 11]
def baseStart_5318327 : Nat := 118140960795 + 5318327 * 2 ^ 59
def prefixEnd_5318327 : Nat := 4983230072969 + 3 ^ 40 * 5318327 * 2
def baseEnd_5318327 : Nat := 33714296651658256232765

theorem tailTrace_5318327 : CollatzResearch.WordTrace tailWord_5318327 prefixEnd_5318327 33714296651658256232765 := by
  unfold tailWord_5318327
  simp only [CollatzResearch.WordTrace]
  refine ⟨193975321403617051783417235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129316880935744701188944823 193975321403617051783417235)
  ·
    refine ⟨290962982105425577675125853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193975321403617051783417235 290962982105425577675125853)
    ·
      refine ⟨109111118289534591628172195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290962982105425577675125853 109111118289534591628172195)
      ·
        refine ⟨163666677434301887442258293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109111118289534591628172195 163666677434301887442258293)
        ·
          refine ⟨15343751009465801947711715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163666677434301887442258293 15343751009465801947711715)
          ·
            refine ⟨23015626514198702921567573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15343751009465801947711715 23015626514198702921567573)
            ·
              refine ⟨33714296651658256232765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23015626514198702921567573 33714296651658256232765)
              ·
                rfl

theorem cell23_5318327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 11].length) (baseStart_5318327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318327 prefixEnd_5318327 := by exact prefixLift 5318327
  have htrace : WordTrace (prefixWord ++ tailWord_5318327) baseStart_5318327 baseEnd_5318327 := by
    simpa [prefixWord, tailWord_5318327, baseEnd_5318327] using wordTrace_append hprefix tailTrace_5318327
  have hstable : (prefixWord ++ tailWord_5318327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318327).length < 2 ^ (prefixWord ++ tailWord_5318327).sum := by decide
  have hdescent : baseEnd_5318327 < baseStart_5318327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318334 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_5318334 : Nat := 118140960795 + 5318334 * 2 ^ 59
def prefixEnd_5318334 : Nat := 4983230072969 + 3 ^ 40 * 5318334 * 2
def baseEnd_5318334 : Nat := 2730861623148900227466433

theorem tailTrace_5318334 : CollatzResearch.WordTrace tailWord_5318334 prefixEnd_5318334 2730861623148900227466433 := by
  unfold tailWord_5318334
  simp only [CollatzResearch.WordTrace]
  refine ⟨24246947089323961497365257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129317051143061127985948037 24246947089323961497365257)
  ·
    refine ⟨18185210316992971123023943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24246947089323961497365257 18185210316992971123023943)
    ·
      refine ⟨27277815475489456684535915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18185210316992971123023943 27277815475489456684535915)
      ·
        refine ⟨40916723213234185026803873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27277815475489456684535915 40916723213234185026803873)
        ·
          refine ⟨30687542409925638770102905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40916723213234185026803873 30687542409925638770102905)
          ·
            refine ⟨23015656807444229077577179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30687542409925638770102905 23015656807444229077577179)
            ·
              refine ⟨34523485211166343616365769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23015656807444229077577179 34523485211166343616365769)
              ·
                refine ⟨25892613908374757712274327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34523485211166343616365769 25892613908374757712274327)
                ·
                  refine ⟨38838920862562136568411491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25892613908374757712274327 38838920862562136568411491)
                  ·
                    refine ⟨58258381293843204852617237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38838920862562136568411491 58258381293843204852617237)
                    ·
                      refine ⟨2730861623148900227466433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58258381293843204852617237 2730861623148900227466433)
                      ·
                        rfl

theorem cell23_5318334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_5318334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318334 prefixEnd_5318334 := by exact prefixLift 5318334
  have htrace : WordTrace (prefixWord ++ tailWord_5318334) baseStart_5318334 baseEnd_5318334 := by
    simpa [prefixWord, tailWord_5318334, baseEnd_5318334] using wordTrace_append hprefix tailTrace_5318334
  have hstable : (prefixWord ++ tailWord_5318334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318334).length < 2 ^ (prefixWord ++ tailWord_5318334).sum := by decide
  have hdescent : baseEnd_5318334 < baseStart_5318334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318348 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_5318348 : Nat := 118140960795 + 5318348 * 2 ^ 59
def prefixEnd_5318348 : Nat := 4983230072969 + 3 ^ 40 * 5318348 * 2
def baseEnd_5318348 : Nat := 910289603959354390897123

theorem tailTrace_5318348 : CollatzResearch.WordTrace tailWord_5318348 prefixEnd_5318348 910289603959354390897123 := by
  unfold tailWord_5318348
  simp only [CollatzResearch.WordTrace]
  refine ⟨96988043668270486184965849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129317391557693981579954465 96988043668270486184965849)
  ·
    refine ⟨72741032751202864638724387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96988043668270486184965849 72741032751202864638724387)
    ·
      refine ⟨109111549126804296958086581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72741032751202864638724387 109111549126804296958086581)
      ·
        refine ⟨10229207730637902839820617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109111549126804296958086581 10229207730637902839820617)
        ·
          refine ⟨7671905797978427129865463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10229207730637902839820617 7671905797978427129865463)
          ·
            refine ⟨11507858696967640694798195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7671905797978427129865463 11507858696967640694798195)
            ·
              refine ⟨17261788045451461042197293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11507858696967640694798195 17261788045451461042197293)
              ·
                refine ⟨6473170517044297890823985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17261788045451461042197293 6473170517044297890823985)
                ·
                  refine ⟨4854877887783223418117989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473170517044297890823985 4854877887783223418117989)
                  ·
                    refine ⟨910289603959354390897123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4854877887783223418117989 910289603959354390897123)
                    ·
                      rfl

theorem cell23_5318348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_5318348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318348 prefixEnd_5318348 := by exact prefixLift 5318348
  have htrace : WordTrace (prefixWord ++ tailWord_5318348) baseStart_5318348 baseEnd_5318348 := by
    simpa [prefixWord, tailWord_5318348, baseEnd_5318348] using wordTrace_append hprefix tailTrace_5318348
  have hstable : (prefixWord ++ tailWord_5318348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318348).length < 2 ^ (prefixWord ++ tailWord_5318348).sum := by decide
  have hdescent : baseEnd_5318348 < baseStart_5318348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318375 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5318375 : Nat := 118140960795 + 5318375 * 2 ^ 59
def prefixEnd_5318375 : Nat := 4983230072969 + 3 ^ 40 * 5318375 * 2
def baseEnd_5318375 : Nat := 2730882675855734567053745

theorem tailTrace_5318375 : CollatzResearch.WordTrace tailWord_5318375 prefixEnd_5318375 2730882675855734567053745 := by
  unfold tailWord_5318375
  simp only [CollatzResearch.WordTrace]
  refine ⟨193977072107443155981164579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129318048071628770654109719 193977072107443155981164579)
  ·
    refine ⟨290965608161164733971746869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193977072107443155981164579 290965608161164733971746869)
    ·
      refine ⟨27278025765109193809851269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 290965608161164733971746869 27278025765109193809851269)
      ·
        refine ⟨5114629830957973839347113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27278025765109193809851269 5114629830957973839347113)
        ·
          refine ⟨3835972373218480379510335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5114629830957973839347113 3835972373218480379510335)
          ·
            refine ⟨5753958559827720569265503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3835972373218480379510335 5753958559827720569265503)
            ·
              refine ⟨8630937839741580853898255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5753958559827720569265503 8630937839741580853898255)
              ·
                refine ⟨12946406759612371280847383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8630937839741580853898255 12946406759612371280847383)
                ·
                  refine ⟨19419610139418556921271075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12946406759612371280847383 19419610139418556921271075)
                  ·
                    refine ⟨29129415209127835381906613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19419610139418556921271075 29129415209127835381906613)
                    ·
                      refine ⟨2730882675855734567053745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29129415209127835381906613 2730882675855734567053745)
                      ·
                        rfl

theorem cell23_5318375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5318375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318375 prefixEnd_5318375 := by exact prefixLift 5318375
  have htrace : WordTrace (prefixWord ++ tailWord_5318375) baseStart_5318375 baseEnd_5318375 := by
    simpa [prefixWord, tailWord_5318375, baseEnd_5318375] using wordTrace_append hprefix tailTrace_5318375
  have hstable : (prefixWord ++ tailWord_5318375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318375).length < 2 ^ (prefixWord ++ tailWord_5318375).sum := by decide
  have hdescent : baseEnd_5318375 < baseStart_5318375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318404 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_5318404 : Nat := 118140960795 + 5318404 * 2 ^ 59
def prefixEnd_5318404 : Nat := 4983230072969 + 3 ^ 40 * 5318404 * 2
def baseEnd_5318404 : Nat := 910299188931571651197037

theorem tailTrace_5318404 : CollatzResearch.WordTrace tailWord_5318404 prefixEnd_5318404 910299188931571651197037 := by
  unfold tailWord_5318404
  simp only [CollatzResearch.WordTrace]
  refine ⟨96989064912169046966985133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129318753216225395955980177 96989064912169046966985133)
  ·
    refine ⟨36370899342063392612619425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96989064912169046966985133 36370899342063392612619425)
    ·
      refine ⟨27278174506547544459464569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36370899342063392612619425 27278174506547544459464569)
      ·
        refine ⟨20458630879910658344598427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27278174506547544459464569 20458630879910658344598427)
        ·
          refine ⟨30687946319865987516897641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20458630879910658344598427 30687946319865987516897641)
          ·
            refine ⟨23015959739899490637673231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30687946319865987516897641 23015959739899490637673231)
            ·
              refine ⟨34523939609849235956509847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23015959739899490637673231 34523939609849235956509847)
              ·
                refine ⟨51785909414773853934764771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34523939609849235956509847 51785909414773853934764771)
                ·
                  refine ⟨77678864122160780902147157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51785909414773853934764771 77678864122160780902147157)
                  ·
                    refine ⟨910299188931571651197037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77678864122160780902147157 910299188931571651197037)
                    ·
                      rfl

theorem cell23_5318404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_5318404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318404 prefixEnd_5318404 := by exact prefixLift 5318404
  have htrace : WordTrace (prefixWord ++ tailWord_5318404) baseStart_5318404 baseEnd_5318404 := by
    simpa [prefixWord, tailWord_5318404, baseEnd_5318404] using wordTrace_append hprefix tailTrace_5318404
  have hstable : (prefixWord ++ tailWord_5318404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318404).length < 2 ^ (prefixWord ++ tailWord_5318404).sum := by decide
  have hdescent : baseEnd_5318404 < baseStart_5318404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318411 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 1, 4, 2]
def baseStart_5318411 : Nat := 118140960795 + 5318411 * 2 ^ 59
def prefixEnd_5318411 : Nat := 4983230072969 + 3 ^ 40 * 5318411 * 2
def baseEnd_5318411 : Nat := 2730901161159296426203579

theorem tailTrace_5318411 : CollatzResearch.WordTrace tailWord_5318411 prefixEnd_5318411 2730901161159296426203579 := by
  unfold tailWord_5318411
  simp only [CollatzResearch.WordTrace]
  refine ⟨193978385135312734129475087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129318923423541822752983391 193978385135312734129475087)
  ·
    refine ⟨290967577702969101194212631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193978385135312734129475087 290967577702969101194212631)
    ·
      refine ⟨436451366554453651791318947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290967577702969101194212631 436451366554453651791318947)
      ·
        refine ⟨654677049831680477686978421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436451366554453651791318947 654677049831680477686978421)
        ·
          refine ⟨61375973421720044783154227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 654677049831680477686978421 61375973421720044783154227)
          ·
            refine ⟨92063960132580067174731341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61375973421720044783154227 92063960132580067174731341)
            ·
              refine ⟨34523985049717525190524253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92063960132580067174731341 34523985049717525190524253)
              ·
                refine ⟨12946494393644071946446595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34523985049717525190524253 12946494393644071946446595)
                ·
                  refine ⟨19419741590466107919669893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12946494393644071946446595 19419741590466107919669893)
                  ·
                    refine ⟨3641201548212395234938105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19419741590466107919669893 3641201548212395234938105)
                    ·
                      refine ⟨2730901161159296426203579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641201548212395234938105 2730901161159296426203579)
                      ·
                        rfl

theorem cell23_5318411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4, 2].length) (baseStart_5318411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318411 prefixEnd_5318411 := by exact prefixLift 5318411
  have htrace : WordTrace (prefixWord ++ tailWord_5318411) baseStart_5318411 baseEnd_5318411 := by
    simpa [prefixWord, tailWord_5318411, baseEnd_5318411] using wordTrace_append hprefix tailTrace_5318411
  have hstable : (prefixWord ++ tailWord_5318411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318411).length < 2 ^ (prefixWord ++ tailWord_5318411).sum := by decide
  have hdescent : baseEnd_5318411 < baseStart_5318411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318414 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5318414 : Nat := 118140960795 + 5318414 * 2 ^ 59
def prefixEnd_5318414 : Nat := 4983230072969 + 3 ^ 40 * 5318414 * 2
def baseEnd_5318414 : Nat := 2730902701601259914466065

theorem tailTrace_5318414 : CollatzResearch.WordTrace tailWord_5318414 prefixEnd_5318414 2730902701601259914466065 := by
  unfold tailWord_5318414
  simp only [CollatzResearch.WordTrace]
  refine ⟨24247311819287733205229287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129318996369534577094556197 24247311819287733205229287)
  ·
    refine ⟨36370967728931599807843931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24247311819287733205229287 36370967728931599807843931)
    ·
      refine ⟨54556451593397399711765897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36370967728931599807843931 54556451593397399711765897)
      ·
        refine ⟨40917338695048049783824423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54556451593397399711765897 40917338695048049783824423)
        ·
          refine ⟨61376008042572074675736635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40917338695048049783824423 61376008042572074675736635)
          ·
            refine ⟨92064012063858112013604953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61376008042572074675736635 92064012063858112013604953)
            ·
              refine ⟨69048009047893584010203715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92064012063858112013604953 69048009047893584010203715)
              ·
                refine ⟨103572013571840376015305573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69048009047893584010203715 103572013571840376015305573)
                ·
                  refine ⟨19419752544720070502869795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103572013571840376015305573 19419752544720070502869795)
                  ·
                    refine ⟨29129628817080105754304693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19419752544720070502869795 29129628817080105754304693)
                    ·
                      refine ⟨2730902701601259914466065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29129628817080105754304693 2730902701601259914466065)
                      ·
                        rfl

theorem cell23_5318414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5318414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318414 prefixEnd_5318414 := by exact prefixLift 5318414
  have htrace : WordTrace (prefixWord ++ tailWord_5318414) baseStart_5318414 baseEnd_5318414 := by
    simpa [prefixWord, tailWord_5318414, baseEnd_5318414] using wordTrace_append hprefix tailTrace_5318414
  have hstable : (prefixWord ++ tailWord_5318414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318414).length < 2 ^ (prefixWord ++ tailWord_5318414).sum := by decide
  have hdescent : baseEnd_5318414 < baseStart_5318414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318428 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_5318428 : Nat := 118140960795 + 5318428 * 2 ^ 59
def prefixEnd_5318428 : Nat := 4983230072969 + 3 ^ 40 * 5318428 * 2
def baseEnd_5318428 : Nat := 2730909890330422859691001

theorem tailTrace_5318428 : CollatzResearch.WordTrace tailWord_5318428 prefixEnd_5318428 2730909890330422859691001 := by
  unfold tailWord_5318428
  simp only [CollatzResearch.WordTrace]
  refine ⟨96989502588125573016421969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129319336784167430688562625 96989502588125573016421969)
  ·
    refine ⟨72742126941094179762316477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96989502588125573016421969 72742126941094179762316477)
    ·
      refine ⟨27278297602910317410868679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72742126941094179762316477 27278297602910317410868679)
      ·
        refine ⟨40917446404365476116303019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27278297602910317410868679 40917446404365476116303019)
        ·
          refine ⟨61376169606548214174454529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40917446404365476116303019 61376169606548214174454529)
          ·
            refine ⟨46032127204911160630840897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61376169606548214174454529 46032127204911160630840897)
            ·
              refine ⟨34524095403683370473130673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46032127204911160630840897 34524095403683370473130673)
              ·
                refine ⟨25893071552762527854848005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34524095403683370473130673 25893071552762527854848005)
                ·
                  refine ⟨4854950916142973972784001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25893071552762527854848005 4854950916142973972784001)
                  ·
                    refine ⟨3641213187107230479588001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4854950916142973972784001 3641213187107230479588001)
                    ·
                      refine ⟨2730909890330422859691001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641213187107230479588001 2730909890330422859691001)
                      ·
                        rfl

theorem cell23_5318428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_5318428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318428 prefixEnd_5318428 := by exact prefixLift 5318428
  have htrace : WordTrace (prefixWord ++ tailWord_5318428) baseStart_5318428 baseEnd_5318428 := by
    simpa [prefixWord, tailWord_5318428, baseEnd_5318428] using wordTrace_append hprefix tailTrace_5318428
  have hstable : (prefixWord ++ tailWord_5318428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318428).length < 2 ^ (prefixWord ++ tailWord_5318428).sum := by decide
  have hdescent : baseEnd_5318428 < baseStart_5318428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318434 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_5318434 : Nat := 118140960795 + 5318434 * 2 ^ 59
def prefixEnd_5318434 : Nat := 4983230072969 + 3 ^ 40 * 5318434 * 2
def baseEnd_5318434 : Nat := 303434774579372204023997

theorem tailTrace_5318434 : CollatzResearch.WordTrace tailWord_5318434 prefixEnd_5318434 303434774579372204023997 := by
  unfold tailWord_5318434
  simp only [CollatzResearch.WordTrace]
  refine ⟨48494806003557352264390589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129319482676152939371708237 48494806003557352264390589)
  ·
    refine ⟨18185552251334007099146471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48494806003557352264390589 18185552251334007099146471)
    ·
      refine ⟨27278328377001010648719707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18185552251334007099146471 27278328377001010648719707)
      ·
        refine ⟨40917492565501515973079561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27278328377001010648719707 40917492565501515973079561)
        ·
          refine ⟨30688119424126136979809671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40917492565501515973079561 30688119424126136979809671)
          ·
            refine ⟨46032179136189205469714507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30688119424126136979809671 46032179136189205469714507)
            ·
              refine ⟨69048268704283808204571761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46032179136189205469714507 69048268704283808204571761)
              ·
                refine ⟨51786201528212856153428821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69048268704283808204571761 51786201528212856153428821)
                ·
                  refine ⟨303434774579372204023997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51786201528212856153428821 303434774579372204023997)
                  ·
                    rfl

theorem cell23_5318434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_5318434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318434 prefixEnd_5318434 := by exact prefixLift 5318434
  have htrace : WordTrace (prefixWord ++ tailWord_5318434) baseStart_5318434 baseEnd_5318434 := by
    simpa [prefixWord, tailWord_5318434, baseEnd_5318434] using wordTrace_append hprefix tailTrace_5318434
  have hstable : (prefixWord ++ tailWord_5318434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318434).length < 2 ^ (prefixWord ++ tailWord_5318434).sum := by decide
  have hdescent : baseEnd_5318434 < baseStart_5318434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318451 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 7]
def baseStart_5318451 : Nat := 118140960795 + 5318451 * 2 ^ 59
def prefixEnd_5318451 : Nat := 4983230072969 + 3 ^ 40 * 5318451 * 2
def baseEnd_5318451 : Nat := 303435744487275141078155

theorem tailTrace_5318451 : CollatzResearch.WordTrace tailWord_5318451 prefixEnd_5318451 303435744487275141078155 := by
  unfold tailWord_5318451
  simp only [CollatzResearch.WordTrace]
  refine ⟨193979844055167820960931207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129319896036778547307287471 193979844055167820960931207)
  ·
    refine ⟨290969766082751731441396811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193979844055167820960931207 290969766082751731441396811)
    ·
      refine ⟨436454649124127597162095217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290969766082751731441396811 436454649124127597162095217)
      ·
        refine ⟨327340986843095697871571413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436454649124127597162095217 327340986843095697871571413)
        ·
          refine ⟨7672054379135055418864955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 327340986843095697871571413 7672054379135055418864955)
          ·
            refine ⟨11508081568702583128297433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672054379135055418864955 11508081568702583128297433)
            ·
              refine ⟨8631061176526937346223075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11508081568702583128297433 8631061176526937346223075)
              ·
                refine ⟨12946591764790406019334613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8631061176526937346223075 12946591764790406019334613)
                ·
                  refine ⟨303435744487275141078155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12946591764790406019334613 303435744487275141078155)
                  ·
                    rfl

theorem cell23_5318451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 7].length) (baseStart_5318451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318451 prefixEnd_5318451 := by exact prefixLift 5318451
  have htrace : WordTrace (prefixWord ++ tailWord_5318451) baseStart_5318451 baseEnd_5318451 := by
    simpa [prefixWord, tailWord_5318451, baseEnd_5318451] using wordTrace_append hprefix tailTrace_5318451
  have hstable : (prefixWord ++ tailWord_5318451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318451).length < 2 ^ (prefixWord ++ tailWord_5318451).sum := by decide
  have hdescent : baseEnd_5318451 < baseStart_5318451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318471 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_5318471 : Nat := 118140960795 + 5318471 * 2 ^ 59
def prefixEnd_5318471 : Nat := 4983230072969 + 3 ^ 40 * 5318471 * 2
def baseEnd_5318471 : Nat := 2730931969998566191453303

theorem tailTrace_5318471 : CollatzResearch.WordTrace tailWord_5318471 prefixEnd_5318471 2730931969998566191453303 := by
  unfold tailWord_5318471
  simp only [CollatzResearch.WordTrace]
  refine ⟨193980573515095364376659267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129320382343396909584439511 193980573515095364376659267)
  ·
    refine ⟨290970860272643046564988901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193980573515095364376659267 290970860272643046564988901)
    ·
      refine ⟨54557036301120571230935419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290970860272643046564988901 54557036301120571230935419)
      ·
        refine ⟨81835554451680856846403129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54557036301120571230935419 81835554451680856846403129)
        ·
          refine ⟨61376665838760642634802347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81835554451680856846403129 61376665838760642634802347)
          ·
            refine ⟨92064998758140963952203521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61376665838760642634802347 92064998758140963952203521)
            ·
              refine ⟨69048749068605722964152641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92064998758140963952203521 69048749068605722964152641)
              ·
                refine ⟨51786561801454292223114481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69048749068605722964152641 51786561801454292223114481)
                ·
                  refine ⟨38839921351090719167335861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51786561801454292223114481 38839921351090719167335861)
                  ·
                    refine ⟨3641242626664754921937737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38839921351090719167335861 3641242626664754921937737)
                    ·
                      refine ⟨2730931969998566191453303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641242626664754921937737 2730931969998566191453303)
                      ·
                        rfl

theorem cell23_5318471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_5318471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318471 prefixEnd_5318471 := by exact prefixLift 5318471
  have htrace : WordTrace (prefixWord ++ tailWord_5318471) baseStart_5318471 baseEnd_5318471 := by
    simpa [prefixWord, tailWord_5318471, baseEnd_5318471] using wordTrace_append hprefix tailTrace_5318471
  have hstable : (prefixWord ++ tailWord_5318471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318471).length < 2 ^ (prefixWord ++ tailWord_5318471).sum := by decide
  have hdescent : baseEnd_5318471 < baseStart_5318471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318498 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5318498 : Nat := 118140960795 + 5318498 * 2 ^ 59
def prefixEnd_5318498 : Nat := 4983230072969 + 3 ^ 40 * 5318498 * 2
def baseEnd_5318498 : Nat := 910315277992079195271893

theorem tailTrace_5318498 : CollatzResearch.WordTrace tailWord_5318498 prefixEnd_5318498 910315277992079195271893 := by
  unfold tailWord_5318498
  simp only [CollatzResearch.WordTrace]
  refine ⟨48495389571499386996973037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129321038857331698658594765 48495389571499386996973037)
  ·
    refine ⟨18185771089312270123864889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48495389571499386996973037 18185771089312270123864889)
    ·
      refine ⟨13639328316984202592898667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18185771089312270123864889 13639328316984202592898667)
      ·
        refine ⟨20458992475476303889348001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13639328316984202592898667 20458992475476303889348001)
        ·
          refine ⟨15344244356607227917011001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20458992475476303889348001 15344244356607227917011001)
          ·
            refine ⟨11508183267455420937758251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15344244356607227917011001 11508183267455420937758251)
            ·
              refine ⟨17262274901183131406637377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508183267455420937758251 17262274901183131406637377)
              ·
                refine ⟨12946706175887348554978033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17262274901183131406637377 12946706175887348554978033)
                ·
                  refine ⟨9710029631915511416233525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12946706175887348554978033 9710029631915511416233525)
                  ·
                    refine ⟨910315277992079195271893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9710029631915511416233525 910315277992079195271893)
                    ·
                      rfl

theorem cell23_5318498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5318498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318498 prefixEnd_5318498 := by exact prefixLift 5318498
  have htrace : WordTrace (prefixWord ++ tailWord_5318498) baseStart_5318498 baseEnd_5318498 := by
    simpa [prefixWord, tailWord_5318498, baseEnd_5318498] using wordTrace_append hprefix tailTrace_5318498
  have hstable : (prefixWord ++ tailWord_5318498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318498).length < 2 ^ (prefixWord ++ tailWord_5318498).sum := by decide
  have hdescent : baseEnd_5318498 < baseStart_5318498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318521 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_5318521 : Nat := 118140960795 + 5318521 * 2 ^ 59
def prefixEnd_5318521 : Nat := 4983230072969 + 3 ^ 40 * 5318521 * 2
def baseEnd_5318521 : Nat := 2730957644031290995828073

theorem tailTrace_5318521 : CollatzResearch.WordTrace tailWord_5318521 prefixEnd_5318521 2730957644031290995828073 := by
  unfold tailWord_5318521
  simp only [CollatzResearch.WordTrace]
  refine ⟨193982397164914222915979417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129321598109942815277319611 193982397164914222915979417)
  ·
    refine ⟨145486797873685667186984563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193982397164914222915979417 145486797873685667186984563)
    ·
      refine ⟨218230196810528500780476845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145486797873685667186984563 218230196810528500780476845)
      ·
        refine ⟨81836323803948187792678817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218230196810528500780476845 81836323803948187792678817)
        ·
          refine ⟨61377242852961140844509113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81836323803948187792678817 61377242852961140844509113)
          ·
            refine ⟨46032932139720855633381835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61377242852961140844509113 46032932139720855633381835)
            ·
              refine ⟨69049398209581283450072753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46032932139720855633381835 69049398209581283450072753)
              ·
                refine ⟨51787048657185962587554565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69049398209581283450072753 51787048657185962587554565)
                ·
                  refine ⟨9710071623222367985166481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51787048657185962587554565 9710071623222367985166481)
                  ·
                    refine ⟨7282553717416775988874861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9710071623222367985166481 7282553717416775988874861)
                    ·
                      refine ⟨2730957644031290995828073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7282553717416775988874861 2730957644031290995828073)
                      ·
                        rfl

theorem cell23_5318521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_5318521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318521 prefixEnd_5318521 := by exact prefixLift 5318521
  have htrace : WordTrace (prefixWord ++ tailWord_5318521) baseStart_5318521 baseEnd_5318521 := by
    simpa [prefixWord, tailWord_5318521, baseEnd_5318521] using wordTrace_append hprefix tailTrace_5318521
  have hstable : (prefixWord ++ tailWord_5318521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318521).length < 2 ^ (prefixWord ++ tailWord_5318521).sum := by decide
  have hdescent : baseEnd_5318521 < baseStart_5318521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318562 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5318562 : Nat := 118140960795 + 5318562 * 2 ^ 59
def prefixEnd_5318562 : Nat := 4983230072969 + 3 ^ 40 * 5318562 * 2
def baseEnd_5318562 : Nat := 910326232246041778471795

theorem tailTrace_5318562 : CollatzResearch.WordTrace tailWord_5318562 prefixEnd_5318562 910326232246041778471795 := by
  unfold tailWord_5318562
  simp only [CollatzResearch.WordTrace]
  refine ⟨48495973139441421729555485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129322595038510457945481293 48495973139441421729555485)
  ·
    refine ⟨18185989927290533148583307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48495973139441421729555485 18185989927290533148583307)
    ·
      refine ⟨27278984890935799722874961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18185989927290533148583307 27278984890935799722874961)
      ·
        refine ⟨20459238668201849792156221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27278984890935799722874961 20459238668201849792156221)
        ·
          refine ⟨7672214500575693672058583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20459238668201849792156221 7672214500575693672058583)
          ·
            refine ⟨11508321750863540508087875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672214500575693672058583 11508321750863540508087875)
            ·
              refine ⟨17262482626295310762131813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508321750863540508087875 17262482626295310762131813)
              ·
                refine ⟨3236715492430370767899715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17262482626295310762131813 3236715492430370767899715)
                ·
                  refine ⟨4855073238645556151849573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236715492430370767899715 4855073238645556151849573)
                  ·
                    refine ⟨910326232246041778471795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4855073238645556151849573 910326232246041778471795)
                    ·
                      rfl

theorem cell23_5318562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5318562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318562 prefixEnd_5318562 := by exact prefixLift 5318562
  have htrace : WordTrace (prefixWord ++ tailWord_5318562) baseStart_5318562 baseEnd_5318562 := by
    simpa [prefixWord, tailWord_5318562, baseEnd_5318562] using wordTrace_append hprefix tailTrace_5318562
  have hstable : (prefixWord ++ tailWord_5318562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318562).length < 2 ^ (prefixWord ++ tailWord_5318562).sum := by decide
  have hdescent : baseEnd_5318562 < baseStart_5318562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318578 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_5318578 : Nat := 118140960795 + 5318578 * 2 ^ 59
def prefixEnd_5318578 : Nat := 4983230072969 + 3 ^ 40 * 5318578 * 2
def baseEnd_5318578 : Nat := 2730986912428597272815311

theorem tailTrace_5318578 : CollatzResearch.WordTrace tailWord_5318578 prefixEnd_5318578 2730986912428597272815311 := by
  unfold tailWord_5318578
  simp only [CollatzResearch.WordTrace]
  refine ⟨48496119031426930412701097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129322984083805147767202925 48496119031426930412701097)
  ·
    refine ⟨36372089273570197809525823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48496119031426930412701097 36372089273570197809525823)
    ·
      refine ⟨54558133910355296714288735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36372089273570197809525823 54558133910355296714288735)
      ·
        refine ⟨81837200865532945071433103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54558133910355296714288735 81837200865532945071433103)
        ·
          refine ⟨122755801298299417607149655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81837200865532945071433103 122755801298299417607149655)
          ·
            refine ⟨184133701947449126410724483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122755801298299417607149655 184133701947449126410724483)
            ·
              refine ⟨276200552921173689616086725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184133701947449126410724483 276200552921173689616086725)
              ·
                refine ⟨51787603672720066803016261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276200552921173689616086725 51787603672720066803016261)
                ·
                  refine ⟨9710175688635012525565549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51787603672720066803016261 9710175688635012525565549)
                  ·
                    refine ⟨3641315883238129697087081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9710175688635012525565549 3641315883238129697087081)
                    ·
                      refine ⟨2730986912428597272815311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641315883238129697087081 2730986912428597272815311)
                      ·
                        rfl

theorem cell23_5318578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_5318578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318578 prefixEnd_5318578 := by exact prefixLift 5318578
  have htrace : WordTrace (prefixWord ++ tailWord_5318578) baseStart_5318578 baseEnd_5318578 := by
    simpa [prefixWord, tailWord_5318578, baseEnd_5318578] using wordTrace_append hprefix tailTrace_5318578
  have hstable : (prefixWord ++ tailWord_5318578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318578).length < 2 ^ (prefixWord ++ tailWord_5318578).sum := by decide
  have hdescent : baseEnd_5318578 < baseStart_5318578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318591 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_5318591 : Nat := 118140960795 + 5318591 * 2 ^ 59
def prefixEnd_5318591 : Nat := 4983230072969 + 3 ^ 40 * 5318591 * 2
def baseEnd_5318591 : Nat := 2730993587677105721952751

theorem tailTrace_5318591 : CollatzResearch.WordTrace tailWord_5318591 prefixEnd_5318591 2730993587677105721952751 := by
  unfold tailWord_5318591
  simp only [CollatzResearch.WordTrace]
  refine ⟨193984950274660624871027627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129323300183107083247351751 193984950274660624871027627)
  ·
    refine ⟨290977425411990937306541441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193984950274660624871027627 290977425411990937306541441)
    ·
      refine ⟨218233069058993202979906081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290977425411990937306541441 218233069058993202979906081)
      ·
        refine ⟨163674801794244902234929561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218233069058993202979906081 163674801794244902234929561)
        ·
          refine ⟨122756101345683676676197171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163674801794244902234929561 122756101345683676676197171)
          ·
            refine ⟨184134152018525515014295757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122756101345683676676197171 184134152018525515014295757)
            ·
              refine ⟨69050307006947068130360909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184134152018525515014295757 69050307006947068130360909)
              ·
                refine ⟨25893865127605150548885341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69050307006947068130360909 25893865127605150548885341)
                ·
                  refine ⟨9710199422851931455832003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25893865127605150548885341 9710199422851931455832003)
                  ·
                    refine ⟨14565299134277897183748005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9710199422851931455832003 14565299134277897183748005)
                    ·
                      refine ⟨2730993587677105721952751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14565299134277897183748005 2730993587677105721952751)
                      ·
                        rfl

theorem cell23_5318591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_5318591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318591 prefixEnd_5318591 := by exact prefixLift 5318591
  have htrace : WordTrace (prefixWord ++ tailWord_5318591) baseStart_5318591 baseEnd_5318591 := by
    simpa [prefixWord, tailWord_5318591, baseEnd_5318591] using wordTrace_append hprefix tailTrace_5318591
  have hstable : (prefixWord ++ tailWord_5318591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318591).length < 2 ^ (prefixWord ++ tailWord_5318591).sum := by decide
  have hdescent : baseEnd_5318591 < baseStart_5318591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318601 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 6, 4]
def baseStart_5318601 : Nat := 118140960795 + 5318601 * 2 ^ 59
def prefixEnd_5318601 : Nat := 4983230072969 + 3 ^ 40 * 5318601 * 2
def baseEnd_5318601 : Nat := 910332907494550227609235

theorem tailTrace_5318601 : CollatzResearch.WordTrace tailWord_5318601 prefixEnd_5318601 910332907494550227609235 := by
  unfold tailWord_5318601
  simp only [CollatzResearch.WordTrace]
  refine ⟨193985315004624396578891657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129323543336416264385927771 193985315004624396578891657)
  ·
    refine ⟨145488986253468297434168743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193985315004624396578891657 145488986253468297434168743)
    ·
      refine ⟨218233479380202446151253115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145488986253468297434168743 218233479380202446151253115)
      ·
        refine ⟨327350219070303669226879673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218233479380202446151253115 327350219070303669226879673)
        ·
          refine ⟨245512664302727751920159755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327350219070303669226879673 245512664302727751920159755)
          ·
            refine ⟨368268996454091627880239633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245512664302727751920159755 368268996454091627880239633)
            ·
              refine ⟨276201747340568720910179725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368268996454091627880239633 276201747340568720910179725)
              ·
                refine ⟨103575655252713270341317397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276201747340568720910179725 103575655252713270341317397)
                ·
                  refine ⟨4855108839970934547249253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103575655252713270341317397 4855108839970934547249253)
                  ·
                    refine ⟨910332907494550227609235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4855108839970934547249253 910332907494550227609235)
                    ·
                      rfl

theorem cell23_5318601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_5318601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318601 prefixEnd_5318601 := by exact prefixLift 5318601
  have htrace : WordTrace (prefixWord ++ tailWord_5318601) baseStart_5318601 baseEnd_5318601 := by
    simpa [prefixWord, tailWord_5318601, baseEnd_5318601] using wordTrace_append hprefix tailTrace_5318601
  have hstable : (prefixWord ++ tailWord_5318601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318601).length < 2 ^ (prefixWord ++ tailWord_5318601).sum := by decide
  have hdescent : baseEnd_5318601 < baseStart_5318601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318625 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_5318625 : Nat := 118140960795 + 5318625 * 2 ^ 59
def prefixEnd_5318625 : Nat := 4983230072969 + 3 ^ 40 * 5318625 * 2
def baseEnd_5318625 : Nat := 2731011046019358588927595

theorem tailTrace_5318625 : CollatzResearch.WordTrace tailWord_5318625 prefixEnd_5318625 2731011046019358588927595 := by
  unfold tailWord_5318625
  simp only [CollatzResearch.WordTrace]
  refine ⟨193986190356537448677765329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129324126904358299118510219 193986190356537448677765329)
  ·
    refine ⟨145489642767403086508323997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193986190356537448677765329 145489642767403086508323997)
    ·
      refine ⟨54558616037776157440621499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145489642767403086508323997 54558616037776157440621499)
      ·
        refine ⟨81837924056664236160932249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54558616037776157440621499 81837924056664236160932249)
        ·
          refine ⟨61378443042498177120699187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81837924056664236160932249 61378443042498177120699187)
          ·
            refine ⟨92067664563747265681048781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61378443042498177120699187 92067664563747265681048781)
            ·
              refine ⟨34525374211405224630393293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92067664563747265681048781 34525374211405224630393293)
              ·
                refine ⟨12947015329276959236397485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34525374211405224630393293 12947015329276959236397485)
                ·
                  refine ⟨4855130748478859713649057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12947015329276959236397485 4855130748478859713649057)
                  ·
                    refine ⟨3641348061359144785236793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855130748478859713649057 3641348061359144785236793)
                    ·
                      refine ⟨2731011046019358588927595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641348061359144785236793 2731011046019358588927595)
                      ·
                        rfl

theorem cell23_5318625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_5318625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318625 prefixEnd_5318625 := by exact prefixLift 5318625
  have htrace : WordTrace (prefixWord ++ tailWord_5318625) baseStart_5318625 baseEnd_5318625 := by
    simpa [prefixWord, tailWord_5318625, baseEnd_5318625] using wordTrace_append hprefix tailTrace_5318625
  have hstable : (prefixWord ++ tailWord_5318625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318625).length < 2 ^ (prefixWord ++ tailWord_5318625).sum := by decide
  have hdescent : baseEnd_5318625 < baseStart_5318625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318638 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_5318638 : Nat := 118140960795 + 5318638 * 2 ^ 59
def prefixEnd_5318638 : Nat := 4983230072969 + 3 ^ 40 * 5318638 * 2
def baseEnd_5318638 : Nat := 2731017721267867038065035

theorem tailTrace_5318638 : CollatzResearch.WordTrace tailWord_5318638 prefixEnd_5318638 2731017721267867038065035 := by
  unfold tailWord_5318638
  simp only [CollatzResearch.WordTrace]
  refine ⟨24248333063186293987248571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129324443003660234598659045 24248333063186293987248571)
  ·
    refine ⟨36372499594779440980872857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24248333063186293987248571 36372499594779440980872857)
    ·
      refine ⟨27279374696084580735654643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36372499594779440980872857 27279374696084580735654643)
      ·
        refine ⟨40919062044126871103481965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27279374696084580735654643 40919062044126871103481965)
        ·
          refine ⟨15344648266547576663805737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40919062044126871103481965 15344648266547576663805737)
          ·
            refine ⟨11508486199910682497854303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15344648266547576663805737 11508486199910682497854303)
            ·
              refine ⟨17262729299866023746781455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508486199910682497854303 17262729299866023746781455)
              ·
                refine ⟨25894093949799035620172183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17262729299866023746781455 25894093949799035620172183)
                ·
                  refine ⟨38841140924698553430258275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25894093949799035620172183 38841140924698553430258275)
                  ·
                    refine ⟨58261711387047830145387413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38841140924698553430258275 58261711387047830145387413)
                    ·
                      refine ⟨2731017721267867038065035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58261711387047830145387413 2731017721267867038065035)
                      ·
                        rfl

theorem cell23_5318638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_5318638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318638 prefixEnd_5318638 := by exact prefixLift 5318638
  have htrace : WordTrace (prefixWord ++ tailWord_5318638) baseStart_5318638 baseEnd_5318638 := by
    simpa [prefixWord, tailWord_5318638, baseEnd_5318638] using wordTrace_append hprefix tailTrace_5318638
  have hstable : (prefixWord ++ tailWord_5318638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318638).length < 2 ^ (prefixWord ++ tailWord_5318638).sum := by decide
  have hdescent : baseEnd_5318638 < baseStart_5318638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318681 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_5318681 : Nat := 118140960795 + 5318681 * 2 ^ 59
def prefixEnd_5318681 : Nat := 4983230072969 + 3 ^ 40 * 5318681 * 2
def baseEnd_5318681 : Nat := 2731039800936010369827337

theorem tailTrace_5318681 : CollatzResearch.WordTrace tailWord_5318681 prefixEnd_5318681 2731039800936010369827337 := by
  unfold tailWord_5318681
  simp only [CollatzResearch.WordTrace]
  refine ⟨193988232844334570241803897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129325488562889713494535931 193988232844334570241803897)
  ·
    refine ⟨145491174633250927681352923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193988232844334570241803897 145491174633250927681352923)
    ·
      refine ⟨218236761949876391522029385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145491174633250927681352923 218236761949876391522029385)
      ·
        refine ⟨163677571462407293641522039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218236761949876391522029385 163677571462407293641522039)
        ·
          refine ⟨245516357193610940462283059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163677571462407293641522039 245516357193610940462283059)
          ·
            refine ⟨368274535790416410693424589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245516357193610940462283059 368274535790416410693424589)
            ·
              refine ⟨138102950921406154010034221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368274535790416410693424589 138102950921406154010034221)
              ·
                refine ⟨51788606595527307753762833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138102950921406154010034221 51788606595527307753762833)
                ·
                  refine ⟨38841454946645480815322125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51788606595527307753762833 38841454946645480815322125)
                  ·
                    refine ⟨14565545604992055305745797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38841454946645480815322125 14565545604992055305745797)
                    ·
                      refine ⟨2731039800936010369827337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14565545604992055305745797 2731039800936010369827337)
                      ·
                        rfl

theorem cell23_5318681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_5318681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318681 prefixEnd_5318681 := by exact prefixLift 5318681
  have htrace : WordTrace (prefixWord ++ tailWord_5318681) baseStart_5318681 baseEnd_5318681 := by
    simpa [prefixWord, tailWord_5318681, baseEnd_5318681] using wordTrace_append hprefix tailTrace_5318681
  have hstable : (prefixWord ++ tailWord_5318681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318681).length < 2 ^ (prefixWord ++ tailWord_5318681).sum := by decide
  have hdescent : baseEnd_5318681 < baseStart_5318681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318691 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 8]
def baseStart_5318691 : Nat := 118140960795 + 5318691 * 2 ^ 59
def prefixEnd_5318691 : Nat := 4983230072969 + 3 ^ 40 * 5318691 * 2
def baseEnd_5318691 : Nat := 910348311914185110234097

theorem tailTrace_5318691 : CollatzResearch.WordTrace tailWord_5318691 prefixEnd_5318691 910348311914185110234097 := by
  unfold tailWord_5318691
  simp only [CollatzResearch.WordTrace]
  refine ⟨193988597574298341949667927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129325731716198894633111951 193988597574298341949667927)
  ·
    refine ⟨290982896361447512924501891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193988597574298341949667927 290982896361447512924501891)
    ·
      refine ⟨436474344542171269386752837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290982896361447512924501891 436474344542171269386752837)
      ·
        refine ⟨81838939601657113010016157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 436474344542171269386752837 81838939601657113010016157)
        ·
          refine ⟨30689602350621417378756059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81838939601657113010016157 30689602350621417378756059)
          ·
            refine ⟨46034403525932126068134089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30689602350621417378756059 46034403525932126068134089)
            ·
              refine ⟨34525802644449094551100567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46034403525932126068134089 34525802644449094551100567)
              ·
                refine ⟨51788703966673641826650851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34525802644449094551100567 51788703966673641826650851)
                ·
                  refine ⟨77683055950010462739976277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51788703966673641826650851 77683055950010462739976277)
                  ·
                    refine ⟨910348311914185110234097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77683055950010462739976277 910348311914185110234097)
                    ·
                      rfl

theorem cell23_5318691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_5318691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318691 prefixEnd_5318691 := by exact prefixLift 5318691
  have htrace : WordTrace (prefixWord ++ tailWord_5318691) baseStart_5318691 baseEnd_5318691 := by
    simpa [prefixWord, tailWord_5318691, baseEnd_5318691] using wordTrace_append hprefix tailTrace_5318691
  have hstable : (prefixWord ++ tailWord_5318691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318691).length < 2 ^ (prefixWord ++ tailWord_5318691).sum := by decide
  have hdescent : baseEnd_5318691 < baseStart_5318691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318696 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5318696 : Nat := 118140960795 + 5318696 * 2 ^ 59
def prefixEnd_5318696 : Nat := 4983230072969 + 3 ^ 40 * 5318696 * 2
def baseEnd_5318696 : Nat := 2731047503145827811139769

theorem tailTrace_5318696 : CollatzResearch.WordTrace tailWord_5318696 prefixEnd_5318696 2731047503145827811139769 := by
  unfold tailWord_5318696
  simp only [CollatzResearch.WordTrace]
  refine ⟨96994389969640113901799971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129325853292853485202399961 96994389969640113901799971)
  ·
    refine ⟨145491584954460170852699957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96994389969640113901799971 145491584954460170852699957)
    ·
      refine ⟨13639836089480641017440621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145491584954460170852699957 13639836089480641017440621)
      ·
        refine ⟨5114938533555240381540233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13639836089480641017440621 5114938533555240381540233)
        ·
          refine ⟨3836203900166430286155175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5114938533555240381540233 3836203900166430286155175)
          ·
            refine ⟨5754305850249645429232763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836203900166430286155175 5754305850249645429232763)
            ·
              refine ⟨8631458775374468143849145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754305850249645429232763 8631458775374468143849145)
              ·
                refine ⟨6473594081530851107886859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8631458775374468143849145 6473594081530851107886859)
                ·
                  refine ⟨9710391122296276661830289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473594081530851107886859 9710391122296276661830289)
                  ·
                    refine ⟨7282793341722207496372717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9710391122296276661830289 7282793341722207496372717)
                    ·
                      refine ⟨2731047503145827811139769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7282793341722207496372717 2731047503145827811139769)
                      ·
                        rfl

theorem cell23_5318696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5318696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318696 prefixEnd_5318696 := by exact prefixLift 5318696
  have htrace : WordTrace (prefixWord ++ tailWord_5318696) baseStart_5318696 baseEnd_5318696 := by
    simpa [prefixWord, tailWord_5318696, baseEnd_5318696] using wordTrace_append hprefix tailTrace_5318696
  have hstable : (prefixWord ++ tailWord_5318696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318696).length < 2 ^ (prefixWord ++ tailWord_5318696).sum := by decide
  have hdescent : baseEnd_5318696 < baseStart_5318696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318702 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_5318702 : Nat := 118140960795 + 5318702 * 2 ^ 59
def prefixEnd_5318702 : Nat := 4983230072969 + 3 ^ 40 * 5318702 * 2
def baseEnd_5318702 : Nat := 2731050584029754787664741

theorem tailTrace_5318702 : CollatzResearch.WordTrace tailWord_5318702 prefixEnd_5318702 2731050584029754787664741 := by
  unfold tailWord_5318702
  simp only [CollatzResearch.WordTrace]
  refine ⟨24248624847157311353539795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129325999184838993885545573 24248624847157311353539795)
  ·
    refine ⟨36372937270735967030309693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24248624847157311353539795 36372937270735967030309693)
    ·
      refine ⟨13639851476525987636366135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36372937270735967030309693 13639851476525987636366135)
      ·
        refine ⟨20459777214788981454549203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13639851476525987636366135 20459777214788981454549203)
        ·
          refine ⟨30689665822183472181823805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20459777214788981454549203 30689665822183472181823805)
          ·
            refine ⟨11508624683318802068183927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30689665822183472181823805 11508624683318802068183927)
            ·
              refine ⟨17262937024978203102275891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508624683318802068183927 17262937024978203102275891)
              ·
                refine ⟨25894405537467304653413837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17262937024978203102275891 25894405537467304653413837)
                ·
                  refine ⟨9710402076550239245030189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25894405537467304653413837 9710402076550239245030189)
                  ·
                    refine ⟨3641400778706339716886321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9710402076550239245030189 3641400778706339716886321)
                    ·
                      refine ⟨2731050584029754787664741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641400778706339716886321 2731050584029754787664741)
                      ·
                        rfl

theorem cell23_5318702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_5318702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318702 prefixEnd_5318702 := by exact prefixLift 5318702
  have htrace : WordTrace (prefixWord ++ tailWord_5318702) baseStart_5318702 baseEnd_5318702 := by
    simpa [prefixWord, tailWord_5318702, baseEnd_5318702] using wordTrace_append hprefix tailTrace_5318702
  have hstable : (prefixWord ++ tailWord_5318702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318702).length < 2 ^ (prefixWord ++ tailWord_5318702).sum := by decide
  have hdescent : baseEnd_5318702 < baseStart_5318702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318732 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5318732 : Nat := 118140960795 + 5318732 * 2 ^ 59
def prefixEnd_5318732 : Nat := 4983230072969 + 3 ^ 40 * 5318732 * 2
def baseEnd_5318732 : Nat := 2731065988449389670289603

theorem tailTrace_5318732 : CollatzResearch.WordTrace tailWord_5318732 prefixEnd_5318732 2731065988449389670289603 := by
  unfold tailWord_5318732
  simp only [CollatzResearch.WordTrace]
  refine ⟨96995046483574902975955225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129326728644766537301273633 96995046483574902975955225)
  ·
    refine ⟨72746284862681177231966419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96995046483574902975955225 72746284862681177231966419)
    ·
      refine ⟨109119427294021765847949629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72746284862681177231966419 109119427294021765847949629)
      ·
        refine ⟨40919785235258162192981111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109119427294021765847949629 40919785235258162192981111)
        ·
          refine ⟨61379677852887243289471667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40919785235258162192981111 61379677852887243289471667)
          ·
            refine ⟨92069516779330864934207501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61379677852887243289471667 92069516779330864934207501)
            ·
              refine ⟨34526068792249074350327813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92069516779330864934207501 34526068792249074350327813)
              ·
                refine ⟨6473637898546701440686465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34526068792249074350327813 6473637898546701440686465)
                ·
                  refine ⟨4855228423910026080514849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473637898546701440686465 4855228423910026080514849)
                  ·
                    refine ⟨3641421317932519560386137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855228423910026080514849 3641421317932519560386137)
                    ·
                      refine ⟨2731065988449389670289603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641421317932519560386137 2731065988449389670289603)
                      ·
                        rfl

theorem cell23_5318732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5318732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318732 prefixEnd_5318732 := by exact prefixLift 5318732
  have htrace : WordTrace (prefixWord ++ tailWord_5318732) baseStart_5318732 baseEnd_5318732 := by
    simpa [prefixWord, tailWord_5318732, baseEnd_5318732] using wordTrace_append hprefix tailTrace_5318732
  have hstable : (prefixWord ++ tailWord_5318732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318732).length < 2 ^ (prefixWord ++ tailWord_5318732).sum := by decide
  have hdescent : baseEnd_5318732 < baseStart_5318732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318742 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5318742 : Nat := 118140960795 + 5318742 * 2 ^ 59
def prefixEnd_5318742 : Nat := 4983230072969 + 3 ^ 40 * 5318742 * 2
def baseEnd_5318742 : Nat := 910357041085311543721519

theorem tailTrace_5318742 : CollatzResearch.WordTrace tailWord_5318742 prefixEnd_5318742 910357041085311543721519 := by
  unfold tailWord_5318742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12124403606069598603735905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129326971798075718439849653 12124403606069598603735905)
  ·
    refine ⟨9093302704552198952801929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12124403606069598603735905 9093302704552198952801929)
    ·
      refine ⟨6819977028414149214601447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9093302704552198952801929 6819977028414149214601447)
      ·
        refine ⟨10229965542621223821902171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6819977028414149214601447 10229965542621223821902171)
        ·
          refine ⟨15344948313931835732853257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10229965542621223821902171 15344948313931835732853257)
          ·
            refine ⟨11508711235448876799639943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15344948313931835732853257 11508711235448876799639943)
            ·
              refine ⟨17263066853173315199459915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508711235448876799639943 17263066853173315199459915)
              ·
                refine ⟨25894600279759972799189873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17263066853173315199459915 25894600279759972799189873)
                ·
                  refine ⟨19420950209819979599392405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25894600279759972799189873 19420950209819979599392405)
                  ·
                    refine ⟨910357041085311543721519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19420950209819979599392405 910357041085311543721519)
                    ·
                      rfl

theorem cell23_5318742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5318742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318742 prefixEnd_5318742 := by exact prefixLift 5318742
  have htrace : WordTrace (prefixWord ++ tailWord_5318742) baseStart_5318742 baseEnd_5318742 := by
    simpa [prefixWord, tailWord_5318742, baseEnd_5318742] using wordTrace_append hprefix tailTrace_5318742
  have hstable : (prefixWord ++ tailWord_5318742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318742).length < 2 ^ (prefixWord ++ tailWord_5318742).sum := by decide
  have hdescent : baseEnd_5318742 < baseStart_5318742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318749 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5318749 : Nat := 118140960795 + 5318749 * 2 ^ 59
def prefixEnd_5318749 : Nat := 4983230072969 + 3 ^ 40 * 5318749 * 2
def baseEnd_5318749 : Nat := 2731074717620516103777025

theorem tailTrace_5318749 : CollatzResearch.WordTrace tailWord_5318749 prefixEnd_5318749 2731074717620516103777025 := by
  unfold tailWord_5318749
  simp only [CollatzResearch.WordTrace]
  refine ⟨193990713008088217855279301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129327142005392145236852867 193990713008088217855279301)
  ·
    refine ⟨36373258689016540847864869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193990713008088217855279301 36373258689016540847864869)
    ·
      refine ⟨6819986004190601408974663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36373258689016540847864869 6819986004190601408974663)
      ·
        refine ⟨10229979006285902113461995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6819986004190601408974663 10229979006285902113461995)
        ·
          refine ⟨15344968509428853170192993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10229979006285902113461995 15344968509428853170192993)
          ·
            refine ⟨11508726382071639877644745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15344968509428853170192993 11508726382071639877644745)
            ·
              refine ⟨8631544786553729908233559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11508726382071639877644745 8631544786553729908233559)
              ·
                refine ⟨12947317179830594862350339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8631544786553729908233559 12947317179830594862350339)
                ·
                  refine ⟨19420975769745892293525509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12947317179830594862350339 19420975769745892293525509)
                  ·
                    refine ⟨3641432956827354805036033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19420975769745892293525509 3641432956827354805036033)
                    ·
                      refine ⟨2731074717620516103777025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641432956827354805036033 2731074717620516103777025)
                      ·
                        rfl

theorem cell23_5318749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5318749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318749 prefixEnd_5318749 := by exact prefixLift 5318749
  have htrace : WordTrace (prefixWord ++ tailWord_5318749) baseStart_5318749 baseEnd_5318749 := by
    simpa [prefixWord, tailWord_5318749, baseEnd_5318749] using wordTrace_append hprefix tailTrace_5318749
  have hstable : (prefixWord ++ tailWord_5318749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318749).length < 2 ^ (prefixWord ++ tailWord_5318749).sum := by decide
  have hdescent : baseEnd_5318749 < baseStart_5318749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318768 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_5318768 : Nat := 118140960795 + 5318768 * 2 ^ 59
def prefixEnd_5318768 : Nat := 4983230072969 + 3 ^ 40 * 5318768 * 2
def baseEnd_5318768 : Nat := 910361491250983843146479

theorem tailTrace_5318768 : CollatzResearch.WordTrace tailWord_5318768 prefixEnd_5318768 910361491250983843146479 := by
  unfold tailWord_5318768
  simp only [CollatzResearch.WordTrace]
  refine ⟨96995702997509692050110479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129327603996679589400147305 96995702997509692050110479)
  ·
    refine ⟨145493554496264538075165719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96995702997509692050110479 145493554496264538075165719)
    ·
      refine ⟨218240331744396807112748579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145493554496264538075165719 218240331744396807112748579)
      ·
        refine ⟨327360497616595210669122869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218240331744396807112748579 327360497616595210669122869)
        ·
          refine ⟨30690046651555801000230269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327360497616595210669122869 30690046651555801000230269)
          ·
            refine ⟨11508767494333425375086351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30690046651555801000230269 11508767494333425375086351)
            ·
              refine ⟨17263151241500138062629527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508767494333425375086351 17263151241500138062629527)
              ·
                refine ⟨25894726862250207093944291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17263151241500138062629527 25894726862250207093944291)
                ·
                  refine ⟨38842090293375310640916437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25894726862250207093944291 38842090293375310640916437)
                  ·
                    refine ⟨910361491250983843146479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38842090293375310640916437 910361491250983843146479)
                    ·
                      rfl

theorem cell23_5318768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_5318768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318768 prefixEnd_5318768 := by exact prefixLift 5318768
  have htrace : WordTrace (prefixWord ++ tailWord_5318768) baseStart_5318768 baseEnd_5318768 := by
    simpa [prefixWord, tailWord_5318768, baseEnd_5318768] using wordTrace_append hprefix tailTrace_5318768
  have hstable : (prefixWord ++ tailWord_5318768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318768).length < 2 ^ (prefixWord ++ tailWord_5318768).sum := by decide
  have hdescent : baseEnd_5318768 < baseStart_5318768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318805 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_5318805 : Nat := 118140960795 + 5318805 * 2 ^ 59
def prefixEnd_5318805 : Nat := 4983230072969 + 3 ^ 40 * 5318805 * 2
def baseEnd_5318805 : Nat := 2731103472537167884676767

theorem tailTrace_5318805 : CollatzResearch.WordTrace tailWord_5318805 prefixEnd_5318805 2731103472537167884676767 := by
  unfold tailWord_5318805
  simp only [CollatzResearch.WordTrace]
  refine ⟨193992755495885339419317869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129328503663923559612878579 193992755495885339419317869)
  ·
    refine ⟨72747283310957002282244201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193992755495885339419317869 72747283310957002282244201)
    ·
      refine ⟨54560462483217751711683151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72747283310957002282244201 54560462483217751711683151)
      ·
        refine ⟨81840693724826627567524727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54560462483217751711683151 81840693724826627567524727)
        ·
          refine ⟨122761040587239941351287091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81840693724826627567524727 122761040587239941351287091)
          ·
            refine ⟨184141560880859912026930637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122761040587239941351287091 184141560880859912026930637)
            ·
              refine ⟨69053085330322467010098989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184141560880859912026930637 69053085330322467010098989)
              ·
                refine ⟨25894906998870925128787121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69053085330322467010098989 25894906998870925128787121)
                ·
                  refine ⟨19421180249153193846590341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25894906998870925128787121 19421180249153193846590341)
                  ·
                    refine ⟨3641471296716223846235689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19421180249153193846590341 3641471296716223846235689)
                    ·
                      refine ⟨2731103472537167884676767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641471296716223846235689 2731103472537167884676767)
                      ·
                        rfl

theorem cell23_5318805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_5318805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318805 prefixEnd_5318805 := by exact prefixLift 5318805
  have htrace : WordTrace (prefixWord ++ tailWord_5318805) baseStart_5318805 baseEnd_5318805 := by
    simpa [prefixWord, tailWord_5318805, baseEnd_5318805] using wordTrace_append hprefix tailTrace_5318805
  have hstable : (prefixWord ++ tailWord_5318805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318805).length < 2 ^ (prefixWord ++ tailWord_5318805).sum := by decide
  have hdescent : baseEnd_5318805 < baseStart_5318805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318836 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5318836 : Nat := 118140960795 + 5318836 * 2 ^ 59
def prefixEnd_5318836 : Nat := 4983230072969 + 3 ^ 40 * 5318836 * 2
def baseEnd_5318836 : Nat := 910373130145819087796375

theorem tailTrace_5318836 : CollatzResearch.WordTrace tailWord_5318836 prefixEnd_5318836 910373130145819087796375 := by
  unfold tailWord_5318836
  simp only [CollatzResearch.WordTrace]
  refine ⟨96996943079386515856848181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129329257439182021142464241 96996943079386515856848181)
  ·
    refine ⟨9093463413692485861579517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96996943079386515856848181 9093463413692485861579517)
    ·
      refine ⟨3410048780134682198092319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9093463413692485861579517 3410048780134682198092319)
      ·
        refine ⟨5115073170202023297138479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410048780134682198092319 5115073170202023297138479)
        ·
          refine ⟨7672609755303034945707719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115073170202023297138479 7672609755303034945707719)
          ·
            refine ⟨11508914632954552418561579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672609755303034945707719 11508914632954552418561579)
            ·
              refine ⟨17263371949431828627842369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508914632954552418561579 17263371949431828627842369)
              ·
                refine ⟨12947528962073871470881777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17263371949431828627842369 12947528962073871470881777)
                ·
                  refine ⟨9710646721555403603161333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12947528962073871470881777 9710646721555403603161333)
                  ·
                    refine ⟨910373130145819087796375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9710646721555403603161333 910373130145819087796375)
                    ·
                      rfl

theorem cell23_5318836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5318836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318836 prefixEnd_5318836 := by exact prefixLift 5318836
  have htrace : WordTrace (prefixWord ++ tailWord_5318836) baseStart_5318836 baseEnd_5318836 := by
    simpa [prefixWord, tailWord_5318836, baseEnd_5318836] using wordTrace_append hprefix tailTrace_5318836
  have hstable : (prefixWord ++ tailWord_5318836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318836).length < 2 ^ (prefixWord ++ tailWord_5318836).sum := by decide
  have hdescent : baseEnd_5318836 < baseStart_5318836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318862 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_5318862 : Nat := 118140960795 + 5318862 * 2 ^ 59
def prefixEnd_5318862 : Nat := 4983230072969 + 3 ^ 40 * 5318862 * 2
def baseEnd_5318862 : Nat := 303459193437163795740445

theorem tailTrace_5318862 : CollatzResearch.WordTrace tailWord_5318862 prefixEnd_5318862 303459193437163795740445 := by
  unfold tailWord_5318862
  simp only [CollatzResearch.WordTrace]
  refine ⟨24249354307084854769267855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129329889637785892102761893 24249354307084854769267855)
  ·
    refine ⟨36374031460627282153901783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24249354307084854769267855 36374031460627282153901783)
    ·
      refine ⟨54561047190940923230852675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36374031460627282153901783 54561047190940923230852675)
      ·
        refine ⟨81841570786411384846279013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54561047190940923230852675 81841570786411384846279013)
        ·
          refine ⟨15345294522452134658677315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81841570786411384846279013 15345294522452134658677315)
          ·
            refine ⟨23017941783678201988015973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15345294522452134658677315 23017941783678201988015973)
            ·
              refine ⟨4315864084439662872752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23017941783678201988015973 4315864084439662872752995)
              ·
                refine ⟨6473796126659494309129493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315864084439662872752995 6473796126659494309129493)
                ·
                  refine ⟨303459193437163795740445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6473796126659494309129493 303459193437163795740445)
                  ·
                    rfl

theorem cell23_5318862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_5318862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318862 prefixEnd_5318862 := by exact prefixLift 5318862
  have htrace : WordTrace (prefixWord ++ tailWord_5318862) baseStart_5318862 baseEnd_5318862 := by
    simpa [prefixWord, tailWord_5318862, baseEnd_5318862] using wordTrace_append hprefix tailTrace_5318862
  have hstable : (prefixWord ++ tailWord_5318862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318862).length < 2 ^ (prefixWord ++ tailWord_5318862).sum := by decide
  have hdescent : baseEnd_5318862 < baseStart_5318862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318865 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 3, 5, 2]
def baseStart_5318865 : Nat := 118140960795 + 5318865 * 2 ^ 59
def prefixEnd_5318865 : Nat := 4983230072969 + 3 ^ 40 * 5318865 * 2
def baseEnd_5318865 : Nat := 2731134281376437649926491

theorem tailTrace_5318865 : CollatzResearch.WordTrace tailWord_5318865 prefixEnd_5318865 2731134281376437649926491 := by
  unfold tailWord_5318865
  simp only [CollatzResearch.WordTrace]
  refine ⟨193994943875667969666502049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129329962583778646444334699 193994943875667969666502049)
  ·
    refine ⟨145496207906750977249876537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193994943875667969666502049 145496207906750977249876537)
    ·
      refine ⟨109122155930063232937407403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145496207906750977249876537 109122155930063232937407403)
      ·
        refine ⟨163683233895094849406111105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109122155930063232937407403 163683233895094849406111105)
        ·
          refine ⟨122762425421321137054583329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163683233895094849406111105 122762425421321137054583329)
          ·
            refine ⟨92071819065990852790937497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122762425421321137054583329 92071819065990852790937497)
            ·
              refine ⟨69053864299493139593203123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92071819065990852790937497 69053864299493139593203123)
              ·
                refine ⟨103580796449239709389804685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69053864299493139593203123 103580796449239709389804685)
                ·
                  refine ⟨38842798668464891021176757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103580796449239709389804685 38842798668464891021176757)
                  ·
                    refine ⟨3641512375168583533235321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38842798668464891021176757 3641512375168583533235321)
                    ·
                      refine ⟨2731134281376437649926491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641512375168583533235321 2731134281376437649926491)
                      ·
                        rfl

theorem cell23_5318865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_5318865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318865 prefixEnd_5318865 := by exact prefixLift 5318865
  have htrace : WordTrace (prefixWord ++ tailWord_5318865) baseStart_5318865 baseEnd_5318865 := by
    simpa [prefixWord, tailWord_5318865, baseEnd_5318865] using wordTrace_append hprefix tailTrace_5318865
  have hstable : (prefixWord ++ tailWord_5318865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318865).length < 2 ^ (prefixWord ++ tailWord_5318865).sum := by decide
  have hdescent : baseEnd_5318865 < baseStart_5318865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318876 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5318876 : Nat := 118140960795 + 5318876 * 2 ^ 59
def prefixEnd_5318876 : Nat := 4983230072969 + 3 ^ 40 * 5318876 * 2
def baseEnd_5318876 : Nat := 2731139929663637106888941

theorem tailTrace_5318876 : CollatzResearch.WordTrace tailWord_5318876 prefixEnd_5318876 2731139929663637106888941 := by
  unfold tailWord_5318876
  simp only [CollatzResearch.WordTrace]
  refine ⟨96997672539314059272576241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129330230052418745696768321 96997672539314059272576241)
  ·
    refine ⟨72748254404485544454432181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96997672539314059272576241 72748254404485544454432181)
    ·
      refine ⟨6820148850420519792603017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72748254404485544454432181 6820148850420519792603017)
      ·
        refine ⟨5115111637815389844452263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6820148850420519792603017 5115111637815389844452263)
        ·
          refine ⟨7672667456723084766678395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115111637815389844452263 7672667456723084766678395)
          ·
            refine ⟨11509001185084627150017593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672667456723084766678395 11509001185084627150017593)
            ·
              refine ⟨8631750888813470362513195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11509001185084627150017593 8631750888813470362513195)
              ·
                refine ⟨12947626333220205543769793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8631750888813470362513195 12947626333220205543769793)
                ·
                  refine ⟨9710719749915154157827345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12947626333220205543769793 9710719749915154157827345)
                  ·
                    refine ⟨7283039812436365618370509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9710719749915154157827345 7283039812436365618370509)
                    ·
                      refine ⟨2731139929663637106888941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283039812436365618370509 2731139929663637106888941)
                      ·
                        rfl

theorem cell23_5318876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5318876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318876 prefixEnd_5318876 := by exact prefixLift 5318876
  have htrace : WordTrace (prefixWord ++ tailWord_5318876) baseStart_5318876 baseEnd_5318876 := by
    simpa [prefixWord, tailWord_5318876, baseEnd_5318876] using wordTrace_append hprefix tailTrace_5318876
  have hstable : (prefixWord ++ tailWord_5318876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318876).length < 2 ^ (prefixWord ++ tailWord_5318876).sum := by decide
  have hdescent : baseEnd_5318876 < baseStart_5318876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318892 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_5318892 : Nat := 118140960795 + 5318892 * 2 ^ 59
def prefixEnd_5318892 : Nat := 4983230072969 + 3 ^ 40 * 5318892 * 2
def baseEnd_5318892 : Nat := 910382715118036348096289

theorem tailTrace_5318892 : CollatzResearch.WordTrace tailWord_5318892 prefixEnd_5318892 910382715118036348096289 := by
  unfold tailWord_5318892
  simp only [CollatzResearch.WordTrace]
  refine ⟨96997964323285076638867465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129330619097713435518489953 96997964323285076638867465)
  ·
    refine ⟨72748473242463807479150599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96997964323285076638867465 72748473242463807479150599)
    ·
      refine ⟨109122709863695711218725899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72748473242463807479150599 109122709863695711218725899)
      ·
        refine ⟨163684064795543566828088849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109122709863695711218725899 163684064795543566828088849)
        ·
          refine ⟨122763048596657675121066637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163684064795543566828088849 122763048596657675121066637)
          ·
            refine ⟨46036143223746628170399989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122763048596657675121066637 46036143223746628170399989)
            ·
              refine ⟨4315888427226246390974999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46036143223746628170399989 4315888427226246390974999)
              ·
                refine ⟨6473832640839369586462499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315888427226246390974999 6473832640839369586462499)
                ·
                  refine ⟨9710748961259054379693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473832640839369586462499 9710748961259054379693749)
                  ·
                    refine ⟨910382715118036348096289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9710748961259054379693749 910382715118036348096289)
                    ·
                      rfl

theorem cell23_5318892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_5318892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318892 prefixEnd_5318892 := by exact prefixLift 5318892
  have htrace : WordTrace (prefixWord ++ tailWord_5318892) baseStart_5318892 baseEnd_5318892 := by
    simpa [prefixWord, tailWord_5318892, baseEnd_5318892] using wordTrace_append hprefix tailTrace_5318892
  have hstable : (prefixWord ++ tailWord_5318892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318892).length < 2 ^ (prefixWord ++ tailWord_5318892).sum := by decide
  have hdescent : baseEnd_5318892 < baseStart_5318892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318906 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3]
def baseStart_5318906 : Nat := 118140960795 + 5318906 * 2 ^ 59
def prefixEnd_5318906 : Nat := 4983230072969 + 3 ^ 40 * 5318906 * 2
def baseEnd_5318906 : Nat := 2731155334083271989513803

theorem tailTrace_5318906 : CollatzResearch.WordTrace tailWord_5318906 prefixEnd_5318906 2731155334083271989513803 := by
  unfold tailWord_5318906
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499109817129858417186143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129330959512346289112496381 48499109817129858417186143)
  ·
    refine ⟨72748664725694787625779215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48499109817129858417186143 72748664725694787625779215)
    ·
      refine ⟨109122997088542181438668823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72748664725694787625779215 109122997088542181438668823)
      ·
        refine ⟨163684495632813272158003235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109122997088542181438668823 163684495632813272158003235)
        ·
          refine ⟨245526743449219908237004853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163684495632813272158003235 245526743449219908237004853)
          ·
            refine ⟨23018132198364366397219205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245526743449219908237004853 23018132198364366397219205)
            ·
              refine ⟨4315899787193318699478601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23018132198364366397219205 4315899787193318699478601)
              ·
                refine ⟨3236924840394989024608951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4315899787193318699478601 3236924840394989024608951)
                ·
                  refine ⟨4855387260592483536913427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236924840394989024608951 4855387260592483536913427)
                  ·
                    refine ⟨7283080890888725305370141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4855387260592483536913427 7283080890888725305370141)
                    ·
                      refine ⟨2731155334083271989513803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283080890888725305370141 2731155334083271989513803)
                      ·
                        rfl

theorem cell23_5318906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_5318906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318906 prefixEnd_5318906 := by exact prefixLift 5318906
  have htrace : WordTrace (prefixWord ++ tailWord_5318906) baseStart_5318906 baseEnd_5318906 := by
    simpa [prefixWord, tailWord_5318906, baseEnd_5318906] using wordTrace_append hprefix tailTrace_5318906
  have hstable : (prefixWord ++ tailWord_5318906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318906).length < 2 ^ (prefixWord ++ tailWord_5318906).sum := by decide
  have hdescent : baseEnd_5318906 < baseStart_5318906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318915 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 3]
def baseStart_5318915 : Nat := 118140960795 + 5318915 * 2 ^ 59
def prefixEnd_5318915 : Nat := 4983230072969 + 3 ^ 40 * 5318915 * 2
def baseEnd_5318915 : Nat := 2731159955409162454301261

theorem tailTrace_5318915 : CollatzResearch.WordTrace tailWord_5318915 prefixEnd_5318915 2731159955409162454301261 := by
  unfold tailWord_5318915
  simp only [CollatzResearch.WordTrace]
  refine ⟨193996767525486828205822199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129331178350324552137214799 193996767525486828205822199)
  ·
    refine ⟨290995151288230242308733299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193996767525486828205822199 290995151288230242308733299)
    ·
      refine ⟨436492726932345363463099949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290995151288230242308733299 436492726932345363463099949)
      ·
        refine ⟨163684772599629511298662481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436492726932345363463099949 163684772599629511298662481)
        ·
          refine ⟨122763579449722133473996861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163684772599629511298662481 122763579449722133473996861)
          ·
            refine ⟨46036342293645800052748823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122763579449722133473996861 46036342293645800052748823)
            ·
              refine ⟨69054513440468700079123235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46036342293645800052748823 69054513440468700079123235)
              ·
                refine ⟨103581770160703050118684853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69054513440468700079123235 103581770160703050118684853)
                ·
                  refine ⟨9710790952565910948626705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103581770160703050118684853 9710790952565910948626705)
                  ·
                    refine ⟨7283093214424433211470029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9710790952565910948626705 7283093214424433211470029)
                    ·
                      refine ⟨2731159955409162454301261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283093214424433211470029 2731159955409162454301261)
                      ·
                        rfl

theorem cell23_5318915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_5318915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318915 prefixEnd_5318915 := by exact prefixLift 5318915
  have htrace : WordTrace (prefixWord ++ tailWord_5318915) baseStart_5318915 baseEnd_5318915 := by
    simpa [prefixWord, tailWord_5318915, baseEnd_5318915] using wordTrace_append hprefix tailTrace_5318915
  have hstable : (prefixWord ++ tailWord_5318915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318915).length < 2 ^ (prefixWord ++ tailWord_5318915).sum := by decide
  have hdescent : baseEnd_5318915 < baseStart_5318915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318922 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_5318922 : Nat := 118140960795 + 5318922 * 2 ^ 59
def prefixEnd_5318922 : Nat := 4983230072969 + 3 ^ 40 * 5318922 * 2
def baseEnd_5318922 : Nat := 910387849924581308971243

theorem tailTrace_5318922 : CollatzResearch.WordTrace tailWord_5318922 prefixEnd_5318922 910387849924581308971243 := by
  unfold tailWord_5318922
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499255709115367100331755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129331348557640978934218013 48499255709115367100331755)
  ·
    refine ⟨72748883563673050650497633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48499255709115367100331755 72748883563673050650497633)
    ·
      refine ⟨54561662672754787987873225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72748883563673050650497633 54561662672754787987873225)
      ·
        refine ⟨40921247004566090990904919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54561662672754787987873225 40921247004566090990904919)
        ·
          refine ⟨61381870506849136486357379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40921247004566090990904919 61381870506849136486357379)
          ·
            refine ⟨92072805760273704729536069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61381870506849136486357379 92072805760273704729536069)
            ·
              refine ⟨17263651080051319636788013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92072805760273704729536069 17263651080051319636788013)
              ·
                refine ⟨6473869155019244863795505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17263651080051319636788013 6473869155019244863795505)
                ·
                  refine ⟨4855401866264433647846629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473869155019244863795505 4855401866264433647846629)
                  ·
                    refine ⟨910387849924581308971243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4855401866264433647846629 910387849924581308971243)
                    ·
                      rfl

theorem cell23_5318922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_5318922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318922 prefixEnd_5318922 := by exact prefixLift 5318922
  have htrace : WordTrace (prefixWord ++ tailWord_5318922) baseStart_5318922 baseEnd_5318922 := by
    simpa [prefixWord, tailWord_5318922, baseEnd_5318922] using wordTrace_append hprefix tailTrace_5318922
  have hstable : (prefixWord ++ tailWord_5318922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318922).length < 2 ^ (prefixWord ++ tailWord_5318922).sum := by decide
  have hdescent : baseEnd_5318922 < baseStart_5318922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318929 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 3, 2, 2]
def baseStart_5318929 : Nat := 118140960795 + 5318929 * 2 ^ 59
def prefixEnd_5318929 : Nat := 4983230072969 + 3 ^ 40 * 5318929 * 2
def baseEnd_5318929 : Nat := 2731167144138325399526197

theorem tailTrace_5318929 : CollatzResearch.WordTrace tailWord_5318929 prefixEnd_5318929 2731167144138325399526197 := by
  unfold tailWord_5318929
  simp only [CollatzResearch.WordTrace]
  refine ⟨193997278147436108596831841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129331518764957405731221227 193997278147436108596831841)
  ·
    refine ⟨145497958610577081447623881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193997278147436108596831841 145497958610577081447623881)
    ·
      refine ⟨109123468957932811085717911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145497958610577081447623881 109123468957932811085717911)
      ·
        refine ⟨163685203436899216628576867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109123468957932811085717911 163685203436899216628576867)
        ·
          refine ⟨245527805155348824942865301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163685203436899216628576867 245527805155348824942865301)
          ·
            refine ⟨11509115866656976169196811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 245527805155348824942865301 11509115866656976169196811)
            ·
              refine ⟨17263673799985464253795217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11509115866656976169196811 17263673799985464253795217)
              ·
                refine ⟨12947755349989098190346413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17263673799985464253795217 12947755349989098190346413)
                ·
                  refine ⟨4855408256245911821379905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12947755349989098190346413 4855408256245911821379905)
                  ·
                    refine ⟨3641556192184433866034929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855408256245911821379905 3641556192184433866034929)
                    ·
                      refine ⟨2731167144138325399526197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641556192184433866034929 2731167144138325399526197)
                      ·
                        rfl

theorem cell23_5318929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_5318929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318929 prefixEnd_5318929 := by exact prefixLift 5318929
  have htrace : WordTrace (prefixWord ++ tailWord_5318929) baseStart_5318929 baseEnd_5318929 := by
    simpa [prefixWord, tailWord_5318929, baseEnd_5318929] using wordTrace_append hprefix tailTrace_5318929
  have hstable : (prefixWord ++ tailWord_5318929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318929).length < 2 ^ (prefixWord ++ tailWord_5318929).sum := by decide
  have hdescent : baseEnd_5318929 < baseStart_5318929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318946 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_5318946 : Nat := 118140960795 + 5318946 * 2 ^ 59
def prefixEnd_5318946 : Nat := 4983230072969 + 3 ^ 40 * 5318946 * 2
def baseEnd_5318946 : Nat := 2731175873309451833013619

theorem tailTrace_5318946 : CollatzResearch.WordTrace tailWord_5318946 prefixEnd_5318946 2731175873309451833013619 := by
  unfold tailWord_5318946
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499474547093630125050173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129331932125583013666800461 48499474547093630125050173)
  ·
    refine ⟨18187302955160111296893815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48499474547093630125050173 18187302955160111296893815)
    ·
      refine ⟨27280954432740166945340723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18187302955160111296893815 27280954432740166945340723)
      ·
        refine ⟨40921431649110250418011085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27280954432740166945340723 40921431649110250418011085)
        ·
          refine ⟨15345536868416343906754157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40921431649110250418011085 15345536868416343906754157)
          ·
            refine ⟨5754576325656128965032809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15345536868416343906754157 5754576325656128965032809)
            ·
              refine ⟨4315932244242096723774607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5754576325656128965032809 4315932244242096723774607)
              ·
                refine ⟨6473898366363145085661911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315932244242096723774607 6473898366363145085661911)
                ·
                  refine ⟨9710847549544717628492867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473898366363145085661911 9710847549544717628492867)
                  ·
                    refine ⟨14566271324317076442739301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9710847549544717628492867 14566271324317076442739301)
                    ·
                      refine ⟨2731175873309451833013619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14566271324317076442739301 2731175873309451833013619)
                      ·
                        rfl

theorem cell23_5318946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_5318946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318946 prefixEnd_5318946 := by exact prefixLift 5318946
  have htrace : WordTrace (prefixWord ++ tailWord_5318946) baseStart_5318946 baseEnd_5318946 := by
    simpa [prefixWord, tailWord_5318946, baseEnd_5318946] using wordTrace_append hprefix tailTrace_5318946
  have hstable : (prefixWord ++ tailWord_5318946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318946).length < 2 ^ (prefixWord ++ tailWord_5318946).sum := by decide
  have hdescent : baseEnd_5318946 < baseStart_5318946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5318949 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_5318949 : Nat := 118140960795 + 5318949 * 2 ^ 59
def prefixEnd_5318949 : Nat := 4983230072969 + 3 ^ 40 * 5318949 * 2
def baseEnd_5318949 : Nat := 2731177413751415321276105

theorem tailTrace_5318949 : CollatzResearch.WordTrace tailWord_5318949 prefixEnd_5318949 2731177413751415321276105 := by
  unfold tailWord_5318949
  simp only [CollatzResearch.WordTrace]
  refine ⟨193998007607363652012559901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129332005071575768008373267 193998007607363652012559901)
  ·
    refine ⟨72749252852761369504709963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193998007607363652012559901 72749252852761369504709963)
    ·
      refine ⟨109123879279142054257064945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72749252852761369504709963 109123879279142054257064945)
      ·
        refine ⟨81842909459356540692798709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109123879279142054257064945 81842909459356540692798709)
        ·
          refine ⟨7672772761814675689949879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81842909459356540692798709 7672772761814675689949879)
          ·
            refine ⟨11509159142722013534924819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672772761814675689949879 11509159142722013534924819)
            ·
              refine ⟨17263738714083020302387229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11509159142722013534924819 17263738714083020302387229)
              ·
                refine ⟨6473902017781132613395211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17263738714083020302387229 6473902017781132613395211)
                ·
                  refine ⟨9710853026671698920092817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473902017781132613395211 9710853026671698920092817)
                  ·
                    refine ⟨7283139770003774190069613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9710853026671698920092817 7283139770003774190069613)
                    ·
                      refine ⟨2731177413751415321276105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283139770003774190069613 2731177413751415321276105)
                      ·
                        rfl

theorem cell23_5318949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_5318949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5318949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5318949 prefixEnd_5318949 := by exact prefixLift 5318949
  have htrace : WordTrace (prefixWord ++ tailWord_5318949) baseStart_5318949 baseEnd_5318949 := by
    simpa [prefixWord, tailWord_5318949, baseEnd_5318949] using wordTrace_append hprefix tailTrace_5318949
  have hstable : (prefixWord ++ tailWord_5318949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5318949).length < 2 ^ (prefixWord ++ tailWord_5318949).sum := by decide
  have hdescent : baseEnd_5318949 < baseStart_5318949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5318949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319002 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2]
def baseStart_5319002 : Nat := 118140960795 + 5319002 * 2 ^ 59
def prefixEnd_5319002 : Nat := 4983230072969 + 3 ^ 40 * 5319002 * 2
def baseEnd_5319002 : Nat := 2731204628226103613913361

theorem tailTrace_5319002 : CollatzResearch.WordTrace tailWord_5319002 prefixEnd_5319002 2731204628226103613913361 := by
  unfold tailWord_5319002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499985169042910516059815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129333293784114428042826173 48499985169042910516059815)
  ·
    refine ⟨72749977753564365774089723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48499985169042910516059815 72749977753564365774089723)
    ·
      refine ⟨109124966630346548661134585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72749977753564365774089723 109124966630346548661134585)
      ·
        refine ⟨81843724972759911495850939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109124966630346548661134585 81843724972759911495850939)
        ·
          refine ⟨122765587459139867243776409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81843724972759911495850939 122765587459139867243776409)
          ·
            refine ⟨92074190594354900432832307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122765587459139867243776409 92074190594354900432832307)
            ·
              refine ⟨138111285891532350649248461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92074190594354900432832307 138111285891532350649248461)
              ·
                refine ⟨51791732209324631493468173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138111285891532350649248461 51791732209324631493468173)
                ·
                  refine ⟨19421899578496736810050565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51791732209324631493468173 19421899578496736810050565)
                  ·
                    refine ⟨3641606170968138151884481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19421899578496736810050565 3641606170968138151884481)
                    ·
                      refine ⟨2731204628226103613913361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641606170968138151884481 2731204628226103613913361)
                      ·
                        rfl

theorem cell23_5319002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_5319002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319002 prefixEnd_5319002 := by exact prefixLift 5319002
  have htrace : WordTrace (prefixWord ++ tailWord_5319002) baseStart_5319002 baseEnd_5319002 := by
    simpa [prefixWord, tailWord_5319002, baseEnd_5319002] using wordTrace_append hprefix tailTrace_5319002
  have hstable : (prefixWord ++ tailWord_5319002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319002).length < 2 ^ (prefixWord ++ tailWord_5319002).sum := by decide
  have hdescent : baseEnd_5319002 < baseStart_5319002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319065 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_5319065 : Nat := 118140960795 + 5319065 * 2 ^ 59
def prefixEnd_5319065 : Nat := 4983230072969 + 3 ^ 40 * 5319065 * 2
def baseEnd_5319065 : Nat := 2731236977507336867425571

theorem tailTrace_5319065 : CollatzResearch.WordTrace tailWord_5319065 prefixEnd_5319065 2731236977507336867425571 := by
  unfold tailWord_5319065
  simp only [CollatzResearch.WordTrace]
  refine ⟨194002238474943403823782649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129334825649962269215855099 194002238474943403823782649)
  ·
    refine ⟨145501678856207552867836987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194002238474943403823782649 145501678856207552867836987)
    ·
      refine ⟨218252518284311329301755481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145501678856207552867836987 218252518284311329301755481)
      ·
        refine ⟨163689388713233496976316611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218252518284311329301755481 163689388713233496976316611)
        ·
          refine ⟨245534083069850245464474917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163689388713233496976316611 245534083069850245464474917)
          ·
            refine ⟨46037640575596921024589047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245534083069850245464474917 46037640575596921024589047)
            ·
              refine ⟨69056460863395381536883571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46037640575596921024589047 69056460863395381536883571)
              ·
                refine ⟨103584691295093072305325357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69056460863395381536883571 103584691295093072305325357)
                ·
                  refine ⟨38844259235659902114497009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103584691295093072305325357 38844259235659902114497009)
                  ·
                    refine ⟨29133194426744926585872757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38844259235659902114497009 29133194426744926585872757)
                    ·
                      refine ⟨2731236977507336867425571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29133194426744926585872757 2731236977507336867425571)
                      ·
                        rfl

theorem cell23_5319065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_5319065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319065 prefixEnd_5319065 := by exact prefixLift 5319065
  have htrace : WordTrace (prefixWord ++ tailWord_5319065) baseStart_5319065 baseEnd_5319065 := by
    simpa [prefixWord, tailWord_5319065, baseEnd_5319065] using wordTrace_append hprefix tailTrace_5319065
  have hstable : (prefixWord ++ tailWord_5319065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319065).length < 2 ^ (prefixWord ++ tailWord_5319065).sum := by decide
  have hdescent : baseEnd_5319065 < baseStart_5319065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319070 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5319070 : Nat := 118140960795 + 5319070 * 2 ^ 59
def prefixEnd_5319070 : Nat := 4983230072969 + 3 ^ 40 * 5319070 * 2
def baseEnd_5319070 : Nat := 2731239544910609347863049

theorem tailTrace_5319070 : CollatzResearch.WordTrace tailWord_5319070 prefixEnd_5319070 2731239544910609347863049 := by
  unfold tailWord_5319070
  simp only [CollatzResearch.WordTrace]
  refine ⟨24250302604990661209714333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129334947226616859785143109 24250302604990661209714333)
  ·
    refine ⟨9093863476871497953642875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24250302604990661209714333 9093863476871497953642875)
    ·
      refine ⟨13640795215307246930464313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093863476871497953642875 13640795215307246930464313)
      ·
        refine ⟨10230596411480435197848235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13640795215307246930464313 10230596411480435197848235)
        ·
          refine ⟨15345894617220652796772353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10230596411480435197848235 15345894617220652796772353)
          ·
            refine ⟨11509420962915489597579265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15345894617220652796772353 11509420962915489597579265)
            ·
              refine ⟨8632065722186617198184449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11509420962915489597579265 8632065722186617198184449)
              ·
                refine ⟨6474049291639962898638337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8632065722186617198184449 6474049291639962898638337)
                ·
                  refine ⟨4855536968729972173978753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6474049291639962898638337 4855536968729972173978753)
                  ·
                    refine ⟨3641652726547479130484065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855536968729972173978753 3641652726547479130484065)
                    ·
                      refine ⟨2731239544910609347863049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641652726547479130484065 2731239544910609347863049)
                      ·
                        rfl

theorem cell23_5319070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5319070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319070 prefixEnd_5319070 := by exact prefixLift 5319070
  have htrace : WordTrace (prefixWord ++ tailWord_5319070) baseStart_5319070 baseEnd_5319070 := by
    simpa [prefixWord, tailWord_5319070, baseEnd_5319070] using wordTrace_append hprefix tailTrace_5319070
  have hstable : (prefixWord ++ tailWord_5319070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319070).length < 2 ^ (prefixWord ++ tailWord_5319070).sum := by decide
  have hdescent : baseEnd_5319070 < baseStart_5319070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319072 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_5319072 : Nat := 118140960795 + 5319072 * 2 ^ 59
def prefixEnd_5319072 : Nat := 4983230072969 + 3 ^ 40 * 5319072 * 2
def baseEnd_5319072 : Nat := 910413523957306113346013

theorem tailTrace_5319072 : CollatzResearch.WordTrace tailWord_5319072 prefixEnd_5319072 910413523957306113346013 := by
  unfold tailWord_5319072
  simp only [CollatzResearch.WordTrace]
  refine ⟨97001246892959022009643735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129334995857278696012858313 97001246892959022009643735)
  ·
    refine ⟨145501870339438533014465603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97001246892959022009643735 145501870339438533014465603)
    ·
      refine ⟨218252805509157799521698405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145501870339438533014465603 218252805509157799521698405)
      ·
        refine ⟨40922401032967087410318451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218252805509157799521698405 40922401032967087410318451)
        ·
          refine ⟨61383601549450631115477677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40922401032967087410318451 61383601549450631115477677)
          ·
            refine ⟨23018850581043986668304129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61383601549450631115477677 23018850581043986668304129)
            ·
              refine ⟨17264137935782990001228097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23018850581043986668304129 17264137935782990001228097)
              ·
                refine ⟨12948103451837242500921073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17264137935782990001228097 12948103451837242500921073)
                ·
                  refine ⟨9711077588877931875690805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12948103451837242500921073 9711077588877931875690805)
                  ·
                    refine ⟨910413523957306113346013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9711077588877931875690805 910413523957306113346013)
                    ·
                      rfl

theorem cell23_5319072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_5319072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319072 prefixEnd_5319072 := by exact prefixLift 5319072
  have htrace : WordTrace (prefixWord ++ tailWord_5319072) baseStart_5319072 baseEnd_5319072 := by
    simpa [prefixWord, tailWord_5319072, baseEnd_5319072] using wordTrace_append hprefix tailTrace_5319072
  have hstable : (prefixWord ++ tailWord_5319072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319072).length < 2 ^ (prefixWord ++ tailWord_5319072).sum := by decide
  have hdescent : baseEnd_5319072 < baseStart_5319072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319079 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_5319079 : Nat := 118140960795 + 5319079 * 2 ^ 59
def prefixEnd_5319079 : Nat := 4983230072969 + 3 ^ 40 * 5319079 * 2
def baseEnd_5319079 : Nat := 2731244166236499812650507

theorem tailTrace_5319079 : CollatzResearch.WordTrace tailWord_5319079 prefixEnd_5319079 2731244166236499812650507 := by
  unfold tailWord_5319079
  simp only [CollatzResearch.WordTrace]
  refine ⟨194002749096892684214792291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129335166064595122809861527 194002749096892684214792291)
  ·
    refine ⟨291004123645339026322188437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194002749096892684214792291 291004123645339026322188437)
    ·
      refine ⟨13640818295875266858852583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 291004123645339026322188437 13640818295875266858852583)
      ·
        refine ⟨20461227443812900288278875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13640818295875266858852583 20461227443812900288278875)
        ·
          refine ⟨30691841165719350432418313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20461227443812900288278875 30691841165719350432418313)
          ·
            refine ⟨23018880874289512824313735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30691841165719350432418313 23018880874289512824313735)
            ·
              refine ⟨34528321311434269236470603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23018880874289512824313735 34528321311434269236470603)
              ·
                refine ⟨51792481967151403854705905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34528321311434269236470603 51792481967151403854705905)
                ·
                  refine ⟨38844361475363552891029429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51792481967151403854705905 38844361475363552891029429)
                  ·
                    refine ⟨3641658888315333083534009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38844361475363552891029429 3641658888315333083534009)
                    ·
                      refine ⟨2731244166236499812650507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641658888315333083534009 2731244166236499812650507)
                      ·
                        rfl

theorem cell23_5319079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_5319079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319079 prefixEnd_5319079 := by exact prefixLift 5319079
  have htrace : WordTrace (prefixWord ++ tailWord_5319079) baseStart_5319079 baseEnd_5319079 := by
    simpa [prefixWord, tailWord_5319079, baseEnd_5319079] using wordTrace_append hprefix tailTrace_5319079
  have hstable : (prefixWord ++ tailWord_5319079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319079).length < 2 ^ (prefixWord ++ tailWord_5319079).sum := by decide
  have hdescent : baseEnd_5319079 < baseStart_5319079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319115 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 8]
def baseStart_5319115 : Nat := 118140960795 + 5319115 * 2 ^ 59
def prefixEnd_5319115 : Nat := 4983230072969 + 3 ^ 40 * 5319115 * 2
def baseEnd_5319115 : Nat := 303473627948895741311149

theorem tailTrace_5319115 : CollatzResearch.WordTrace tailWord_5319115 prefixEnd_5319115 303473627948895741311149 := by
  unfold tailWord_5319115
  simp only [CollatzResearch.WordTrace]
  refine ⟨194004062124762262363102799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129336041416508174908735199 194004062124762262363102799)
  ·
    refine ⟨291006093187143393544654199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194004062124762262363102799 291006093187143393544654199)
    ·
      refine ⟨436509139780715090316981299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291006093187143393544654199 436509139780715090316981299)
      ·
        refine ⟨654763709671072635475471949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436509139780715090316981299 654763709671072635475471949)
        ·
          refine ⟨245536391126652238303301981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 654763709671072635475471949 245536391126652238303301981)
          ·
            refine ⟨92076146672494589363738243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245536391126652238303301981 92076146672494589363738243)
            ·
              refine ⟨138114220008741884045607365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92076146672494589363738243 138114220008741884045607365)
              ·
                refine ⟨25896416251639103258551381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138114220008741884045607365 25896416251639103258551381)
                ·
                  refine ⟨303473627948895741311149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25896416251639103258551381 303473627948895741311149)
                  ·
                    rfl

theorem cell23_5319115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 8].length) (baseStart_5319115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319115 prefixEnd_5319115 := by exact prefixLift 5319115
  have htrace : WordTrace (prefixWord ++ tailWord_5319115) baseStart_5319115 baseEnd_5319115 := by
    simpa [prefixWord, tailWord_5319115, baseEnd_5319115] using wordTrace_append hprefix tailTrace_5319115
  have hstable : (prefixWord ++ tailWord_5319115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319115).length < 2 ^ (prefixWord ++ tailWord_5319115).sum := by decide
  have hdescent : baseEnd_5319115 < baseStart_5319115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319126 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_5319126 : Nat := 118140960795 + 5319126 * 2 ^ 59
def prefixEnd_5319126 : Nat := 4983230072969 + 3 ^ 40 * 5319126 * 2
def baseEnd_5319126 : Nat := 2731268299827261128762791

theorem tailTrace_5319126 : CollatzResearch.WordTrace tailWord_5319126 prefixEnd_5319126 2731268299827261128762791 := by
  unfold tailWord_5319126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125278957982650702609577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129336308885148274161168821 12125278957982650702609577)
  ·
    refine ⟨9093959218486988026957183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12125278957982650702609577 9093959218486988026957183)
    ·
      refine ⟨13640938827730482040435775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093959218486988026957183 13640938827730482040435775)
      ·
        refine ⟨20461408241595723060653663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13640938827730482040435775 20461408241595723060653663)
        ·
          refine ⟨30692112362393584590980495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20461408241595723060653663 30692112362393584590980495)
          ·
            refine ⟨46038168543590376886470743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30692112362393584590980495 46038168543590376886470743)
            ·
              refine ⟨69057252815385565329706115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46038168543590376886470743 69057252815385565329706115)
              ·
                refine ⟨103585879223078347994559173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69057252815385565329706115 103585879223078347994559173)
                ·
                  refine ⟨19422352354327190248979845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103585879223078347994559173 19422352354327190248979845)
                  ·
                    refine ⟨3641691066436348171683721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19422352354327190248979845 3641691066436348171683721)
                    ·
                      refine ⟨2731268299827261128762791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641691066436348171683721 2731268299827261128762791)
                      ·
                        rfl

theorem cell23_5319126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_5319126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319126 prefixEnd_5319126 := by exact prefixLift 5319126
  have htrace : WordTrace (prefixWord ++ tailWord_5319126) baseStart_5319126 baseEnd_5319126 := by
    simpa [prefixWord, tailWord_5319126, baseEnd_5319126] using wordTrace_append hprefix tailTrace_5319126
  have hstable : (prefixWord ++ tailWord_5319126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319126).length < 2 ^ (prefixWord ++ tailWord_5319126).sum := by decide
  have hdescent : baseEnd_5319126 < baseStart_5319126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319145 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_5319145 : Nat := 118140960795 + 5319145 * 2 ^ 59
def prefixEnd_5319145 : Nat := 4983230072969 + 3 ^ 40 * 5319145 * 2
def baseEnd_5319145 : Nat := 910426018653232184808401

theorem tailTrace_5319145 : CollatzResearch.WordTrace tailWord_5319145 prefixEnd_5319145 910426018653232184808401 := by
  unfold tailWord_5319145
  simp only [CollatzResearch.WordTrace]
  refine ⟨194005156314653577486694889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129336770876435718324463259 194005156314653577486694889)
  ·
    refine ⟨145503867235990183115021167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194005156314653577486694889 145503867235990183115021167)
    ·
      refine ⟨218255800853985274672531751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145503867235990183115021167 218255800853985274672531751)
      ·
        refine ⟨327383701280977912008797627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218255800853985274672531751 327383701280977912008797627)
        ·
          refine ⟨491075551921466868013196441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327383701280977912008797627 491075551921466868013196441)
          ·
            refine ⟨368306663941100151009897331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491075551921466868013196441 368306663941100151009897331)
            ·
              refine ⟨552459995911650226514845997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368306663941100151009897331 552459995911650226514845997)
              ·
                refine ⟨207172498466868834943067249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552459995911650226514845997 207172498466868834943067249)
                ·
                  refine ⟨155379373850151626207300437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207172498466868834943067249 155379373850151626207300437)
                  ·
                    refine ⟨910426018653232184808401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155379373850151626207300437 910426018653232184808401)
                    ·
                      rfl

theorem cell23_5319145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_5319145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319145 prefixEnd_5319145 := by exact prefixLift 5319145
  have htrace : WordTrace (prefixWord ++ tailWord_5319145) baseStart_5319145 baseEnd_5319145 := by
    simpa [prefixWord, tailWord_5319145, baseEnd_5319145] using wordTrace_append hprefix tailTrace_5319145
  have hstable : (prefixWord ++ tailWord_5319145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319145).length < 2 ^ (prefixWord ++ tailWord_5319145).sum := by decide
  have hdescent : baseEnd_5319145 < baseStart_5319145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319179 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 1, 5]
def baseStart_5319179 : Nat := 118140960795 + 5319179 * 2 ^ 59
def prefixEnd_5319179 : Nat := 4983230072969 + 3 ^ 40 * 5319179 * 2
def baseEnd_5319179 : Nat := 910431838100649807133349

theorem tailTrace_5319179 : CollatzResearch.WordTrace tailWord_5319179 prefixEnd_5319179 910431838100649807133349 := by
  unfold tailWord_5319179
  simp only [CollatzResearch.WordTrace]
  refine ⟨194006396396530401293432591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129337597597686934195621727 194006396396530401293432591)
  ·
    refine ⟨291009594594795601940148887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194006396396530401293432591 291009594594795601940148887)
    ·
      refine ⟨436514391892193402910223331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291009594594795601940148887 436514391892193402910223331)
      ·
        refine ⟨654771587838290104365334997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436514391892193402910223331 654771587838290104365334997)
        ·
          refine ⟨15346209089959924321062539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 654771587838290104365334997 15346209089959924321062539)
          ·
            refine ⟨23019313634939886481593809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15346209089959924321062539 23019313634939886481593809)
            ·
              refine ⟨17264485226204914861195357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23019313634939886481593809 17264485226204914861195357)
              ·
                refine ⟨6474181959826843072948259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17264485226204914861195357 6474181959826843072948259)
                ·
                  refine ⟨9711272939740264609422389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474181959826843072948259 9711272939740264609422389)
                  ·
                    refine ⟨910431838100649807133349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9711272939740264609422389 910431838100649807133349)
                    ·
                      rfl

theorem cell23_5319179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 5].length) (baseStart_5319179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319179 prefixEnd_5319179 := by exact prefixLift 5319179
  have htrace : WordTrace (prefixWord ++ tailWord_5319179) baseStart_5319179 baseEnd_5319179 := by
    simpa [prefixWord, tailWord_5319179, baseEnd_5319179] using wordTrace_append hprefix tailTrace_5319179
  have hstable : (prefixWord ++ tailWord_5319179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319179).length < 2 ^ (prefixWord ++ tailWord_5319179).sum := by decide
  have hdescent : baseEnd_5319179 < baseStart_5319179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319212 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_5319212 : Nat := 118140960795 + 5319212 * 2 ^ 59
def prefixEnd_5319212 : Nat := 4983230072969 + 3 ^ 40 * 5319212 * 2
def baseEnd_5319212 : Nat := 2731312459163547792287395

theorem tailTrace_5319212 : CollatzResearch.WordTrace tailWord_5319212 prefixEnd_5319212 2731312459163547792287395 := by
  unfold tailWord_5319212
  simp only [CollatzResearch.WordTrace]
  refine ⟨97003800002705423964691945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129338400003607231952922593 97003800002705423964691945)
  ·
    refine ⟨72752850002029067973518959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97003800002705423964691945 72752850002029067973518959)
    ·
      refine ⟨109129275003043601960278439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72752850002029067973518959 109129275003043601960278439)
      ·
        refine ⟨163693912504565402940417659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109129275003043601960278439 163693912504565402940417659)
        ·
          refine ⟨245540868756848104410626489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163693912504565402940417659 245540868756848104410626489)
          ·
            refine ⟨184155651567636078307969867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245540868756848104410626489 184155651567636078307969867)
            ·
              refine ⟨276233477351454117461954801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184155651567636078307969867 276233477351454117461954801)
              ·
                refine ⟨207175108013590588096466101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276233477351454117461954801 207175108013590588096466101)
                ·
                  refine ⟨19422666376274117634043697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207175108013590588096466101 19422666376274117634043697)
                  ·
                    refine ⟨14566999782205588225532773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19422666376274117634043697 14566999782205588225532773)
                    ·
                      refine ⟨2731312459163547792287395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14566999782205588225532773 2731312459163547792287395)
                      ·
                        rfl

theorem cell23_5319212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_5319212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319212 prefixEnd_5319212 := by exact prefixLift 5319212
  have htrace : WordTrace (prefixWord ++ tailWord_5319212) baseStart_5319212 baseEnd_5319212 := by
    simpa [prefixWord, tailWord_5319212, baseEnd_5319212] using wordTrace_append hprefix tailTrace_5319212
  have hstable : (prefixWord ++ tailWord_5319212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319212).length < 2 ^ (prefixWord ++ tailWord_5319212).sum := by decide
  have hdescent : baseEnd_5319212 < baseStart_5319212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319216 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 3, 2, 2]
def baseStart_5319216 : Nat := 118140960795 + 5319216 * 2 ^ 59
def prefixEnd_5319216 : Nat := 4983230072969 + 3 ^ 40 * 5319216 * 2
def baseEnd_5319216 : Nat := 2731314513086165776637377

theorem tailTrace_5319216 : CollatzResearch.WordTrace tailWord_5319216 prefixEnd_5319216 2731314513086165776637377 := by
  unfold tailWord_5319216
  simp only [CollatzResearch.WordTrace]
  refine ⟨97003872948698178306264751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129338497264930904408353001 97003872948698178306264751)
  ·
    refine ⟨145505809423047267459397127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97003872948698178306264751 145505809423047267459397127)
    ·
      refine ⟨218258714134570901189095691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145505809423047267459397127 218258714134570901189095691)
      ·
        refine ⟨327388071201856351783643537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218258714134570901189095691 327388071201856351783643537)
        ·
          refine ⟨245541053401392263837732653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327388071201856351783643537 245541053401392263837732653)
          ·
            refine ⟨92077895025522098939149745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245541053401392263837732653 92077895025522098939149745)
            ·
              refine ⟨69058421269141574204362309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92077895025522098939149745 69058421269141574204362309)
              ·
                refine ⟨12948453987964045163317933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69058421269141574204362309 12948453987964045163317933)
                ·
                  refine ⟨4855670245486516936244225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12948453987964045163317933 4855670245486516936244225)
                  ·
                    refine ⟨3641752684114887702183169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855670245486516936244225 3641752684114887702183169)
                    ·
                      refine ⟨2731314513086165776637377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641752684114887702183169 2731314513086165776637377)
                      ·
                        rfl

theorem cell23_5319216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 2, 2].length) (baseStart_5319216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319216 prefixEnd_5319216 := by exact prefixLift 5319216
  have htrace : WordTrace (prefixWord ++ tailWord_5319216) baseStart_5319216 baseEnd_5319216 := by
    simpa [prefixWord, tailWord_5319216, baseEnd_5319216] using wordTrace_append hprefix tailTrace_5319216
  have hstable : (prefixWord ++ tailWord_5319216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319216).length < 2 ^ (prefixWord ++ tailWord_5319216).sum := by decide
  have hdescent : baseEnd_5319216 < baseStart_5319216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319219 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 3]
def baseStart_5319219 : Nat := 118140960795 + 5319219 * 2 ^ 59
def prefixEnd_5319219 : Nat := 4983230072969 + 3 ^ 40 * 5319219 * 2
def baseEnd_5319219 : Nat := 2731316053528129264899863

theorem tailTrace_5319219 : CollatzResearch.WordTrace tailWord_5319219 prefixEnd_5319219 2731316053528129264899863 := by
  unfold tailWord_5319219
  simp only [CollatzResearch.WordTrace]
  refine ⟨194007855316385488124888711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129338570210923658749925807 194007855316385488124888711)
  ·
    refine ⟨291011782974578232187333067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194007855316385488124888711 291011782974578232187333067)
    ·
      refine ⟨436517674461867348280999601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291011782974578232187333067 436517674461867348280999601)
      ·
        refine ⟨327388255846400511210749701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436517674461867348280999601 327388255846400511210749701)
        ·
          refine ⟨61385297971200095852015569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327388255846400511210749701 61385297971200095852015569)
          ·
            refine ⟨46038973478400071889011677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61385297971200095852015569 46038973478400071889011677)
            ·
              refine ⟨17264615054400026958379379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46038973478400071889011677 17264615054400026958379379)
              ·
                refine ⟨25896922581600040437569069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17264615054400026958379379 25896922581600040437569069)
                ·
                  refine ⟨9711345968100015164088401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25896922581600040437569069 9711345968100015164088401)
                  ·
                    refine ⟨7283509476075011373066301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9711345968100015164088401 7283509476075011373066301)
                    ·
                      refine ⟨2731316053528129264899863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283509476075011373066301 2731316053528129264899863)
                      ·
                        rfl

theorem cell23_5319219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_5319219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319219 prefixEnd_5319219 := by exact prefixLift 5319219
  have htrace : WordTrace (prefixWord ++ tailWord_5319219) baseStart_5319219 baseEnd_5319219 := by
    simpa [prefixWord, tailWord_5319219, baseEnd_5319219] using wordTrace_append hprefix tailTrace_5319219
  have hstable : (prefixWord ++ tailWord_5319219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319219).length < 2 ^ (prefixWord ++ tailWord_5319219).sum := by decide
  have hdescent : baseEnd_5319219 < baseStart_5319219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319229 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5319229 : Nat := 118140960795 + 5319229 * 2 ^ 59
def prefixEnd_5319229 : Nat := 4983230072969 + 3 ^ 40 * 5319229 * 2
def baseEnd_5319229 : Nat := 2731321188334674225774817

theorem tailTrace_5319229 : CollatzResearch.WordTrace tailWord_5319229 prefixEnd_5319229 2731321188334674225774817 := by
  unfold tailWord_5319229
  simp only [CollatzResearch.WordTrace]
  refine ⟨194008220046349259832752741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129338813364232839888501827 194008220046349259832752741)
  ·
    refine ⟨36376541258690486218641139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194008220046349259832752741 36376541258690486218641139)
    ·
      refine ⟨54564811888035729327961709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36376541258690486218641139 54564811888035729327961709)
      ·
        refine ⟨20461804458013398497985641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54564811888035729327961709 20461804458013398497985641)
        ·
          refine ⟨15346353343510048873489231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20461804458013398497985641 15346353343510048873489231)
          ·
            refine ⟨23019530015265073310233847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15346353343510048873489231 23019530015265073310233847)
            ·
              refine ⟨34529295022897609965350771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23019530015265073310233847 34529295022897609965350771)
              ·
                refine ⟨51793942534346414948026157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34529295022897609965350771 51793942534346414948026157)
                ·
                  refine ⟨19422728450379905605509809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51793942534346414948026157 19422728450379905605509809)
                  ·
                    refine ⟨14567046337784929204132357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19422728450379905605509809 14567046337784929204132357)
                    ·
                      refine ⟨2731321188334674225774817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14567046337784929204132357 2731321188334674225774817)
                      ·
                        rfl

theorem cell23_5319229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5319229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319229 prefixEnd_5319229 := by exact prefixLift 5319229
  have htrace : WordTrace (prefixWord ++ tailWord_5319229) baseStart_5319229 baseEnd_5319229 := by
    simpa [prefixWord, tailWord_5319229, baseEnd_5319229] using wordTrace_append hprefix tailTrace_5319229
  have hstable : (prefixWord ++ tailWord_5319229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319229).length < 2 ^ (prefixWord ++ tailWord_5319229).sum := by decide
  have hdescent : baseEnd_5319229 < baseStart_5319229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319230 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_5319230 : Nat := 118140960795 + 5319230 * 2 ^ 59
def prefixEnd_5319230 : Nat := 4983230072969 + 3 ^ 40 * 5319230 * 2
def baseEnd_5319230 : Nat := 910440567271776240620771

theorem tailTrace_5319230 : CollatzResearch.WordTrace tailWord_5319230 prefixEnd_5319230 910440567271776240620771 := by
  unfold tailWord_5319230
  simp only [CollatzResearch.WordTrace]
  refine ⟨24251032064918204625442393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129338837679563758002359429 24251032064918204625442393)
  ·
    refine ⟨18188274048688653469081795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24251032064918204625442393 18188274048688653469081795)
    ·
      refine ⟨27282411073032980203622693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18188274048688653469081795 27282411073032980203622693)
      ·
        refine ⟨5115452076193683788179255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27282411073032980203622693 5115452076193683788179255)
        ·
          refine ⟨7673178114290525682268883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115452076193683788179255 7673178114290525682268883)
          ·
            refine ⟨11509767171435788523403325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7673178114290525682268883 11509767171435788523403325)
            ·
              refine ⟨4316162689288420696276247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11509767171435788523403325 4316162689288420696276247)
              ·
                refine ⟨6474244033932631044414371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316162689288420696276247 6474244033932631044414371)
                ·
                  refine ⟨9711366050898946566621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474244033932631044414371 9711366050898946566621557)
                  ·
                    refine ⟨910440567271776240620771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9711366050898946566621557 910440567271776240620771)
                    ·
                      rfl

theorem cell23_5319230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_5319230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319230 prefixEnd_5319230 := by exact prefixLift 5319230
  have htrace : WordTrace (prefixWord ++ tailWord_5319230) baseStart_5319230 baseEnd_5319230 := by
    simpa [prefixWord, tailWord_5319230, baseEnd_5319230] using wordTrace_append hprefix tailTrace_5319230
  have hstable : (prefixWord ++ tailWord_5319230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319230).length < 2 ^ (prefixWord ++ tailWord_5319230).sum := by decide
  have hdescent : baseEnd_5319230 < baseStart_5319230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319233 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5319233 : Nat := 118140960795 + 5319233 * 2 ^ 59
def prefixEnd_5319233 : Nat := 4983230072969 + 3 ^ 40 * 5319233 * 2
def baseEnd_5319233 : Nat := 2731323242257292210124799

theorem tailTrace_5319233 : CollatzResearch.WordTrace tailWord_5319233 prefixEnd_5319233 2731323242257292210124799 := by
  unfold tailWord_5319233
  simp only [CollatzResearch.WordTrace]
  refine ⟨194008365938334768515898353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129338910625556512343932235 194008365938334768515898353)
  ·
    refine ⟨145506274453751076386923765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194008365938334768515898353 145506274453751076386923765)
    ·
      refine ⟨13641213230039163411274103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145506274453751076386923765 13641213230039163411274103)
      ·
        refine ⟨20461819845058745116911155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13641213230039163411274103 20461819845058745116911155)
        ·
          refine ⟨30692729767588117675366733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20461819845058745116911155 30692729767588117675366733)
          ·
            refine ⟨11509773662845544128262525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30692729767588117675366733 11509773662845544128262525)
            ·
              refine ⟨4316165123567079048098447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11509773662845544128262525 4316165123567079048098447)
              ·
                refine ⟨6474247685350618572147671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316165123567079048098447 6474247685350618572147671)
                ·
                  refine ⟨9711371528025927858221507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474247685350618572147671 9711371528025927858221507)
                  ·
                    refine ⟨14567057292038891787332261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9711371528025927858221507 14567057292038891787332261)
                    ·
                      refine ⟨2731323242257292210124799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14567057292038891787332261 2731323242257292210124799)
                      ·
                        rfl

theorem cell23_5319233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5319233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319233 prefixEnd_5319233 := by exact prefixLift 5319233
  have htrace : WordTrace (prefixWord ++ tailWord_5319233) baseStart_5319233 baseEnd_5319233 := by
    simpa [prefixWord, tailWord_5319233, baseEnd_5319233] using wordTrace_append hprefix tailTrace_5319233
  have hstable : (prefixWord ++ tailWord_5319233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319233).length < 2 ^ (prefixWord ++ tailWord_5319233).sum := by decide
  have hdescent : baseEnd_5319233 < baseStart_5319233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319250 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_5319250 : Nat := 118140960795 + 5319250 * 2 ^ 59
def prefixEnd_5319250 : Nat := 4983230072969 + 3 ^ 40 * 5319250 * 2
def baseEnd_5319250 : Nat := 2731331971428418643612221

theorem tailTrace_5319250 : CollatzResearch.WordTrace tailWord_5319250 prefixEnd_5319250 2731331971428418643612221 := by
  unfold tailWord_5319250
  simp only [CollatzResearch.WordTrace]
  refine ⟨48502246494818295104816801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129339323986182120279511469 48502246494818295104816801)
  ·
    refine ⟨36376684871113721328612601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48502246494818295104816801 36376684871113721328612601)
    ·
      refine ⟨27282513653335290996459451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36376684871113721328612601 27282513653335290996459451)
      ·
        refine ⟨40923770480002936494689177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27282513653335290996459451 40923770480002936494689177)
        ·
          refine ⟨30692827860002202371016883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40923770480002936494689177 30692827860002202371016883)
          ·
            refine ⟨46039241790003303556525325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30692827860002202371016883 46039241790003303556525325)
            ·
              refine ⟨17264715671251238833696997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46039241790003303556525325 17264715671251238833696997)
              ·
                refine ⟨3237134188359607281318187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17264715671251238833696997 3237134188359607281318187)
                ·
                  refine ⟨4855701282539410921977281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237134188359607281318187 4855701282539410921977281)
                  ·
                    refine ⟨3641775961904558191482961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855701282539410921977281 3641775961904558191482961)
                    ·
                      refine ⟨2731331971428418643612221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641775961904558191482961 2731331971428418643612221)
                      ·
                        rfl

theorem cell23_5319250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_5319250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319250 prefixEnd_5319250 := by exact prefixLift 5319250
  have htrace : WordTrace (prefixWord ++ tailWord_5319250) baseStart_5319250 baseEnd_5319250 := by
    simpa [prefixWord, tailWord_5319250, baseEnd_5319250] using wordTrace_append hprefix tailTrace_5319250
  have hstable : (prefixWord ++ tailWord_5319250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319250).length < 2 ^ (prefixWord ++ tailWord_5319250).sum := by decide
  have hdescent : baseEnd_5319250 < baseStart_5319250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319276 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 3, 3, 2]
def baseStart_5319276 : Nat := 118140960795 + 5319276 * 2 ^ 59
def prefixEnd_5319276 : Nat := 4983230072969 + 3 ^ 40 * 5319276 * 2
def baseEnd_5319276 : Nat := 2731345321925435541887101

theorem tailTrace_5319276 : CollatzResearch.WordTrace tailWord_5319276 prefixEnd_5319276 2731345321925435541887101 := by
  unfold tailWord_5319276
  simp only [CollatzResearch.WordTrace]
  refine ⟨97004967138589493429856841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129339956184785991239809121 97004967138589493429856841)
  ·
    refine ⟨72753725353942120072392631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97004967138589493429856841 72753725353942120072392631)
    ·
      refine ⟨109130588030913180108588947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72753725353942120072392631 109130588030913180108588947)
      ·
        refine ⟨163695882046369770162883421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109130588030913180108588947 163695882046369770162883421)
        ·
          refine ⟨61385955767388663811081283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163695882046369770162883421 61385955767388663811081283)
          ·
            refine ⟨92078933651082995716621925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61385955767388663811081283 92078933651082995716621925)
            ·
              refine ⟨17264800059578061696866611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92078933651082995716621925 17264800059578061696866611)
              ·
                refine ⟨25897200089367092545299917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17264800059578061696866611 25897200089367092545299917)
                ·
                  refine ⟨9711450033512659704487469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25897200089367092545299917 9711450033512659704487469)
                  ·
                    refine ⟨3641793762567247389182801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9711450033512659704487469 3641793762567247389182801)
                    ·
                      refine ⟨2731345321925435541887101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641793762567247389182801 2731345321925435541887101)
                      ·
                        rfl

theorem cell23_5319276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_5319276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319276 prefixEnd_5319276 := by exact prefixLift 5319276
  have htrace : WordTrace (prefixWord ++ tailWord_5319276) baseStart_5319276 baseEnd_5319276 := by
    simpa [prefixWord, tailWord_5319276, baseEnd_5319276] using wordTrace_append hprefix tailTrace_5319276
  have hstable : (prefixWord ++ tailWord_5319276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319276).length < 2 ^ (prefixWord ++ tailWord_5319276).sum := by decide
  have hdescent : baseEnd_5319276 < baseStart_5319276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319300 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_5319300 : Nat := 118140960795 + 5319300 * 2 ^ 59
def prefixEnd_5319300 : Nat := 4983230072969 + 3 ^ 40 * 5319300 * 2
def baseEnd_5319300 : Nat := 2731357645461143447986991

theorem tailTrace_5319300 : CollatzResearch.WordTrace tailWord_5319300 prefixEnd_5319300 2731357645461143447986991 := by
  unfold tailWord_5319300
  simp only [CollatzResearch.WordTrace]
  refine ⟨97005404814546019479293677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129340539752728025972391569 97005404814546019479293677)
  ·
    refine ⟨36377026805454757304735129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97005404814546019479293677 36377026805454757304735129)
    ·
      refine ⟨27282770104091067978551347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36377026805454757304735129 27282770104091067978551347)
      ·
        refine ⟨40924155156136601967827021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27282770104091067978551347 40924155156136601967827021)
        ·
          refine ⟨15346558183551225737935133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40924155156136601967827021 15346558183551225737935133)
          ·
            refine ⟨5754959318831709651725675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15346558183551225737935133 5754959318831709651725675)
            ·
              refine ⟨8632438978247564477588513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754959318831709651725675 8632438978247564477588513)
              ·
                refine ⟨6474329233685673358191385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8632438978247564477588513 6474329233685673358191385)
                ·
                  refine ⟨4855746925264255018643539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6474329233685673358191385 4855746925264255018643539)
                  ·
                    refine ⟨7283620387896382527965309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4855746925264255018643539 7283620387896382527965309)
                    ·
                      refine ⟨2731357645461143447986991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283620387896382527965309 2731357645461143447986991)
                      ·
                        rfl

theorem cell23_5319300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_5319300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319300 prefixEnd_5319300 := by exact prefixLift 5319300
  have htrace : WordTrace (prefixWord ++ tailWord_5319300) baseStart_5319300 baseEnd_5319300 := by
    simpa [prefixWord, tailWord_5319300, baseEnd_5319300] using wordTrace_append hprefix tailTrace_5319300
  have hstable : (prefixWord ++ tailWord_5319300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319300).length < 2 ^ (prefixWord ++ tailWord_5319300).sum := by decide
  have hdescent : baseEnd_5319300 < baseStart_5319300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319316 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_5319316 : Nat := 118140960795 + 5319316 * 2 ^ 59
def prefixEnd_5319316 : Nat := 4983230072969 + 3 ^ 40 * 5319316 * 2
def baseEnd_5319316 : Nat := 910455287050538461795639

theorem tailTrace_5319316 : CollatzResearch.WordTrace tailWord_5319316 prefixEnd_5319316 910455287050538461795639 := by
  unfold tailWord_5319316
  simp only [CollatzResearch.WordTrace]
  refine ⟨97005696598517036845584901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129340928798022715794113201 97005696598517036845584901)
  ·
    refine ⟨18188568112221944408547169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97005696598517036845584901 18188568112221944408547169)
    ·
      refine ⟨13641426084166458306410377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18188568112221944408547169 13641426084166458306410377)
      ·
        refine ⟨10231069563124843729807783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13641426084166458306410377 10231069563124843729807783)
        ·
          refine ⟨15346604344687265594711675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231069563124843729807783 15346604344687265594711675)
          ·
            refine ⟨23019906517030898392067513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15346604344687265594711675 23019906517030898392067513)
            ·
              refine ⟨17264929887773173794050635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23019906517030898392067513 17264929887773173794050635)
              ·
                refine ⟨25897394831659760691075953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17264929887773173794050635 25897394831659760691075953)
                ·
                  refine ⟨19423046123744820518306965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25897394831659760691075953 19423046123744820518306965)
                  ·
                    refine ⟨910455287050538461795639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19423046123744820518306965 910455287050538461795639)
                    ·
                      rfl

theorem cell23_5319316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_5319316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319316 prefixEnd_5319316 := by exact prefixLift 5319316
  have htrace : WordTrace (prefixWord ++ tailWord_5319316) baseStart_5319316 baseEnd_5319316 := by
    simpa [prefixWord, tailWord_5319316, baseEnd_5319316] using wordTrace_append hprefix tailTrace_5319316
  have hstable : (prefixWord ++ tailWord_5319316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319316).length < 2 ^ (prefixWord ++ tailWord_5319316).sum := by decide
  have hdescent : baseEnd_5319316 < baseStart_5319316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319319 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5319319 : Nat := 118140960795 + 5319319 * 2 ^ 59
def prefixEnd_5319319 : Nat := 4983230072969 + 3 ^ 40 * 5319319 * 2
def baseEnd_5319319 : Nat := 2731367401593578873649403

theorem tailTrace_5319319 : CollatzResearch.WordTrace tailWord_5319319 prefixEnd_5319319 2731367401593578873649403 := by
  unfold tailWord_5319319
  simp only [CollatzResearch.WordTrace]
  refine ⟨194011502616023205203529011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129341001744015470135686007 194011502616023205203529011)
  ·
    refine ⟨291017253924034807805293517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194011502616023205203529011 291017253924034807805293517)
    ·
      refine ⟨109131470221513052926985069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291017253924034807805293517 109131470221513052926985069)
      ·
        refine ⟨40924301333067394847619401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109131470221513052926985069 40924301333067394847619401)
        ·
          refine ⟨30693225999800546135714551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40924301333067394847619401 30693225999800546135714551)
          ·
            refine ⟨46039838999700819203571827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30693225999800546135714551 46039838999700819203571827)
            ·
              refine ⟨69059758499551228805357741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46039838999700819203571827 69059758499551228805357741)
              ·
                refine ⟨25897409437331710802009153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69059758499551228805357741 25897409437331710802009153)
                ·
                  refine ⟨19423057077998783101506865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25897409437331710802009153 19423057077998783101506865)
                  ·
                    refine ⟨14567292808499087326130149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19423057077998783101506865 14567292808499087326130149)
                    ·
                      refine ⟨2731367401593578873649403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14567292808499087326130149 2731367401593578873649403)
                      ·
                        rfl

theorem cell23_5319319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5319319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319319 prefixEnd_5319319 := by exact prefixLift 5319319
  have htrace : WordTrace (prefixWord ++ tailWord_5319319) baseStart_5319319 baseEnd_5319319 := by
    simpa [prefixWord, tailWord_5319319, baseEnd_5319319] using wordTrace_append hprefix tailTrace_5319319
  have hstable : (prefixWord ++ tailWord_5319319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319319).length < 2 ^ (prefixWord ++ tailWord_5319319).sum := by decide
  have hdescent : baseEnd_5319319 < baseStart_5319319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319326 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5319326 : Nat := 118140960795 + 5319326 * 2 ^ 59
def prefixEnd_5319326 : Nat := 4983230072969 + 3 ^ 40 * 5319326 * 2
def baseEnd_5319326 : Nat := 2731370995958160346261871

theorem tailTrace_5319326 : CollatzResearch.WordTrace tailWord_5319326 prefixEnd_5319326 2731370995958160346261871 := by
  unfold tailWord_5319326
  simp only [CollatzResearch.WordTrace]
  refine ⟨24251469740874730674879229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129341171951331896932689221 24251469740874730674879229)
  ·
    refine ⟨9094301152828024003079711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24251469740874730674879229 9094301152828024003079711)
    ·
      refine ⟨13641451729242036004619567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9094301152828024003079711 13641451729242036004619567)
      ·
        refine ⟨20462177593863054006929351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13641451729242036004619567 20462177593863054006929351)
        ·
          refine ⟨30693266390794581010394027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20462177593863054006929351 30693266390794581010394027)
          ·
            refine ⟨46039899586191871515591041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30693266390794581010394027 46039899586191871515591041)
            ·
              refine ⟨34529924689643903636693281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46039899586191871515591041 34529924689643903636693281)
              ·
                refine ⟨25897443517232927727519961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34529924689643903636693281 25897443517232927727519961)
                ·
                  refine ⟨19423082637924695795639971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25897443517232927727519961 19423082637924695795639971)
                  ·
                    refine ⟨29134623956887043693459957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19423082637924695795639971 29134623956887043693459957)
                    ·
                      refine ⟨2731370995958160346261871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29134623956887043693459957 2731370995958160346261871)
                      ·
                        rfl

theorem cell23_5319326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5319326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319326 prefixEnd_5319326 := by exact prefixLift 5319326
  have htrace : WordTrace (prefixWord ++ tailWord_5319326) baseStart_5319326 baseEnd_5319326 := by
    simpa [prefixWord, tailWord_5319326, baseEnd_5319326] using wordTrace_append hprefix tailTrace_5319326
  have hstable : (prefixWord ++ tailWord_5319326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319326).length < 2 ^ (prefixWord ++ tailWord_5319326).sum := by decide
  have hdescent : baseEnd_5319326 < baseStart_5319326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319359 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 4, 5]
def baseStart_5319359 : Nat := 118140960795 + 5319359 * 2 ^ 59
def prefixEnd_5319359 : Nat := 4983230072969 + 3 ^ 40 * 5319359 * 2
def baseEnd_5319359 : Nat := 910462646939919572383073

theorem tailTrace_5319359 : CollatzResearch.WordTrace tailWord_5319359 prefixEnd_5319359 910462646939919572383073 := by
  unfold tailWord_5319359
  simp only [CollatzResearch.WordTrace]
  refine ⟨194012961535878292034985131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129341974357252194689990087 194012961535878292034985131)
  ·
    refine ⟨291019442303817438052477697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194012961535878292034985131 291019442303817438052477697)
    ·
      refine ⟨218264581727863078539358273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291019442303817438052477697 218264581727863078539358273)
      ·
        refine ⟨163698436295897308904518705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218264581727863078539358273 163698436295897308904518705)
        ·
          refine ⟨122773827221922981678389029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163698436295897308904518705 122773827221922981678389029)
          ·
            refine ⟨23020092604110559064697943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122773827221922981678389029 23020092604110559064697943)
            ·
              refine ⟨34530138906165838597046915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23020092604110559064697943 34530138906165838597046915)
              ·
                refine ⟨51795208359248757895570373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34530138906165838597046915 51795208359248757895570373)
                ·
                  refine ⟨9711601567359142105419445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51795208359248757895570373 9711601567359142105419445)
                  ·
                    refine ⟨910462646939919572383073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9711601567359142105419445 910462646939919572383073)
                    ·
                      rfl

theorem cell23_5319359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_5319359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319359 prefixEnd_5319359 := by exact prefixLift 5319359
  have htrace : WordTrace (prefixWord ++ tailWord_5319359) baseStart_5319359 baseEnd_5319359 := by
    simpa [prefixWord, tailWord_5319359, baseEnd_5319359] using wordTrace_append hprefix tailTrace_5319359
  have hstable : (prefixWord ++ tailWord_5319359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319359).length < 2 ^ (prefixWord ++ tailWord_5319359).sum := by decide
  have hdescent : baseEnd_5319359 < baseStart_5319359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319396 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_5319396 : Nat := 118140960795 + 5319396 * 2 ^ 59
def prefixEnd_5319396 : Nat := 4983230072969 + 3 ^ 40 * 5319396 * 2
def baseEnd_5319396 : Nat := 2731406939603975072386549

theorem tailTrace_5319396 : CollatzResearch.WordTrace tailWord_5319396 prefixEnd_5319396 2731406939603975072386549 := by
  unfold tailWord_5319396
  simp only [CollatzResearch.WordTrace]
  refine ⟨97007155518372123677041021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129342874024496164902721361 97007155518372123677041021)
  ·
    refine ⟨36377683319389546378890383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97007155518372123677041021 36377683319389546378890383)
    ·
      refine ⟨54566524979084319568335575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36377683319389546378890383 54566524979084319568335575)
      ·
        refine ⟨81849787468626479352503363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54566524979084319568335575 81849787468626479352503363)
        ·
          refine ⟨122774681202939719028755045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81849787468626479352503363 122774681202939719028755045)
          ·
            refine ⟨23020252725551197317891571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122774681202939719028755045 23020252725551197317891571)
            ·
              refine ⟨34530379088326795976837357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23020252725551197317891571 34530379088326795976837357)
              ·
                refine ⟨12948892158122548491314009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34530379088326795976837357 12948892158122548491314009)
                ·
                  refine ⟨9711669118591911368485507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12948892158122548491314009 9711669118591911368485507)
                  ·
                    refine ⟨14567503677887867052728261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9711669118591911368485507 14567503677887867052728261)
                    ·
                      refine ⟨2731406939603975072386549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14567503677887867052728261 2731406939603975072386549)
                      ·
                        rfl

theorem cell23_5319396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_5319396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319396 prefixEnd_5319396 := by exact prefixLift 5319396
  have htrace : WordTrace (prefixWord ++ tailWord_5319396) baseStart_5319396 baseEnd_5319396 := by
    simpa [prefixWord, tailWord_5319396, baseEnd_5319396] using wordTrace_append hprefix tailTrace_5319396
  have hstable : (prefixWord ++ tailWord_5319396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319396).length < 2 ^ (prefixWord ++ tailWord_5319396).sum := by decide
  have hdescent : baseEnd_5319396 < baseStart_5319396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319409 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_5319409 : Nat := 118140960795 + 5319409 * 2 ^ 59
def prefixEnd_5319409 : Nat := 4983230072969 + 3 ^ 40 * 5319409 * 2
def baseEnd_5319409 : Nat := 2731413614852483521523989

theorem tailTrace_5319409 : CollatzResearch.WordTrace tailWord_5319409 prefixEnd_5319409 2731413614852483521523989 := by
  unfold tailWord_5319409
  simp only [CollatzResearch.WordTrace]
  refine ⟨194014785185697150574305281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129343190123798100382870187 194014785185697150574305281)
  ·
    refine ⟨145511088889272862930728961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194014785185697150574305281 145511088889272862930728961)
    ·
      refine ⟨109133316666954647198046721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145511088889272862930728961 109133316666954647198046721)
      ·
        refine ⟨81849987500215985398535041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109133316666954647198046721 81849987500215985398535041)
        ·
          refine ⟨61387490625161989048901281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81849987500215985398535041 61387490625161989048901281)
          ·
            refine ⟨46040617968871491786675961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61387490625161989048901281 46040617968871491786675961)
            ·
              refine ⟨34530463476653618840006971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46040617968871491786675961 34530463476653618840006971)
              ·
                refine ⟨51795695214980428260010457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34530463476653618840006971 51795695214980428260010457)
                ·
                  refine ⟨38846771411235321195007843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51795695214980428260010457 38846771411235321195007843)
                  ·
                    refine ⟨58270157116852981792511765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38846771411235321195007843 58270157116852981792511765)
                    ·
                      refine ⟨2731413614852483521523989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58270157116852981792511765 2731413614852483521523989)
                      ·
                        rfl

theorem cell23_5319409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_5319409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319409 prefixEnd_5319409 := by exact prefixLift 5319409
  have htrace : WordTrace (prefixWord ++ tailWord_5319409) baseStart_5319409 baseEnd_5319409 := by
    simpa [prefixWord, tailWord_5319409, baseEnd_5319409] using wordTrace_append hprefix tailTrace_5319409
  have hstable : (prefixWord ++ tailWord_5319409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319409).length < 2 ^ (prefixWord ++ tailWord_5319409).sum := by decide
  have hdescent : baseEnd_5319409 < baseStart_5319409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319416 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_5319416 : Nat := 118140960795 + 5319416 * 2 ^ 59
def prefixEnd_5319416 : Nat := 4983230072969 + 3 ^ 40 * 5319416 * 2
def baseEnd_5319416 : Nat := 2731417209217064994136457

theorem tailTrace_5319416 : CollatzResearch.WordTrace tailWord_5319416 prefixEnd_5319416 2731417209217064994136457 := by
  unfold tailWord_5319416
  simp only [CollatzResearch.WordTrace]
  refine ⟨97007520248335895384905051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129343360331114527179873401 97007520248335895384905051)
  ·
    refine ⟨145511280372503843077357577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97007520248335895384905051 145511280372503843077357577)
    ·
      refine ⟨109133460279377882308018183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145511280372503843077357577 109133460279377882308018183)
      ·
        refine ⟨163700190419066823462027275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109133460279377882308018183 163700190419066823462027275)
        ·
          refine ⟨245550285628600235193040913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163700190419066823462027275 245550285628600235193040913)
          ·
            refine ⟨184162714221450176394780685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245550285628600235193040913 184162714221450176394780685)
            ·
              refine ⟨69061017833043816148042757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184162714221450176394780685 69061017833043816148042757)
              ·
                refine ⟨12948940843695715527758017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69061017833043816148042757 12948940843695715527758017)
                ·
                  refine ⟨9711705632771786645818513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12948940843695715527758017 9711705632771786645818513)
                  ·
                    refine ⟨7283779224578839984363885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9711705632771786645818513 7283779224578839984363885)
                    ·
                      refine ⟨2731417209217064994136457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283779224578839984363885 2731417209217064994136457)
                      ·
                        rfl

theorem cell23_5319416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_5319416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319416 prefixEnd_5319416 := by exact prefixLift 5319416
  have htrace : WordTrace (prefixWord ++ tailWord_5319416) baseStart_5319416 baseEnd_5319416 := by
    simpa [prefixWord, tailWord_5319416, baseEnd_5319416] using wordTrace_append hprefix tailTrace_5319416
  have hstable : (prefixWord ++ tailWord_5319416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319416).length < 2 ^ (prefixWord ++ tailWord_5319416).sum := by decide
  have hdescent : baseEnd_5319416 < baseStart_5319416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319459 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_5319459 : Nat := 118140960795 + 5319459 * 2 ^ 59
def prefixEnd_5319459 : Nat := 4983230072969 + 3 ^ 40 * 5319459 * 2
def baseEnd_5319459 : Nat := 2731439288885208325898759

theorem tailTrace_5319459 : CollatzResearch.WordTrace tailWord_5319459 prefixEnd_5319459 2731439288885208325898759 := by
  unfold tailWord_5319459
  simp only [CollatzResearch.WordTrace]
  refine ⟨194016608835516009113625431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129344405890344006075750287 194016608835516009113625431)
  ·
    refine ⟨291024913253274013670438147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194016608835516009113625431 291024913253274013670438147)
    ·
      refine ⟨436537369879911020505657221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291024913253274013670438147 436537369879911020505657221)
      ·
        refine ⟨81850756852483316344810729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 436537369879911020505657221 81850756852483316344810729)
        ·
          refine ⟨61388067639362487258608047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81850756852483316344810729 61388067639362487258608047)
          ·
            refine ⟨92082101459043730887912071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61388067639362487258608047 92082101459043730887912071)
            ·
              refine ⟨138123152188565596331868107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92082101459043730887912071 138123152188565596331868107)
              ·
                refine ⟨207184728282848394497802161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138123152188565596331868107 207184728282848394497802161)
                ·
                  refine ⟨155388546212136295873351621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207184728282848394497802161 155388546212136295873351621)
                  ·
                    refine ⟨29135352414775555476253429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155388546212136295873351621 29135352414775555476253429)
                    ·
                      refine ⟨2731439288885208325898759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29135352414775555476253429 2731439288885208325898759)
                      ·
                        rfl

theorem cell23_5319459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_5319459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319459 prefixEnd_5319459 := by exact prefixLift 5319459
  have htrace : WordTrace (prefixWord ++ tailWord_5319459) baseStart_5319459 baseEnd_5319459 := by
    simpa [prefixWord, tailWord_5319459, baseEnd_5319459] using wordTrace_append hprefix tailTrace_5319459
  have hstable : (prefixWord ++ tailWord_5319459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319459).length < 2 ^ (prefixWord ++ tailWord_5319459).sum := by decide
  have hdescent : baseEnd_5319459 < baseStart_5319459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319470 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_5319470 : Nat := 118140960795 + 5319470 * 2 ^ 59
def prefixEnd_5319470 : Nat := 4983230072969 + 3 ^ 40 * 5319470 * 2
def baseEnd_5319470 : Nat := 303493881908045309206801

theorem tailTrace_5319470 : CollatzResearch.WordTrace tailWord_5319470 prefixEnd_5319470 303493881908045309206801 := by
  unfold tailWord_5319470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252126254809519749034483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129344673358984105328183909 24252126254809519749034483)
  ·
    refine ⟨36378189382214279623551725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24252126254809519749034483 36378189382214279623551725)
    ·
      refine ⟨13641821018330354858831897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36378189382214279623551725 13641821018330354858831897)
      ·
        refine ⟨10231365763747766144123923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13641821018330354858831897 10231365763747766144123923)
        ·
          refine ⟨15347048645621649216185885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231365763747766144123923 15347048645621649216185885)
          ·
            refine ⟨5755143242108118456069707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15347048645621649216185885 5755143242108118456069707)
            ·
              refine ⟨8632714863162177684104561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755143242108118456069707 8632714863162177684104561)
              ·
                refine ⟨6474536147371633263078421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8632714863162177684104561 6474536147371633263078421)
                ·
                  refine ⟨303493881908045309206801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6474536147371633263078421 303493881908045309206801)
                  ·
                    rfl

theorem cell23_5319470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_5319470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319470 prefixEnd_5319470 := by exact prefixLift 5319470
  have htrace : WordTrace (prefixWord ++ tailWord_5319470) baseStart_5319470 baseEnd_5319470 := by
    simpa [prefixWord, tailWord_5319470, baseEnd_5319470] using wordTrace_append hprefix tailTrace_5319470
  have hstable : (prefixWord ++ tailWord_5319470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319470).length < 2 ^ (prefixWord ++ tailWord_5319470).sum := by decide
  have hdescent : baseEnd_5319470 < baseStart_5319470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319473 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 4, 3, 2]
def baseStart_5319473 : Nat := 118140960795 + 5319473 * 2 ^ 59
def prefixEnd_5319473 : Nat := 4983230072969 + 3 ^ 40 * 5319473 * 2
def baseEnd_5319473 : Nat := 2731446477614371271123695

theorem tailTrace_5319473 : CollatzResearch.WordTrace tailWord_5319473 prefixEnd_5319473 2731446477614371271123695 := by
  unfold tailWord_5319473
  simp only [CollatzResearch.WordTrace]
  refine ⟨194017119457465289504635073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129344746304976859669756715 194017119457465289504635073)
  ·
    refine ⟨145512839593098967128476305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194017119457465289504635073 145512839593098967128476305)
    ·
      refine ⟨109134629694824225346357229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145512839593098967128476305 109134629694824225346357229)
      ·
        refine ⟨40925486135559084504883961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109134629694824225346357229 40925486135559084504883961)
        ·
          refine ⟨30694114601669313378662971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40925486135559084504883961 30694114601669313378662971)
          ·
            refine ⟨46041171902503970067994457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30694114601669313378662971 46041171902503970067994457)
            ·
              refine ⟨34530878926877977550995843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46041171902503970067994457 34530878926877977550995843)
              ·
                refine ⟨51796318390316966326493765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34530878926877977550995843 51796318390316966326493765)
                ·
                  refine ⟨9711809698184431186217581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51796318390316966326493765 9711809698184431186217581)
                  ·
                    refine ⟨3641928636819161694831593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9711809698184431186217581 3641928636819161694831593)
                    ·
                      refine ⟨2731446477614371271123695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641928636819161694831593 2731446477614371271123695)
                      ·
                        rfl

theorem cell23_5319473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_5319473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319473 prefixEnd_5319473 := by exact prefixLift 5319473
  have htrace : WordTrace (prefixWord ++ tailWord_5319473) baseStart_5319473 baseEnd_5319473 := by
    simpa [prefixWord, tailWord_5319473, baseEnd_5319473] using wordTrace_append hprefix tailTrace_5319473
  have hstable : (prefixWord ++ tailWord_5319473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319473).length < 2 ^ (prefixWord ++ tailWord_5319473).sum := by decide
  have hdescent : baseEnd_5319473 < baseStart_5319473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319480 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 1, 1, 3]
def baseStart_5319480 : Nat := 118140960795 + 5319480 * 2 ^ 59
def prefixEnd_5319480 : Nat := 4983230072969 + 3 ^ 40 * 5319480 * 2
def baseEnd_5319480 : Nat := 2731450071978952743736163

theorem tailTrace_5319480 : CollatzResearch.WordTrace tailWord_5319480 prefixEnd_5319480 2731450071978952743736163 := by
  unfold tailWord_5319480
  simp only [CollatzResearch.WordTrace]
  refine ⟨97008687384219964850069947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129344916512293286466759929 97008687384219964850069947)
  ·
    refine ⟨145513031076329947275104921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97008687384219964850069947 145513031076329947275104921)
    ·
      refine ⟨109134773307247460456328691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145513031076329947275104921 109134773307247460456328691)
      ·
        refine ⟨163702159960871190684493037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109134773307247460456328691 163702159960871190684493037)
        ·
          refine ⟨61388309985326696506684889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163702159960871190684493037 61388309985326696506684889)
          ·
            refine ⟨46041232488995022380013667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61388309985326696506684889 46041232488995022380013667)
            ·
              refine ⟨69061848733492533570020501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46041232488995022380013667 69061848733492533570020501)
              ·
                refine ⟨3237274159382462511094711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69061848733492533570020501 3237274159382462511094711)
                ·
                  refine ⟨4855911239073693766642067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237274159382462511094711 4855911239073693766642067)
                  ·
                    refine ⟨7283866858610540649963101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4855911239073693766642067 7283866858610540649963101)
                    ·
                      refine ⟨2731450071978952743736163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7283866858610540649963101 2731450071978952743736163)
                      ·
                        rfl

theorem cell23_5319480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_5319480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319480 prefixEnd_5319480 := by exact prefixLift 5319480
  have htrace : WordTrace (prefixWord ++ tailWord_5319480) baseStart_5319480 baseEnd_5319480 := by
    simpa [prefixWord, tailWord_5319480, baseEnd_5319480] using wordTrace_append hprefix tailTrace_5319480
  have hstable : (prefixWord ++ tailWord_5319480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319480).length < 2 ^ (prefixWord ++ tailWord_5319480).sum := by decide
  have hdescent : baseEnd_5319480 < baseStart_5319480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319506 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_5319506 : Nat := 118140960795 + 5319506 * 2 ^ 59
def prefixEnd_5319506 : Nat := 4983230072969 + 3 ^ 40 * 5319506 * 2
def baseEnd_5319506 : Nat := 2731463422475969642011043

theorem tailTrace_5319506 : CollatzResearch.WordTrace tailWord_5319506 prefixEnd_5319506 2731463422475969642011043 := by
  unfold tailWord_5319506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48504580766586434035146593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129345548710897157427057581 48504580766586434035146593)
  ·
    refine ⟨36378435574939825526359945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48504580766586434035146593 36378435574939825526359945)
    ·
      refine ⟨27283826681204869144769959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36378435574939825526359945 27283826681204869144769959)
      ·
        refine ⟨40925740021807303717154939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27283826681204869144769959 40925740021807303717154939)
        ·
          refine ⟨61388610032710955575732409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40925740021807303717154939 61388610032710955575732409)
          ·
            refine ⟨46041457524533216681799307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61388610032710955575732409 46041457524533216681799307)
            ·
              refine ⟨69062186286799825022698961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46041457524533216681799307 69062186286799825022698961)
              ·
                refine ⟨51796639715099868767024221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69062186286799825022698961 51796639715099868767024221)
                ·
                  refine ⟨19423739893162450787634083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51796639715099868767024221 19423739893162450787634083)
                  ·
                    refine ⟨29135609839743676181451125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19423739893162450787634083 29135609839743676181451125)
                    ·
                      refine ⟨2731463422475969642011043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29135609839743676181451125 2731463422475969642011043)
                      ·
                        rfl

theorem cell23_5319506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_5319506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319506 prefixEnd_5319506 := by exact prefixLift 5319506
  have htrace : WordTrace (prefixWord ++ tailWord_5319506) baseStart_5319506 baseEnd_5319506 := by
    simpa [prefixWord, tailWord_5319506, baseEnd_5319506] using wordTrace_append hprefix tailTrace_5319506
  have hstable : (prefixWord ++ tailWord_5319506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319506).length < 2 ^ (prefixWord ++ tailWord_5319506).sum := by decide
  have hdescent : baseEnd_5319506 < baseStart_5319506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319523 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 5]
def baseStart_5319523 : Nat := 118140960795 + 5319523 * 2 ^ 59
def prefixEnd_5319523 : Nat := 4983230072969 + 3 ^ 40 * 5319523 * 2
def baseEnd_5319523 : Nat := 2731472151647096075498465

theorem tailTrace_5319523 : CollatzResearch.WordTrace tailWord_5319523 prefixEnd_5319523 2731472151647096075498465 := by
  unfold tailWord_5319523
  simp only [CollatzResearch.WordTrace]
  refine ⟨194018943107284148043955223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129345962071522765362636815 194018943107284148043955223)
  ·
    refine ⟨291028414660926222065932835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194018943107284148043955223 291028414660926222065932835)
    ·
      refine ⟨436542621991389333098899253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291028414660926222065932835 436542621991389333098899253)
      ·
        refine ⟨40925870811692749978021805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 436542621991389333098899253 40925870811692749978021805)
        ·
          refine ⟨15347201554384781241758177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40925870811692749978021805 15347201554384781241758177)
          ·
            refine ⟨11510401165788585931318633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15347201554384781241758177 11510401165788585931318633)
            ·
              refine ⟨8632800874341439448488975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11510401165788585931318633 8632800874341439448488975)
              ·
                refine ⟨12949201311512159172733463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8632800874341439448488975 12949201311512159172733463)
                ·
                  refine ⟨19423801967268238759100195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12949201311512159172733463 19423801967268238759100195)
                  ·
                    refine ⟨29135702950902358138650293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19423801967268238759100195 29135702950902358138650293)
                    ·
                      refine ⟨2731472151647096075498465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29135702950902358138650293 2731472151647096075498465)
                      ·
                        rfl

theorem cell23_5319523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_5319523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319523 prefixEnd_5319523 := by exact prefixLift 5319523
  have htrace : WordTrace (prefixWord ++ tailWord_5319523) baseStart_5319523 baseEnd_5319523 := by
    simpa [prefixWord, tailWord_5319523, baseEnd_5319523] using wordTrace_append hprefix tailTrace_5319523
  have hstable : (prefixWord ++ tailWord_5319523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319523).length < 2 ^ (prefixWord ++ tailWord_5319523).sum := by decide
  have hdescent : baseEnd_5319523 < baseStart_5319523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319537 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 3, 2, 2]
def baseStart_5319537 : Nat := 118140960795 + 5319537 * 2 ^ 59
def prefixEnd_5319537 : Nat := 4983230072969 + 3 ^ 40 * 5319537 * 2
def baseEnd_5319537 : Nat := 2731479340376259020723401

theorem tailTrace_5319537 : CollatzResearch.WordTrace tailWord_5319537 prefixEnd_5319537 2731479340376259020723401 := by
  unfold tailWord_5319537
  simp only [CollatzResearch.WordTrace]
  refine ⟨194019453729233428434964865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129346302486155618956643243 194019453729233428434964865)
  ·
    refine ⟨145514590296925071326223649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194019453729233428434964865 145514590296925071326223649)
    ·
      refine ⟨109135942722693803494667737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145514590296925071326223649 109135942722693803494667737)
      ·
        refine ⟨81851957042020352621000803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109135942722693803494667737 81851957042020352621000803)
        ·
          refine ⟨122777935563030528931501205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81851957042020352621000803 122777935563030528931501205)
          ·
            refine ⟨5755215729517056043664119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122777935563030528931501205 5755215729517056043664119)
            ·
              refine ⟨8632823594275584065496179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755215729517056043664119 8632823594275584065496179)
              ·
                refine ⟨12949235391413376098244269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8632823594275584065496179 12949235391413376098244269)
                ·
                  refine ⟨4855963271780016036841601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12949235391413376098244269 4855963271780016036841601)
                  ·
                    refine ⟨3641972453835012027631201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855963271780016036841601 3641972453835012027631201)
                    ·
                      refine ⟨2731479340376259020723401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3641972453835012027631201 2731479340376259020723401)
                      ·
                        rfl

theorem cell23_5319537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_5319537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319537 prefixEnd_5319537 := by exact prefixLift 5319537
  have htrace : WordTrace (prefixWord ++ tailWord_5319537) baseStart_5319537 baseEnd_5319537 := by
    simpa [prefixWord, tailWord_5319537, baseEnd_5319537] using wordTrace_append hprefix tailTrace_5319537
  have hstable : (prefixWord ++ tailWord_5319537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319537).length < 2 ^ (prefixWord ++ tailWord_5319537).sum := by decide
  have hdescent : baseEnd_5319537 < baseStart_5319537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319574 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5319574 : Nat := 118140960795 + 5319574 * 2 ^ 59
def prefixEnd_5319574 : Nat := 4983230072969 + 3 ^ 40 * 5319574 * 2
def baseEnd_5319574 : Nat := 2731498339160475375960731

theorem tailTrace_5319574 : CollatzResearch.WordTrace tailWord_5319574 prefixEnd_5319574 2731498339160475375960731 := by
  unfold tailWord_5319574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12126300201881211484628861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129347202153399589169374517 12126300201881211484628861)
  ·
    refine ⟨4547362575705454306735823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12126300201881211484628861 4547362575705454306735823)
    ·
      refine ⟨6821043863558181460103735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547362575705454306735823 6821043863558181460103735)
      ·
        refine ⟨10231565795337272190155603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821043863558181460103735 10231565795337272190155603)
        ·
          refine ⟨15347348693005908285233405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231565795337272190155603 15347348693005908285233405)
          ·
            refine ⟨5755255759877215606962527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15347348693005908285233405 5755255759877215606962527)
            ·
              refine ⟨8632883639815823410443791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755255759877215606962527 8632883639815823410443791)
              ·
                refine ⟨12949325459723735115665687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8632883639815823410443791 12949325459723735115665687)
                ·
                  refine ⟨19423988189585602673498531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12949325459723735115665687 19423988189585602673498531)
                  ·
                    refine ⟨29135982284378404010247797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19423988189585602673498531 29135982284378404010247797)
                    ·
                      refine ⟨2731498339160475375960731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29135982284378404010247797 2731498339160475375960731)
                      ·
                        rfl

theorem cell23_5319574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5319574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319574 prefixEnd_5319574 := by exact prefixLift 5319574
  have htrace : WordTrace (prefixWord ++ tailWord_5319574) baseStart_5319574 baseEnd_5319574 := by
    simpa [prefixWord, tailWord_5319574, baseEnd_5319574] using wordTrace_append hprefix tailTrace_5319574
  have hstable : (prefixWord ++ tailWord_5319574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319574).length < 2 ^ (prefixWord ++ tailWord_5319574).sum := by decide
  have hdescent : baseEnd_5319574 < baseStart_5319574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319593 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 3, 4, 2]
def baseStart_5319593 : Nat := 118140960795 + 5319593 * 2 ^ 59
def prefixEnd_5319593 : Nat := 4983230072969 + 3 ^ 40 * 5319593 * 2
def baseEnd_5319593 : Nat := 2731508095292910801623143

theorem tailTrace_5319593 : CollatzResearch.WordTrace tailWord_5319593 prefixEnd_5319593 2731508095292910801623143 := by
  unfold tailWord_5319593
  simp only [CollatzResearch.WordTrace]
  refine ⟨194021496217030549999003433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129347664144687033332668955 194021496217030549999003433)
  ·
    refine ⟨145516122162772912499252575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194021496217030549999003433 145516122162772912499252575)
    ·
      refine ⟨218274183244159368748878863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145516122162772912499252575 218274183244159368748878863)
      ·
        refine ⟨327411274866239053123318295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218274183244159368748878863 327411274866239053123318295)
        ·
          refine ⟨491116912299358579684977443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327411274866239053123318295 491116912299358579684977443)
          ·
            refine ⟨736675368449037869527466165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491116912299358579684977443 736675368449037869527466165)
            ·
              refine ⟨69063315792097300268199953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 736675368449037869527466165 69063315792097300268199953)
              ·
                refine ⟨51797486844072975201149965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69063315792097300268199953 51797486844072975201149965)
                ·
                  refine ⟨19424057566527365700431237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51797486844072975201149965 19424057566527365700431237)
                  ·
                    refine ⟨3642010793723881068830857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19424057566527365700431237 3642010793723881068830857)
                    ·
                      refine ⟨2731508095292910801623143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642010793723881068830857 2731508095292910801623143)
                      ·
                        rfl

theorem cell23_5319593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 4, 2].length) (baseStart_5319593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319593 prefixEnd_5319593 := by exact prefixLift 5319593
  have htrace : WordTrace (prefixWord ++ tailWord_5319593) baseStart_5319593 baseEnd_5319593 := by
    simpa [prefixWord, tailWord_5319593, baseEnd_5319593] using wordTrace_append hprefix tailTrace_5319593
  have hstable : (prefixWord ++ tailWord_5319593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319593).length < 2 ^ (prefixWord ++ tailWord_5319593).sum := by decide
  have hdescent : baseEnd_5319593 < baseStart_5319593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319604 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_5319604 : Nat := 118140960795 + 5319604 * 2 ^ 59
def prefixEnd_5319604 : Nat := 4983230072969 + 3 ^ 40 * 5319604 * 2
def baseEnd_5319604 : Nat := 2731513743580110258585593

theorem tailTrace_5319604 : CollatzResearch.WordTrace tailWord_5319604 prefixEnd_5319604 2731513743580110258585593 := by
  unfold tailWord_5319604
  simp only [CollatzResearch.WordTrace]
  refine ⟨97010948709995349438826933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129347931613327132585102577 97010948709995349438826933)
  ·
    refine ⟨9094776441562064009890025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97010948709995349438826933 9094776441562064009890025)
    ·
      refine ⟨6821082331171548007417519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9094776441562064009890025 6821082331171548007417519)
      ·
        refine ⟨10231623496757322011126279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821082331171548007417519 10231623496757322011126279)
        ·
          refine ⟨15347435245135983016689419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231623496757322011126279 15347435245135983016689419)
          ·
            refine ⟨23021152867703974525034129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15347435245135983016689419 23021152867703974525034129)
            ·
              refine ⟨17265864650777980893775597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23021152867703974525034129 17265864650777980893775597)
              ·
                refine ⟨6474699244041742835165849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17265864650777980893775597 6474699244041742835165849)
                ·
                  refine ⟨4856024433031307126374387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6474699244041742835165849 4856024433031307126374387)
                  ·
                    refine ⟨7284036649546960689561581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4856024433031307126374387 7284036649546960689561581)
                    ·
                      refine ⟨2731513743580110258585593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284036649546960689561581 2731513743580110258585593)
                      ·
                        rfl

theorem cell23_5319604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_5319604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319604 prefixEnd_5319604 := by exact prefixLift 5319604
  have htrace : WordTrace (prefixWord ++ tailWord_5319604) baseStart_5319604 baseEnd_5319604 := by
    simpa [prefixWord, tailWord_5319604, baseEnd_5319604] using wordTrace_append hprefix tailTrace_5319604
  have hstable : (prefixWord ++ tailWord_5319604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319604).length < 2 ^ (prefixWord ++ tailWord_5319604).sum := by decide
  have hdescent : baseEnd_5319604 < baseStart_5319604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319610 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2]
def baseStart_5319610 : Nat := 118140960795 + 5319610 * 2 ^ 59
def prefixEnd_5319610 : Nat := 4983230072969 + 3 ^ 40 * 5319610 * 2
def baseEnd_5319610 : Nat := 2731516824464037235110565

theorem tailTrace_5319610 : CollatzResearch.WordTrace tailWord_5319610 prefixEnd_5319610 2731516824464037235110565 := by
  unfold tailWord_5319610
  simp only [CollatzResearch.WordTrace]
  refine ⟨48505529064492240475593071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129348077505312641268248189 48505529064492240475593071)
  ·
    refine ⟨72758293596738360713389607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48505529064492240475593071 72758293596738360713389607)
    ·
      refine ⟨109137440395107541070084411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72758293596738360713389607 109137440395107541070084411)
      ·
        refine ⟨163706160592661311605126617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109137440395107541070084411 163706160592661311605126617)
        ·
          refine ⟨122779620444495983703844963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163706160592661311605126617 122779620444495983703844963)
          ·
            refine ⟨184169430666743975555767445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122779620444495983703844963 184169430666743975555767445)
            ·
              refine ⟨8632942062503623854176599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184169430666743975555767445 8632942062503623854176599)
              ·
                refine ⟨12949413093755435781264899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8632942062503623854176599 12949413093755435781264899)
                ·
                  refine ⟨19424119640633153671897349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12949413093755435781264899 19424119640633153671897349)
                  ·
                    refine ⟨3642022432618716313480753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19424119640633153671897349 3642022432618716313480753)
                    ·
                      refine ⟨2731516824464037235110565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642022432618716313480753 2731516824464037235110565)
                      ·
                        rfl

theorem cell23_5319610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_5319610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319610 prefixEnd_5319610 := by exact prefixLift 5319610
  have htrace : WordTrace (prefixWord ++ tailWord_5319610) baseStart_5319610 baseEnd_5319610 := by
    simpa [prefixWord, tailWord_5319610, baseEnd_5319610] using wordTrace_append hprefix tailTrace_5319610
  have hstable : (prefixWord ++ tailWord_5319610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319610).length < 2 ^ (prefixWord ++ tailWord_5319610).sum := by decide
  have hdescent : baseEnd_5319610 < baseStart_5319610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319616 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 9]
def baseStart_5319616 : Nat := 118140960795 + 5319616 * 2 ^ 59
def prefixEnd_5319616 : Nat := 4983230072969 + 3 ^ 40 * 5319616 * 2
def baseEnd_5319616 : Nat := 303502211705329356848393

theorem tailTrace_5319616 : CollatzResearch.WordTrace tailWord_5319616 prefixEnd_5319616 303502211705329356848393 := by
  unfold tailWord_5319616
  simp only [CollatzResearch.WordTrace]
  refine ⟨97011167547973612463545351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129348223397298149951393801 97011167547973612463545351)
  ·
    refine ⟨145516751321960418695318027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97011167547973612463545351 145516751321960418695318027)
    ·
      refine ⟨218275126982940628042977041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145516751321960418695318027 218275126982940628042977041)
      ·
        refine ⟨163706345237205471032232781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218275126982940628042977041 163706345237205471032232781)
        ·
          refine ⟨61389879463952051637087293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163706345237205471032232781 61389879463952051637087293)
          ·
            refine ⟨23021204798982019363907735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61389879463952051637087293 23021204798982019363907735)
            ·
              refine ⟨34531807198473029045861603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23021204798982019363907735 34531807198473029045861603)
              ·
                refine ⟨51797710797709543568792405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34531807198473029045861603 51797710797709543568792405)
                ·
                  refine ⟨303502211705329356848393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51797710797709543568792405 303502211705329356848393)
                  ·
                    rfl

theorem cell23_5319616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_5319616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319616 prefixEnd_5319616 := by exact prefixLift 5319616
  have htrace : WordTrace (prefixWord ++ tailWord_5319616) baseStart_5319616 baseEnd_5319616 := by
    simpa [prefixWord, tailWord_5319616, baseEnd_5319616] using wordTrace_append hprefix tailTrace_5319616
  have hstable : (prefixWord ++ tailWord_5319616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319616).length < 2 ^ (prefixWord ++ tailWord_5319616).sum := by decide
  have hdescent : baseEnd_5319616 < baseStart_5319616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319622 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5319622 : Nat := 118140960795 + 5319622 * 2 ^ 59
def prefixEnd_5319622 : Nat := 4983230072969 + 3 ^ 40 * 5319622 * 2
def baseEnd_5319622 : Nat := 2731522986231891188160511

theorem tailTrace_5319622 : CollatzResearch.WordTrace tailWord_5319622 prefixEnd_5319622 2731522986231891188160511 := by
  unfold tailWord_5319622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063204810435171498494035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129348369289283658634539413 6063204810435171498494035)
  ·
    refine ⟨9094807215652757247741053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6063204810435171498494035 9094807215652757247741053)
    ·
      refine ⟨3410552705869783967902895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9094807215652757247741053 3410552705869783967902895)
      ·
        refine ⟨5115829058804675951854343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410552705869783967902895 5115829058804675951854343)
        ·
          refine ⟨7673743588207013927781515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115829058804675951854343 7673743588207013927781515)
          ·
            refine ⟨11510615382310520891672273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7673743588207013927781515 11510615382310520891672273)
            ·
              refine ⟨8632961536732890668754205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11510615382310520891672273 8632961536732890668754205)
              ·
                refine ⟨3237360576274834000782827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8632961536732890668754205 3237360576274834000782827)
                ·
                  refine ⟨4856040864412251001174241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237360576274834000782827 4856040864412251001174241)
                  ·
                    refine ⟨3642030648309188250880681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4856040864412251001174241 3642030648309188250880681)
                    ·
                      refine ⟨2731522986231891188160511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642030648309188250880681 2731522986231891188160511)
                      ·
                        rfl

theorem cell23_5319622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5319622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319622 prefixEnd_5319622 := by exact prefixLift 5319622
  have htrace : WordTrace (prefixWord ++ tailWord_5319622) baseStart_5319622 baseEnd_5319622 := by
    simpa [prefixWord, tailWord_5319622, baseEnd_5319622] using wordTrace_append hprefix tailTrace_5319622
  have hstable : (prefixWord ++ tailWord_5319622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319622).length < 2 ^ (prefixWord ++ tailWord_5319622).sum := by decide
  have hdescent : baseEnd_5319622 < baseStart_5319622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319626 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_5319626 : Nat := 118140960795 + 5319626 * 2 ^ 59
def prefixEnd_5319626 : Nat := 4983230072969 + 3 ^ 40 * 5319626 * 2
def baseEnd_5319626 : Nat := 2731525040154509172510491

theorem tailTrace_5319626 : CollatzResearch.WordTrace tailWord_5319626 prefixEnd_5319626 2731525040154509172510491 := by
  unfold tailWord_5319626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48505674956477749158738683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129348466550607331089969821 48505674956477749158738683)
  ·
    refine ⟨72758512434716623738108025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48505674956477749158738683 72758512434716623738108025)
    ·
      refine ⟨54568884326037467803581019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72758512434716623738108025 54568884326037467803581019)
      ·
        refine ⟨81853326489056201705371529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54568884326037467803581019 81853326489056201705371529)
        ·
          refine ⟨61389994866792151279028647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81853326489056201705371529 61389994866792151279028647)
          ·
            refine ⟨92084992300188226918542971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61389994866792151279028647 92084992300188226918542971)
            ·
              refine ⟨138127488450282340377814457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92084992300188226918542971 138127488450282340377814457)
              ·
                refine ⟨103595616337711755283360843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138127488450282340377814457 103595616337711755283360843)
                ·
                  refine ⟨155393424506567632925041265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103595616337711755283360843 155393424506567632925041265)
                  ·
                    refine ⟨116545068379925724693780949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155393424506567632925041265 116545068379925724693780949)
                    ·
                      refine ⟨2731525040154509172510491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116545068379925724693780949 2731525040154509172510491)
                      ·
                        rfl

theorem cell23_5319626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_5319626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319626 prefixEnd_5319626 := by exact prefixLift 5319626
  have htrace : WordTrace (prefixWord ++ tailWord_5319626) baseStart_5319626 baseEnd_5319626 := by
    simpa [prefixWord, tailWord_5319626, baseEnd_5319626] using wordTrace_append hprefix tailTrace_5319626
  have hstable : (prefixWord ++ tailWord_5319626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319626).length < 2 ^ (prefixWord ++ tailWord_5319626).sum := by decide
  have hdescent : baseEnd_5319626 < baseStart_5319626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319650 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_5319650 : Nat := 118140960795 + 5319650 * 2 ^ 59
def prefixEnd_5319650 : Nat := 4983230072969 + 3 ^ 40 * 5319650 * 2
def baseEnd_5319650 : Nat := 303504151521135230956709

theorem tailTrace_5319650 : CollatzResearch.WordTrace tailWord_5319650 prefixEnd_5319650 303504151521135230956709 := by
  unfold tailWord_5319650
  simp only [CollatzResearch.WordTrace]
  refine ⟨48505893794456012183457101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129349050118549365822552269 48505893794456012183457101)
  ·
    refine ⟨18189710172921004568796413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48505893794456012183457101 18189710172921004568796413)
    ·
      refine ⟨6821141314845376713298655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18189710172921004568796413 6821141314845376713298655)
      ·
        refine ⟨10231711972268065069947983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821141314845376713298655 10231711972268065069947983)
        ·
          refine ⟨15347567958402097604921975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231711972268065069947983 15347567958402097604921975)
          ·
            refine ⟨23021351937603146407382963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15347567958402097604921975 23021351937603146407382963)
            ·
              refine ⟨34532027906404719611074445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23021351937603146407382963 34532027906404719611074445)
              ·
                refine ⟨12949510464901769854152917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34532027906404719611074445 12949510464901769854152917)
                ·
                  refine ⟨303504151521135230956709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12949510464901769854152917 303504151521135230956709)
                  ·
                    rfl

theorem cell23_5319650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_5319650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319650 prefixEnd_5319650 := by exact prefixLift 5319650
  have htrace : WordTrace (prefixWord ++ tailWord_5319650) baseStart_5319650 baseEnd_5319650 := by
    simpa [prefixWord, tailWord_5319650, baseEnd_5319650] using wordTrace_append hprefix tailTrace_5319650
  have hstable : (prefixWord ++ tailWord_5319650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319650).length < 2 ^ (prefixWord ++ tailWord_5319650).sum := by decide
  have hdescent : baseEnd_5319650 < baseStart_5319650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319723 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 6]
def baseStart_5319723 : Nat := 118140960795 + 5319723 * 2 ^ 59
def prefixEnd_5319723 : Nat := 4983230072969 + 3 ^ 40 * 5319723 * 2
def baseEnd_5319723 : Nat := 303508316419777254777505

theorem tailTrace_5319723 : CollatzResearch.WordTrace tailWord_5319723 prefixEnd_5319723 303508316419777254777505 := by
  unfold tailWord_5319723
  simp only [CollatzResearch.WordTrace]
  refine ⟨194026237706559582201235823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129350825137706388134157215 194026237706559582201235823)
  ·
    refine ⟨291039356559839373301853735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194026237706559582201235823 291039356559839373301853735)
    ·
      refine ⟨436559034839759059952780603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291039356559839373301853735 436559034839759059952780603)
      ·
        refine ⟨654838552259638589929170905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436559034839759059952780603 654838552259638589929170905)
        ·
          refine ⟨491128914194728942446878179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654838552259638589929170905 491128914194728942446878179)
          ·
            refine ⟨736693371292093413670317269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491128914194728942446878179 736693371292093413670317269)
            ·
              refine ⟨17266250889658439382898061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 736693371292093413670317269 17266250889658439382898061)
              ·
                refine ⟨6474844083621914768586773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17266250889658439382898061 6474844083621914768586773)
                ·
                  refine ⟨303508316419777254777505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6474844083621914768586773 303508316419777254777505)
                  ·
                    rfl

theorem cell23_5319723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 6].length) (baseStart_5319723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319723 prefixEnd_5319723 := by exact prefixLift 5319723
  have htrace : WordTrace (prefixWord ++ tailWord_5319723) baseStart_5319723 baseEnd_5319723 := by
    simpa [prefixWord, tailWord_5319723, baseEnd_5319723] using wordTrace_append hprefix tailTrace_5319723
  have hstable : (prefixWord ++ tailWord_5319723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319723).length < 2 ^ (prefixWord ++ tailWord_5319723).sum := by decide
  have hdescent : baseEnd_5319723 < baseStart_5319723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319737 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5319737 : Nat := 118140960795 + 5319737 * 2 ^ 59
def prefixEnd_5319737 : Nat := 4983230072969 + 3 ^ 40 * 5319737 * 2
def baseEnd_5319737 : Nat := 2731582036507158238222481

theorem tailTrace_5319737 : CollatzResearch.WordTrace tailWord_5319737 prefixEnd_5319737 2731582036507158238222481 := by
  unfold tailWord_5319737
  simp only [CollatzResearch.WordTrace]
  refine ⟨194026748328508862592245465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129351165552339241728163643 194026748328508862592245465)
  ·
    refine ⟨145520061246381646944184099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194026748328508862592245465 145520061246381646944184099)
    ·
      refine ⟨218280091869572470416276149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145520061246381646944184099 218280091869572470416276149)
      ·
        refine ⟨20463758612772419101525889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218280091869572470416276149 20463758612772419101525889)
        ·
          refine ⟨15347818959579314326144417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20463758612772419101525889 15347818959579314326144417)
          ·
            refine ⟨11510864219684485744608313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15347818959579314326144417 11510864219684485744608313)
            ·
              refine ⟨8633148164763364308456235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11510864219684485744608313 8633148164763364308456235)
              ·
                refine ⟨12949722247145046462684353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8633148164763364308456235 12949722247145046462684353)
                ·
                  refine ⟨9712291685358784847013265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12949722247145046462684353 9712291685358784847013265)
                  ·
                    refine ⟨7284218764019088635259949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9712291685358784847013265 7284218764019088635259949)
                    ·
                      refine ⟨2731582036507158238222481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284218764019088635259949 2731582036507158238222481)
                      ·
                        rfl

theorem cell23_5319737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5319737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319737 prefixEnd_5319737 := by exact prefixLift 5319737
  have htrace : WordTrace (prefixWord ++ tailWord_5319737) baseStart_5319737 baseEnd_5319737 := by
    simpa [prefixWord, tailWord_5319737, baseEnd_5319737] using wordTrace_append hprefix tailTrace_5319737
  have hstable : (prefixWord ++ tailWord_5319737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319737).length < 2 ^ (prefixWord ++ tailWord_5319737).sum := by decide
  have hdescent : baseEnd_5319737 < baseStart_5319737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319757 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 6]
def baseStart_5319757 : Nat := 118140960795 + 5319757 * 2 ^ 59
def prefixEnd_5319757 : Nat := 4983230072969 + 3 ^ 40 * 5319757 * 2
def baseEnd_5319757 : Nat := 303510256235583128885821

theorem tailTrace_5319757 : CollatzResearch.WordTrace tailWord_5319757 prefixEnd_5319757 303510256235583128885821 := by
  unfold tailWord_5319757
  simp only [CollatzResearch.WordTrace]
  refine ⟨194027477788436406007973525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129351651858957604005315683 194027477788436406007973525)
  ·
    refine ⟨9095038021332956531623759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 194027477788436406007973525 9095038021332956531623759)
    ·
      refine ⟨13642557031999434797435639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9095038021332956531623759 13642557031999434797435639)
      ·
        refine ⟨20463835547999152196153459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13642557031999434797435639 20463835547999152196153459)
        ·
          refine ⟨30695753321998728294230189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20463835547999152196153459 30695753321998728294230189)
          ·
            refine ⟨11510907495749523110336321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30695753321998728294230189 11510907495749523110336321)
            ·
              refine ⟨8633180621812142332752241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11510907495749523110336321 8633180621812142332752241)
              ·
                refine ⟨6474885466359106749564181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8633180621812142332752241 6474885466359106749564181)
                ·
                  refine ⟨303510256235583128885821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6474885466359106749564181 303510256235583128885821)
                  ·
                    rfl

theorem cell23_5319757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_5319757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319757 prefixEnd_5319757 := by exact prefixLift 5319757
  have htrace : WordTrace (prefixWord ++ tailWord_5319757) baseStart_5319757 baseEnd_5319757 := by
    simpa [prefixWord, tailWord_5319757, baseEnd_5319757] using wordTrace_append hprefix tailTrace_5319757
  have hstable : (prefixWord ++ tailWord_5319757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319757).length < 2 ^ (prefixWord ++ tailWord_5319757).sum := by decide
  have hdescent : baseEnd_5319757 < baseStart_5319757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319774 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5319774 : Nat := 118140960795 + 5319774 * 2 ^ 59
def prefixEnd_5319774 : Nat := 4983230072969 + 3 ^ 40 * 5319774 * 2
def baseEnd_5319774 : Nat := 303511226143486065939979

theorem tailTrace_5319774 : CollatzResearch.WordTrace tailWord_5319774 prefixEnd_5319774 303511226143486065939979 := by
  unfold tailWord_5319774
  simp only [CollatzResearch.WordTrace]
  refine ⟨24253512228671852238917797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129352065219583211940894917 24253512228671852238917797)
  ·
    refine ⟨4547533542875972294797087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24253512228671852238917797 4547533542875972294797087)
    ·
      refine ⟨6821300314313958442195631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547533542875972294797087 6821300314313958442195631)
      ·
        refine ⟨10231950471470937663293447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821300314313958442195631 10231950471470937663293447)
        ·
          refine ⟨15347925707206406494940171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231950471470937663293447 15347925707206406494940171)
          ·
            refine ⟨23021888560809609742410257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15347925707206406494940171 23021888560809609742410257)
            ·
              refine ⟨17266416420607207306807693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23021888560809609742410257 17266416420607207306807693)
              ·
                refine ⟨6474906157727702740052885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17266416420607207306807693 6474906157727702740052885)
                ·
                  refine ⟨303511226143486065939979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6474906157727702740052885 303511226143486065939979)
                  ·
                    rfl

theorem cell23_5319774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5319774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319774 prefixEnd_5319774 := by exact prefixLift 5319774
  have htrace : WordTrace (prefixWord ++ tailWord_5319774) baseStart_5319774 baseEnd_5319774 := by
    simpa [prefixWord, tailWord_5319774, baseEnd_5319774] using wordTrace_append hprefix tailTrace_5319774
  have hstable : (prefixWord ++ tailWord_5319774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319774).length < 2 ^ (prefixWord ++ tailWord_5319774).sum := by decide
  have hdescent : baseEnd_5319774 < baseStart_5319774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319793 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_5319793 : Nat := 118140960795 + 5319793 * 2 ^ 59
def prefixEnd_5319793 : Nat := 4983230072969 + 3 ^ 40 * 5319793 * 2
def baseEnd_5319793 : Nat := 2731610791423810019122223

theorem tailTrace_5319793 : CollatzResearch.WordTrace tailWord_5319793 prefixEnd_5319793 2731610791423810019122223 := by
  unfold tailWord_5319793
  simp only [CollatzResearch.WordTrace]
  refine ⟨194028790816305984156284033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129352527210870656104189355 194028790816305984156284033)
  ·
    refine ⟨145521593112229488117213025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194028790816305984156284033 145521593112229488117213025)
    ·
      refine ⟨109141194834172116087909769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145521593112229488117213025 109141194834172116087909769)
      ·
        refine ⟨81855896125629087065932327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109141194834172116087909769 81855896125629087065932327)
        ·
          refine ⟨122783844188443630598898491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81855896125629087065932327 122783844188443630598898491)
          ·
            refine ⟨184175766282665445898347737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122783844188443630598898491 184175766282665445898347737)
            ·
              refine ⟨138131824711999084423760803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184175766282665445898347737 138131824711999084423760803)
              ·
                refine ⟨207197737067998626635641205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138131824711999084423760803 207197737067998626635641205)
                ·
                  refine ⟨19424787850124871247091363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207197737067998626635641205 19424787850124871247091363)
                  ·
                    refine ⟨29137181775187306870637045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19424787850124871247091363 29137181775187306870637045)
                    ·
                      refine ⟨2731610791423810019122223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29137181775187306870637045 2731610791423810019122223)
                      ·
                        rfl

theorem cell23_5319793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_5319793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319793 prefixEnd_5319793 := by exact prefixLift 5319793
  have htrace : WordTrace (prefixWord ++ tailWord_5319793) baseStart_5319793 baseEnd_5319793 := by
    simpa [prefixWord, tailWord_5319793, baseEnd_5319793] using wordTrace_append hprefix tailTrace_5319793
  have hstable : (prefixWord ++ tailWord_5319793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319793).length < 2 ^ (prefixWord ++ tailWord_5319793).sum := by decide
  have hdescent : baseEnd_5319793 < baseStart_5319793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319801 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 1, 1, 3]
def baseStart_5319801 : Nat := 118140960795 + 5319801 * 2 ^ 59
def prefixEnd_5319801 : Nat := 4983230072969 + 3 ^ 40 * 5319801 * 2
def baseEnd_5319801 : Nat := 2731614899269045987822187

theorem tailTrace_5319801 : CollatzResearch.WordTrace tailWord_5319801 prefixEnd_5319801 2731614899269045987822187 := by
  unfold tailWord_5319801
  simp only [CollatzResearch.WordTrace]
  refine ⟨194029082600277001522575257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129352721733518001015050171 194029082600277001522575257)
  ·
    refine ⟨145521811950207751141931443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194029082600277001522575257 145521811950207751141931443)
    ·
      refine ⟨218282717925311626712897165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145521811950207751141931443 218282717925311626712897165)
      ·
        refine ⟨81856019221991860017336437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218282717925311626712897165 81856019221991860017336437)
        ·
          refine ⟨7674001802061736876625291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81856019221991860017336437 7674001802061736876625291)
          ·
            refine ⟨11511002703092605314937937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674001802061736876625291 11511002703092605314937937)
            ·
              refine ⟨8633252027319453986203453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11511002703092605314937937 8633252027319453986203453)
              ·
                refine ⟨3237469510244795244826295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8633252027319453986203453 3237469510244795244826295)
                ·
                  refine ⟨4856204265367192867239443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237469510244795244826295 4856204265367192867239443)
                  ·
                    refine ⟨7284306398050789300859165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4856204265367192867239443 7284306398050789300859165)
                    ·
                      refine ⟨2731614899269045987822187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284306398050789300859165 2731614899269045987822187)
                      ·
                        rfl

theorem cell23_5319801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_5319801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319801 prefixEnd_5319801 := by exact prefixLift 5319801
  have htrace : WordTrace (prefixWord ++ tailWord_5319801) baseStart_5319801 baseEnd_5319801 := by
    simpa [prefixWord, tailWord_5319801, baseEnd_5319801] using wordTrace_append hprefix tailTrace_5319801
  have hstable : (prefixWord ++ tailWord_5319801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319801).length < 2 ^ (prefixWord ++ tailWord_5319801).sum := by decide
  have hdescent : baseEnd_5319801 < baseStart_5319801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319817 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 2, 4]
def baseStart_5319817 : Nat := 118140960795 + 5319817 * 2 ^ 59
def prefixEnd_5319817 : Nat := 4983230072969 + 3 ^ 40 * 5319817 * 2
def baseEnd_5319817 : Nat := 910541038319839308407371

theorem tailTrace_5319817 : CollatzResearch.WordTrace tailWord_5319817 prefixEnd_5319817 910541038319839308407371 := by
  unfold tailWord_5319817
  simp only [CollatzResearch.WordTrace]
  refine ⟨194029666168219036255157705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129353110778812690836771803 194029666168219036255157705)
  ·
    refine ⟨145522249626164277191368279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194029666168219036255157705 145522249626164277191368279)
    ·
      refine ⟨218283374439246415787052419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145522249626164277191368279 218283374439246415787052419)
      ·
        refine ⟨327425061658869623680578629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218283374439246415787052419 327425061658869623680578629)
        ·
          refine ⟨61392199061038054440108493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327425061658869623680578629 61392199061038054440108493)
          ·
            refine ⟨23022074647889270415040685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61392199061038054440108493 23022074647889270415040685)
            ·
              refine ⟨8633277992958476405640257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23022074647889270415040685 8633277992958476405640257)
              ·
                refine ⟨6474958494718857304230193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8633277992958476405640257 6474958494718857304230193)
                ·
                  refine ⟨4856218871039142978172645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6474958494718857304230193 4856218871039142978172645)
                  ·
                    refine ⟨910541038319839308407371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856218871039142978172645 910541038319839308407371)
                    ·
                      rfl

theorem cell23_5319817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_5319817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319817 prefixEnd_5319817 := by exact prefixLift 5319817
  have htrace : WordTrace (prefixWord ++ tailWord_5319817) baseStart_5319817 baseEnd_5319817 := by
    simpa [prefixWord, tailWord_5319817, baseEnd_5319817] using wordTrace_append hprefix tailTrace_5319817
  have hstable : (prefixWord ++ tailWord_5319817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319817).length < 2 ^ (prefixWord ++ tailWord_5319817).sum := by decide
  have hdescent : baseEnd_5319817 < baseStart_5319817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319843 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 2, 7]
def baseStart_5319843 : Nat := 118140960795 + 5319843 * 2 ^ 59
def prefixEnd_5319843 : Nat := 4983230072969 + 3 ^ 40 * 5319843 * 2
def baseEnd_5319843 : Nat := 910545488485511607832331

theorem tailTrace_5319843 : CollatzResearch.WordTrace tailWord_5319843 prefixEnd_5319843 910545488485511607832331 := by
  unfold tailWord_5319843
  simp only [CollatzResearch.WordTrace]
  refine ⟨194030614466124842695604183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129353742977416561797069455 194030614466124842695604183)
  ·
    refine ⟨291045921699187264043406275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194030614466124842695604183 291045921699187264043406275)
    ·
      refine ⟨436568882548780896065109413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291045921699187264043406275 436568882548780896065109413)
      ·
        refine ⟨81856665477896418012208015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 436568882548780896065109413 81856665477896418012208015)
        ·
          refine ⟨122784998216844627018312023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81856665477896418012208015 122784998216844627018312023)
          ·
            refine ⟨184177497325266940527468035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122784998216844627018312023 184177497325266940527468035)
            ·
              refine ⟨276266245987900410791202053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184177497325266940527468035 276266245987900410791202053)
              ·
                refine ⟨51799921122731327023350385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276266245987900410791202053 51799921122731327023350385)
                ·
                  refine ⟨38849940842048495267512789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51799921122731327023350385 38849940842048495267512789)
                  ·
                    refine ⟨910545488485511607832331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38849940842048495267512789 910545488485511607832331)
                    ·
                      rfl

theorem cell23_5319843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_5319843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319843 prefixEnd_5319843 := by exact prefixLift 5319843
  have htrace : WordTrace (prefixWord ++ tailWord_5319843) baseStart_5319843 baseEnd_5319843 := by
    simpa [prefixWord, tailWord_5319843, baseEnd_5319843] using wordTrace_append hprefix tailTrace_5319843
  have hstable : (prefixWord ++ tailWord_5319843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319843).length < 2 ^ (prefixWord ++ tailWord_5319843).sum := by decide
  have hdescent : baseEnd_5319843 < baseStart_5319843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319844 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_5319844 : Nat := 118140960795 + 5319844 * 2 ^ 59
def prefixEnd_5319844 : Nat := 4983230072969 + 3 ^ 40 * 5319844 * 2
def baseEnd_5319844 : Nat := 2731636978937189319584489

theorem tailTrace_5319844 : CollatzResearch.WordTrace tailWord_5319844 prefixEnd_5319844 2731636978937189319584489 := by
  unfold tailWord_5319844
  simp only [CollatzResearch.WordTrace]
  refine ⟨97015325469560609933195293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129353767292747479910927057 97015325469560609933195293)
  ·
    refine ⟨36380747051085228724948235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97015325469560609933195293 36380747051085228724948235)
    ·
      refine ⟨54571120576627843087422353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36380747051085228724948235 54571120576627843087422353)
      ·
        refine ⟨40928340432470882315566765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54571120576627843087422353 40928340432470882315566765)
        ·
          refine ⟨15348127662176580868337537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40928340432470882315566765 15348127662176580868337537)
          ·
            refine ⟨11511095746632435651253153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15348127662176580868337537 11511095746632435651253153)
            ·
              refine ⟨8633321809974326738439865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11511095746632435651253153 8633321809974326738439865)
              ·
                refine ⟨6474991357480745053829899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8633321809974326738439865 6474991357480745053829899)
                ·
                  refine ⟨9712487036221117580744849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474991357480745053829899 9712487036221117580744849)
                  ·
                    refine ⟨7284365277165838185558637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9712487036221117580744849 7284365277165838185558637)
                    ·
                      refine ⟨2731636978937189319584489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284365277165838185558637 2731636978937189319584489)
                      ·
                        rfl

theorem cell23_5319844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_5319844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319844 prefixEnd_5319844 := by exact prefixLift 5319844
  have htrace : WordTrace (prefixWord ++ tailWord_5319844) baseStart_5319844 baseEnd_5319844 := by
    simpa [prefixWord, tailWord_5319844, baseEnd_5319844] using wordTrace_append hprefix tailTrace_5319844
  have hstable : (prefixWord ++ tailWord_5319844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319844).length < 2 ^ (prefixWord ++ tailWord_5319844).sum := by decide
  have hdescent : baseEnd_5319844 < baseStart_5319844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319847 : List Nat := [1, 1, 6, 2, 1, 1, 4, 7]
def baseStart_5319847 : Nat := 118140960795 + 5319847 * 2 ^ 59
def prefixEnd_5319847 : Nat := 4983230072969 + 3 ^ 40 * 5319847 * 2
def baseEnd_5319847 : Nat := 101171797014042696586925

theorem tailTrace_5319847 : CollatzResearch.WordTrace tailWord_5319847 prefixEnd_5319847 101171797014042696586925 := by
  unfold tailWord_5319847
  simp only [CollatzResearch.WordTrace]
  refine ⟨194030760358110351378749795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129353840238740234252499863 194030760358110351378749795)
  ·
    refine ⟨291046140537165527068124693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194030760358110351378749795 291046140537165527068124693)
    ·
      refine ⟨13642787837679634081318345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 291046140537165527068124693 13642787837679634081318345)
      ·
        refine ⟨10232090878259725560988759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13642787837679634081318345 10232090878259725560988759)
        ·
          refine ⟨15348136317389588341483139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10232090878259725560988759 15348136317389588341483139)
          ·
            refine ⟨23022204476084382512224709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15348136317389588341483139 23022204476084382512224709)
            ·
              refine ⟨4316663339265821721042133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23022204476084382512224709 4316663339265821721042133)
              ·
                refine ⟨101171797014042696586925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4316663339265821721042133 101171797014042696586925)
                ·
                  rfl

theorem cell23_5319847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 7].length) (baseStart_5319847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319847 prefixEnd_5319847 := by exact prefixLift 5319847
  have htrace : WordTrace (prefixWord ++ tailWord_5319847) baseStart_5319847 baseEnd_5319847 := by
    simpa [prefixWord, tailWord_5319847, baseEnd_5319847] using wordTrace_append hprefix tailTrace_5319847
  have hstable : (prefixWord ++ tailWord_5319847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319847).length < 2 ^ (prefixWord ++ tailWord_5319847).sum := by decide
  have hdescent : baseEnd_5319847 < baseStart_5319847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319858 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_5319858 : Nat := 118140960795 + 5319858 * 2 ^ 59
def prefixEnd_5319858 : Nat := 4983230072969 + 3 ^ 40 * 5319858 * 2
def baseEnd_5319858 : Nat := 2731644167666352264809425

theorem tailTrace_5319858 : CollatzResearch.WordTrace tailWord_5319858 prefixEnd_5319858 2731644167666352264809425 := by
  unfold tailWord_5319858
  simp only [CollatzResearch.WordTrace]
  refine ⟨48507790390267625064350057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129354107707380333504933485 48507790390267625064350057)
  ·
    refine ⟨36380842792700718798262543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48507790390267625064350057 36380842792700718798262543)
    ·
      refine ⟨54571264189051078197393815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36380842792700718798262543 54571264189051078197393815)
      ·
        refine ⟨81856896283576617296090723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54571264189051078197393815 81856896283576617296090723)
        ·
          refine ⟨122785344425364925944136085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81856896283576617296090723 122785344425364925944136085)
          ·
            refine ⟨5755563019938980903631379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122785344425364925944136085 5755563019938980903631379)
            ·
              refine ⟨8633344529908471355447069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755563019938980903631379 8633344529908471355447069)
              ·
                refine ⟨3237504198715676758292651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8633344529908471355447069 3237504198715676758292651)
                ·
                  refine ⟨4856256298073515137438977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237504198715676758292651 4856256298073515137438977)
                  ·
                    refine ⟨3642192223555136353079233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4856256298073515137438977 3642192223555136353079233)
                    ·
                      refine ⟨2731644167666352264809425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642192223555136353079233 2731644167666352264809425)
                      ·
                        rfl

theorem cell23_5319858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_5319858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319858 prefixEnd_5319858 := by exact prefixLift 5319858
  have htrace : WordTrace (prefixWord ++ tailWord_5319858) baseStart_5319858 baseEnd_5319858 := by
    simpa [prefixWord, tailWord_5319858, baseEnd_5319858] using wordTrace_append hprefix tailTrace_5319858
  have hstable : (prefixWord ++ tailWord_5319858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319858).length < 2 ^ (prefixWord ++ tailWord_5319858).sum := by decide
  have hdescent : baseEnd_5319858 < baseStart_5319858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319885 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5319885 : Nat := 118140960795 + 5319885 * 2 ^ 59
def prefixEnd_5319885 : Nat := 4983230072969 + 3 ^ 40 * 5319885 * 2
def baseEnd_5319885 : Nat := 910552677214674553057267

theorem tailTrace_5319885 : CollatzResearch.WordTrace tailWord_5319885 prefixEnd_5319885 910552677214674553057267 := by
  unfold tailWord_5319885
  simp only [CollatzResearch.WordTrace]
  refine ⟨194032146331972683868633109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129354764221315122579088739 194032146331972683868633109)
  ·
    refine ⟨9095256859311219556342177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 194032146331972683868633109 9095256859311219556342177)
    ·
      refine ⟨6821442644483414667256633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9095256859311219556342177 6821442644483414667256633)
      ·
        refine ⟨5116081983362561000442475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6821442644483414667256633 5116081983362561000442475)
        ·
          refine ⟨7674122975043841500663713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116081983362561000442475 7674122975043841500663713)
          ·
            refine ⟨5755592231282881125497785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7674122975043841500663713 5755592231282881125497785)
            ·
              refine ⟨4316694173462160844123339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755592231282881125497785 4316694173462160844123339)
              ·
                refine ⟨6475041260193241266185009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316694173462160844123339 6475041260193241266185009)
                ·
                  refine ⟨4856280945144930949638757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6475041260193241266185009 4856280945144930949638757)
                  ·
                    refine ⟨910552677214674553057267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856280945144930949638757 910552677214674553057267)
                    ·
                      rfl

theorem cell23_5319885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5319885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319885 prefixEnd_5319885 := by exact prefixLift 5319885
  have htrace : WordTrace (prefixWord ++ tailWord_5319885) baseStart_5319885 baseEnd_5319885 := by
    simpa [prefixWord, tailWord_5319885, baseEnd_5319885] using wordTrace_append hprefix tailTrace_5319885
  have hstable : (prefixWord ++ tailWord_5319885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319885).length < 2 ^ (prefixWord ++ tailWord_5319885).sum := by decide
  have hdescent : baseEnd_5319885 < baseStart_5319885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319890 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_5319890 : Nat := 118140960795 + 5319890 * 2 ^ 59
def prefixEnd_5319890 : Nat := 4983230072969 + 3 ^ 40 * 5319890 * 2
def baseEnd_5319890 : Nat := 910553533015765379869759

theorem tailTrace_5319890 : CollatzResearch.WordTrace tailWord_5319890 prefixEnd_5319890 910553533015765379869759 := by
  unfold tailWord_5319890
  simp only [CollatzResearch.WordTrace]
  refine ⟨48508082174238642430641281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129354885797969713148376749 48508082174238642430641281)
  ·
    refine ⟨36381061630678981822980961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48508082174238642430641281 36381061630678981822980961)
    ·
      refine ⟨27285796223009236367235721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36381061630678981822980961 27285796223009236367235721)
      ·
        refine ⟨20464347167256927275426791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27285796223009236367235721 20464347167256927275426791)
        ·
          refine ⟨30696520750885390913140187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20464347167256927275426791 30696520750885390913140187)
          ·
            refine ⟨46044781126328086369710281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30696520750885390913140187 46044781126328086369710281)
            ·
              refine ⟨34533585844746064777282711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46044781126328086369710281 34533585844746064777282711)
              ·
                refine ⟨51800378767119097165924067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34533585844746064777282711 51800378767119097165924067)
                ·
                  refine ⟨77700568150678645748886101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51800378767119097165924067 77700568150678645748886101)
                  ·
                    refine ⟨910553533015765379869759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77700568150678645748886101 910553533015765379869759)
                    ·
                      rfl

theorem cell23_5319890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_5319890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319890 prefixEnd_5319890 := by exact prefixLift 5319890
  have htrace : WordTrace (prefixWord ++ tailWord_5319890) baseStart_5319890 baseEnd_5319890 := by
    simpa [prefixWord, tailWord_5319890, baseEnd_5319890] using wordTrace_append hprefix tailTrace_5319890
  have hstable : (prefixWord ++ tailWord_5319890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319890).length < 2 ^ (prefixWord ++ tailWord_5319890).sum := by decide
  have hdescent : baseEnd_5319890 < baseStart_5319890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319897 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 1, 4, 2]
def baseStart_5319897 : Nat := 118140960795 + 5319897 * 2 ^ 59
def prefixEnd_5319897 : Nat := 4983230072969 + 3 ^ 40 * 5319897 * 2
def baseEnd_5319897 : Nat := 2731664193411877612221745

theorem tailTrace_5319897 : CollatzResearch.WordTrace tailWord_5319897 prefixEnd_5319897 2731664193411877612221745 := by
  unfold tailWord_5319897
  simp only [CollatzResearch.WordTrace]
  refine ⟨194032584007929209918069945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129355056005286139945379963 194032584007929209918069945)
  ·
    refine ⟨145524438005946907438552459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194032584007929209918069945 145524438005946907438552459)
    ·
      refine ⟨218286657008920361157828689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145524438005946907438552459 218286657008920361157828689)
      ·
        refine ⟨163714992756690270868371517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218286657008920361157828689 163714992756690270868371517)
        ·
          refine ⟨61393122283758851575639319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163714992756690270868371517 61393122283758851575639319)
          ·
            refine ⟨92089683425638277363458979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61393122283758851575639319 92089683425638277363458979)
            ·
              refine ⟨138134525138457416045188469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92089683425638277363458979 138134525138457416045188469)
              ·
                refine ⟨12950111731730382754236419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138134525138457416045188469 12950111731730382754236419)
                ·
                  refine ⟨19425167597595574131354629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12950111731730382754236419 19425167597595574131354629)
                  ·
                    refine ⟨3642218924549170149628993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19425167597595574131354629 3642218924549170149628993)
                    ·
                      refine ⟨2731664193411877612221745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642218924549170149628993 2731664193411877612221745)
                      ·
                        rfl

theorem cell23_5319897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_5319897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319897 prefixEnd_5319897 := by exact prefixLift 5319897
  have htrace : WordTrace (prefixWord ++ tailWord_5319897) baseStart_5319897 baseEnd_5319897 := by
    simpa [prefixWord, tailWord_5319897, baseEnd_5319897] using wordTrace_append hprefix tailTrace_5319897
  have hstable : (prefixWord ++ tailWord_5319897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319897).length < 2 ^ (prefixWord ++ tailWord_5319897).sum := by decide
  have hdescent : baseEnd_5319897 < baseStart_5319897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319901 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5319901 : Nat := 118140960795 + 5319901 * 2 ^ 59
def prefixEnd_5319901 : Nat := 4983230072969 + 3 ^ 40 * 5319901 * 2
def baseEnd_5319901 : Nat := 2731666247334495596571727

theorem tailTrace_5319901 : CollatzResearch.WordTrace tailWord_5319901 prefixEnd_5319901 2731666247334495596571727 := by
  unfold tailWord_5319901
  simp only [CollatzResearch.WordTrace]
  refine ⟨194032729899914718601215557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129355153266609812400810371 194032729899914718601215557)
  ·
    refine ⟨36381136856234009737727917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194032729899914718601215557 36381136856234009737727917)
    ·
      refine ⟨13642926321087753651647969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36381136856234009737727917 13642926321087753651647969)
      ·
        refine ⟨10232194740815815238735977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13642926321087753651647969 10232194740815815238735977)
        ·
          refine ⟨7674146055611861429051983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10232194740815815238735977 7674146055611861429051983)
          ·
            refine ⟨11511219083417792143577975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674146055611861429051983 11511219083417792143577975)
            ·
              refine ⟨17266828625126688215366963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511219083417792143577975 17266828625126688215366963)
              ·
                refine ⟨25900242937690032323050445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17266828625126688215366963 25900242937690032323050445)
                ·
                  refine ⟨9712591101633762121143917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25900242937690032323050445 9712591101633762121143917)
                  ·
                    refine ⟨3642221663112660795428969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9712591101633762121143917 3642221663112660795428969)
                    ·
                      refine ⟨2731666247334495596571727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642221663112660795428969 2731666247334495596571727)
                      ·
                        rfl

theorem cell23_5319901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5319901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319901 prefixEnd_5319901 := by exact prefixLift 5319901
  have htrace : WordTrace (prefixWord ++ tailWord_5319901) baseStart_5319901 baseEnd_5319901 := by
    simpa [prefixWord, tailWord_5319901, baseEnd_5319901] using wordTrace_append hprefix tailTrace_5319901
  have hstable : (prefixWord ++ tailWord_5319901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319901).length < 2 ^ (prefixWord ++ tailWord_5319901).sum := by decide
  have hdescent : baseEnd_5319901 < baseStart_5319901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319914 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_5319914 : Nat := 118140960795 + 5319914 * 2 ^ 59
def prefixEnd_5319914 : Nat := 4983230072969 + 3 ^ 40 * 5319914 * 2
def baseEnd_5319914 : Nat := 2731672922583004045709167

theorem tailTrace_5319914 : CollatzResearch.WordTrace tailWord_5319914 prefixEnd_5319914 2731672922583004045709167 := by
  unfold tailWord_5319914
  simp only [CollatzResearch.WordTrace]
  refine ⟨48508301012216905455359699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129355469365911747880959197 48508301012216905455359699)
  ·
    refine ⟨72762451518325358183039549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48508301012216905455359699 72762451518325358183039549)
    ·
      refine ⟨27285919319372009318639831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72762451518325358183039549 27285919319372009318639831)
      ·
        refine ⟨40928878979058013977959747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27285919319372009318639831 40928878979058013977959747)
        ·
          refine ⟨61393318468587020966939621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40928878979058013977959747 61393318468587020966939621)
          ·
            refine ⟨11511247212860066431301179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61393318468587020966939621 11511247212860066431301179)
            ·
              refine ⟨17266870819290099646951769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511247212860066431301179 17266870819290099646951769)
              ·
                refine ⟨12950153114467574735213827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17266870819290099646951769 12950153114467574735213827)
                ·
                  refine ⟨19425229671701362102820741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12950153114467574735213827 19425229671701362102820741)
                  ·
                    refine ⟨3642230563444005394278889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19425229671701362102820741 3642230563444005394278889)
                    ·
                      refine ⟨2731672922583004045709167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642230563444005394278889 2731672922583004045709167)
                      ·
                        rfl

theorem cell23_5319914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_5319914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319914 prefixEnd_5319914 := by exact prefixLift 5319914
  have htrace : WordTrace (prefixWord ++ tailWord_5319914) baseStart_5319914 baseEnd_5319914 := by
    simpa [prefixWord, tailWord_5319914, baseEnd_5319914] using wordTrace_append hprefix tailTrace_5319914
  have hstable : (prefixWord ++ tailWord_5319914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319914).length < 2 ^ (prefixWord ++ tailWord_5319914).sum := by decide
  have hdescent : baseEnd_5319914 < baseStart_5319914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319917 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5319917 : Nat := 118140960795 + 5319917 * 2 ^ 59
def prefixEnd_5319917 : Nat := 4983230072969 + 3 ^ 40 * 5319917 * 2
def baseEnd_5319917 : Nat := 2731674463024967533971653

theorem tailTrace_5319917 : CollatzResearch.WordTrace tailWord_5319917 prefixEnd_5319917 2731674463024967533971653 := by
  unfold tailWord_5319917
  simp only [CollatzResearch.WordTrace]
  refine ⟨194033313467856753333798005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129355542311904502222532003 194033313467856753333798005)
  ·
    refine ⟨18190623137611570625043563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194033313467856753333798005 18190623137611570625043563)
    ·
      refine ⟨27285934706417355937565345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18190623137611570625043563 27285934706417355937565345)
      ·
        refine ⟨20464451029813016953174009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27285934706417355937565345 20464451029813016953174009)
        ·
          refine ⟨15348338272359762714880507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20464451029813016953174009 15348338272359762714880507)
          ·
            refine ⟨23022507408539644072320761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15348338272359762714880507 23022507408539644072320761)
            ·
              refine ⟨17266880556404733054240571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23022507408539644072320761 17266880556404733054240571)
              ·
                refine ⟨25900320834607099581360857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17266880556404733054240571 25900320834607099581360857)
                ·
                  refine ⟨19425240625955324686020643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25900320834607099581360857 19425240625955324686020643)
                  ·
                    refine ⟨29137860938932987029030965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19425240625955324686020643 29137860938932987029030965)
                    ·
                      refine ⟨2731674463024967533971653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29137860938932987029030965 2731674463024967533971653)
                      ·
                        rfl

theorem cell23_5319917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5319917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319917 prefixEnd_5319917 := by exact prefixLift 5319917
  have htrace : WordTrace (prefixWord ++ tailWord_5319917) baseStart_5319917 baseEnd_5319917 := by
    simpa [prefixWord, tailWord_5319917, baseEnd_5319917] using wordTrace_append hprefix tailTrace_5319917
  have hstable : (prefixWord ++ tailWord_5319917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319917).length < 2 ^ (prefixWord ++ tailWord_5319917).sum := by decide
  have hdescent : baseEnd_5319917 < baseStart_5319917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319947 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 3]
def baseStart_5319947 : Nat := 118140960795 + 5319947 * 2 ^ 59
def prefixEnd_5319947 : Nat := 4983230072969 + 3 ^ 40 * 5319947 * 2
def baseEnd_5319947 : Nat := 2731689867444602416596515

theorem tailTrace_5319947 : CollatzResearch.WordTrace tailWord_5319947 prefixEnd_5319947 2731689867444602416596515 := by
  unfold tailWord_5319947
  simp only [CollatzResearch.WordTrace]
  refine ⟨194034407657748068457390095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129356271771832045638260063 194034407657748068457390095)
  ·
    refine ⟨291051611486622102686085143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194034407657748068457390095 291051611486622102686085143)
    ·
      refine ⟨436577417229933154029127715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291051611486622102686085143 436577417229933154029127715)
      ·
        refine ⟨654866125844899731043691573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436577417229933154029127715 654866125844899731043691573)
        ·
          refine ⟨61393699297959349785346085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 654866125844899731043691573 61393699297959349785346085)
          ·
            refine ⟨11511318618367378084752391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61393699297959349785346085 11511318618367378084752391)
            ·
              refine ⟨17266977927551067127128587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511318618367378084752391 17266977927551067127128587)
              ·
                refine ⟨25900466891326600690692881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17266977927551067127128587 25900466891326600690692881)
                ·
                  refine ⟨19425350168494950518019661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25900466891326600690692881 19425350168494950518019661)
                  ·
                    refine ⟨7284506313185606444257373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19425350168494950518019661 7284506313185606444257373)
                    ·
                      refine ⟨2731689867444602416596515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284506313185606444257373 2731689867444602416596515)
                      ·
                        rfl

theorem cell23_5319947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 3].length) (baseStart_5319947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319947 prefixEnd_5319947 := by exact prefixLift 5319947
  have htrace : WordTrace (prefixWord ++ tailWord_5319947) baseStart_5319947 baseEnd_5319947 := by
    simpa [prefixWord, tailWord_5319947, baseEnd_5319947] using wordTrace_append hprefix tailTrace_5319947
  have hstable : (prefixWord ++ tailWord_5319947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319947).length < 2 ^ (prefixWord ++ tailWord_5319947).sum := by decide
  have hdescent : baseEnd_5319947 < baseStart_5319947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319957 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_5319957 : Nat := 118140960795 + 5319957 * 2 ^ 59
def prefixEnd_5319957 : Nat := 4983230072969 + 3 ^ 40 * 5319957 * 2
def baseEnd_5319957 : Nat := 2731695002251147377471469

theorem tailTrace_5319957 : CollatzResearch.WordTrace tailWord_5319957 prefixEnd_5319957 2731695002251147377471469 := by
  unfold tailWord_5319957
  simp only [CollatzResearch.WordTrace]
  refine ⟨194034772387711840165254125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129356514925141226776836083 194034772387711840165254125)
  ·
    refine ⟨72763039645391940061970297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194034772387711840165254125 72763039645391940061970297)
    ·
      refine ⟨54572279734043955046477723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72763039645391940061970297 54572279734043955046477723)
      ·
        refine ⟨81858419601065932569716585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54572279734043955046477723 81858419601065932569716585)
        ·
          refine ⟨61393814700799449427287439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81858419601065932569716585 61393814700799449427287439)
          ·
            refine ⟨92090722051199174140931159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61393814700799449427287439 92090722051199174140931159)
            ·
              refine ⟨138136083076798761211396739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92090722051199174140931159 138136083076798761211396739)
              ·
                refine ⟨207204124615198141817095109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138136083076798761211396739 207204124615198141817095109)
                ·
                  refine ⟨38850773365349651590705333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207204124615198141817095109 38850773365349651590705333)
                  ·
                    refine ⟨3642260003001529836628625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38850773365349651590705333 3642260003001529836628625)
                    ·
                      refine ⟨2731695002251147377471469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642260003001529836628625 2731695002251147377471469)
                      ·
                        rfl

theorem cell23_5319957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_5319957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319957 prefixEnd_5319957 := by exact prefixLift 5319957
  have htrace : WordTrace (prefixWord ++ tailWord_5319957) baseStart_5319957 baseEnd_5319957 := by
    simpa [prefixWord, tailWord_5319957, baseEnd_5319957] using wordTrace_append hprefix tailTrace_5319957
  have hstable : (prefixWord ++ tailWord_5319957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319957).length < 2 ^ (prefixWord ++ tailWord_5319957).sum := by decide
  have hdescent : baseEnd_5319957 < baseStart_5319957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5319967 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 1, 7]
def baseStart_5319967 : Nat := 118140960795 + 5319967 * 2 ^ 59
def prefixEnd_5319967 : Nat := 4983230072969 + 3 ^ 40 * 5319967 * 2
def baseEnd_5319967 : Nat := 910566712352564112782141

theorem tailTrace_5319967 : CollatzResearch.WordTrace tailWord_5319967 prefixEnd_5319967 910566712352564112782141 := by
  unfold tailWord_5319967
  simp only [CollatzResearch.WordTrace]
  refine ⟨194035137117675611873118155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129356758078450407915412103 194035137117675611873118155)
  ·
    refine ⟨291052705676513417809677233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194035137117675611873118155 291052705676513417809677233)
    ·
      refine ⟨218289529257385063357257925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291052705676513417809677233 218289529257385063357257925)
      ·
        refine ⟨40929286735759699379485861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218289529257385063357257925 40929286735759699379485861)
        ·
          refine ⟨7674241262954943633653599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40929286735759699379485861 7674241262954943633653599)
          ·
            refine ⟨11511361894432415450480399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674241262954943633653599 11511361894432415450480399)
            ·
              refine ⟨17267042841648623175720599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511361894432415450480399 17267042841648623175720599)
              ·
                refine ⟨25900564262472934763580899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17267042841648623175720599 25900564262472934763580899)
                ·
                  refine ⟨38850846393709402145371349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25900564262472934763580899 38850846393709402145371349)
                  ·
                    refine ⟨910566712352564112782141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38850846393709402145371349 910566712352564112782141)
                    ·
                      rfl

theorem cell23_5319967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_5319967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5319967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5319967 prefixEnd_5319967 := by exact prefixLift 5319967
  have htrace : WordTrace (prefixWord ++ tailWord_5319967) baseStart_5319967 baseEnd_5319967 := by
    simpa [prefixWord, tailWord_5319967, baseEnd_5319967] using wordTrace_append hprefix tailTrace_5319967
  have hstable : (prefixWord ++ tailWord_5319967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5319967).length < 2 ^ (prefixWord ++ tailWord_5319967).sum := by decide
  have hdescent : baseEnd_5319967 < baseStart_5319967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5319967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320000 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_5320000 : Nat := 118140960795 + 5320000 * 2 ^ 59
def prefixEnd_5320000 : Nat := 4983230072969 + 3 ^ 40 * 5320000 * 2
def baseEnd_5320000 : Nat := 2731717081919290709233771

theorem tailTrace_5320000 : CollatzResearch.WordTrace tailWord_5320000 prefixEnd_5320000 2731717081919290709233771 := by
  unfold tailWord_5320000
  simp only [CollatzResearch.WordTrace]
  refine ⟨97018170363278029254534727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129357560484370705672712969 97018170363278029254534727)
  ·
    refine ⟨145527255544917043881802091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97018170363278029254534727 145527255544917043881802091)
    ·
      refine ⟨218290883317375565822703137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145527255544917043881802091 218290883317375565822703137)
      ·
        refine ⟨163718162488031674367027353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218290883317375565822703137 163718162488031674367027353)
        ·
          refine ⟨122788621866023755775270515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163718162488031674367027353 122788621866023755775270515)
          ·
            refine ⟨184182932799035633662905773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122788621866023755775270515 184182932799035633662905773)
            ·
              refine ⟨69068599799638362623589665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184182932799035633662905773 69068599799638362623589665)
              ·
                refine ⟨51801449849728771967692249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69068599799638362623589665 51801449849728771967692249)
                ·
                  refine ⟨38851087387296578975769187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51801449849728771967692249 38851087387296578975769187)
                  ·
                    refine ⟨58276631080944868463653781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38851087387296578975769187 58276631080944868463653781)
                    ·
                      refine ⟨2731717081919290709233771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58276631080944868463653781 2731717081919290709233771)
                      ·
                        rfl

theorem cell23_5320000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_5320000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320000 prefixEnd_5320000 := by exact prefixLift 5320000
  have htrace : WordTrace (prefixWord ++ tailWord_5320000) baseStart_5320000 baseEnd_5320000 := by
    simpa [prefixWord, tailWord_5320000, baseEnd_5320000] using wordTrace_append hprefix tailTrace_5320000
  have hstable : (prefixWord ++ tailWord_5320000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320000).length < 2 ^ (prefixWord ++ tailWord_5320000).sum := by decide
  have hdescent : baseEnd_5320000 < baseStart_5320000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320004 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5320004 : Nat := 118140960795 + 5320004 * 2 ^ 59
def prefixEnd_5320004 : Nat := 4983230072969 + 3 ^ 40 * 5320004 * 2
def baseEnd_5320004 : Nat := 2731719135841908693583753

theorem tailTrace_5320004 : CollatzResearch.WordTrace tailWord_5320004 prefixEnd_5320004 2731719135841908693583753 := by
  unfold tailWord_5320004
  simp only [CollatzResearch.WordTrace]
  refine ⟨97018243309270783596107533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129357657745694378128143377 97018243309270783596107533)
  ·
    refine ⟨36381841240976543848540325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97018243309270783596107533 36381841240976543848540325)
    ·
      refine ⟨6821595232683101971601311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36381841240976543848540325 6821595232683101971601311)
      ·
        refine ⟨10232392849024652957401967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821595232683101971601311 10232392849024652957401967)
        ·
          refine ⟨15348589273536979436102951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10232392849024652957401967 15348589273536979436102951)
          ·
            refine ⟨23022883910305469154154427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15348589273536979436102951 23022883910305469154154427)
            ·
              refine ⟨34534325865458203731231641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23022883910305469154154427 34534325865458203731231641)
              ·
                refine ⟨25900744399093652798423731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34534325865458203731231641 25900744399093652798423731)
                ·
                  refine ⟨38851116598640479197635597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25900744399093652798423731 38851116598640479197635597)
                  ·
                    refine ⟨14569168724490179699113349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38851116598640479197635597 14569168724490179699113349)
                    ·
                      refine ⟨2731719135841908693583753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14569168724490179699113349 2731719135841908693583753)
                      ·
                        rfl

theorem cell23_5320004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5320004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320004 prefixEnd_5320004 := by exact prefixLift 5320004
  have htrace : WordTrace (prefixWord ++ tailWord_5320004) baseStart_5320004 baseEnd_5320004 := by
    simpa [prefixWord, tailWord_5320004, baseEnd_5320004] using wordTrace_append hprefix tailTrace_5320004
  have hstable : (prefixWord ++ tailWord_5320004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320004).length < 2 ^ (prefixWord ++ tailWord_5320004).sum := by decide
  have hdescent : baseEnd_5320004 < baseStart_5320004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320007 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_5320007 : Nat := 118140960795 + 5320007 * 2 ^ 59
def prefixEnd_5320007 : Nat := 4983230072969 + 3 ^ 40 * 5320007 * 2
def baseEnd_5320007 : Nat := 2731720676283872181846239

theorem tailTrace_5320007 : CollatzResearch.WordTrace tailWord_5320007 prefixEnd_5320007 2731720676283872181846239 := by
  unfold tailWord_5320007
  simp only [CollatzResearch.WordTrace]
  refine ⟨194036596037530698704574275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129357730691687132469716183 194036596037530698704574275)
  ·
    refine ⟨291054894056296048056861413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194036596037530698704574275 291054894056296048056861413)
    ·
      refine ⟨54572792635555509010661515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291054894056296048056861413 54572792635555509010661515)
      ·
        refine ⟨81859188953333263515992273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54572792635555509010661515 81859188953333263515992273)
        ·
          refine ⟨61394391714999947636994205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81859188953333263515992273 61394391714999947636994205)
          ·
            refine ⟨23022896893124980363872827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61394391714999947636994205 23022896893124980363872827)
            ·
              refine ⟨34534345339687470545809241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23022896893124980363872827 34534345339687470545809241)
              ·
                refine ⟨25900759004765602909356931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34534345339687470545809241 25900759004765602909356931)
                ·
                  refine ⟨38851138507148404364035397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25900759004765602909356931 38851138507148404364035397)
                  ·
                    refine ⟨7284588470090325818256637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38851138507148404364035397 7284588470090325818256637)
                    ·
                      refine ⟨2731720676283872181846239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284588470090325818256637 2731720676283872181846239)
                      ·
                        rfl

theorem cell23_5320007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_5320007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320007 prefixEnd_5320007 := by exact prefixLift 5320007
  have htrace : WordTrace (prefixWord ++ tailWord_5320007) baseStart_5320007 baseEnd_5320007 := by
    simpa [prefixWord, tailWord_5320007, baseEnd_5320007] using wordTrace_append hprefix tailTrace_5320007
  have hstable : (prefixWord ++ tailWord_5320007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320007).length < 2 ^ (prefixWord ++ tailWord_5320007).sum := by decide
  have hdescent : baseEnd_5320007 < baseStart_5320007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320022 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_5320022 : Nat := 118140960795 + 5320022 * 2 ^ 59
def prefixEnd_5320022 : Nat := 4983230072969 + 3 ^ 40 * 5320022 * 2
def baseEnd_5320022 : Nat := 303525375388187735906519

theorem tailTrace_5320022 : CollatzResearch.WordTrace tailWord_5320022 prefixEnd_5320022 303525375388187735906519 := by
  unfold tailWord_5320022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127321445779772266648145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129358095421650904177580213 12127321445779772266648145)
  ·
    refine ⟨9095491084334829199986109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12127321445779772266648145 9095491084334829199986109)
    ·
      refine ⟨3410809156625560949994791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9095491084334829199986109 3410809156625560949994791)
      ·
        refine ⟨5116213734938341424992187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410809156625560949994791 5116213734938341424992187)
        ·
          refine ⟨7674320602407512137488281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116213734938341424992187 7674320602407512137488281)
          ·
            refine ⟨5755740451805634103116211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7674320602407512137488281 5755740451805634103116211)
            ·
              refine ⟨8633610677708451154674317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755740451805634103116211 8633610677708451154674317)
              ·
                refine ⟨3237604004140669183002869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8633610677708451154674317 3237604004140669183002869)
                ·
                  refine ⟨303525375388187735906519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3237604004140669183002869 303525375388187735906519)
                  ·
                    rfl

theorem cell23_5320022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_5320022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320022 prefixEnd_5320022 := by exact prefixLift 5320022
  have htrace : WordTrace (prefixWord ++ tailWord_5320022) baseStart_5320022 baseEnd_5320022 := by
    simpa [prefixWord, tailWord_5320022, baseEnd_5320022] using wordTrace_append hprefix tailTrace_5320022
  have hstable : (prefixWord ++ tailWord_5320022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320022).length < 2 ^ (prefixWord ++ tailWord_5320022).sum := by decide
  have hdescent : baseEnd_5320022 < baseStart_5320022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320144 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 6, 1, 3]
def baseStart_5320144 : Nat := 118140960795 + 5320144 * 2 ^ 59
def prefixEnd_5320144 : Nat := 4983230072969 + 3 ^ 40 * 5320144 * 2
def baseEnd_5320144 : Nat := 2731791023133538145833109

theorem tailTrace_5320144 : CollatzResearch.WordTrace tailWord_5320144 prefixEnd_5320144 2731791023133538145833109 := by
  unfold tailWord_5320144
  simp only [CollatzResearch.WordTrace]
  refine ⟨97020796419017185551155743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129361061892022914068207657 97020796419017185551155743)
  ·
    refine ⟨145531194628525778326733615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97020796419017185551155743 145531194628525778326733615)
    ·
      refine ⟨218296791942788667490100423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145531194628525778326733615 218296791942788667490100423)
      ·
        refine ⟨327445187914183001235150635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218296791942788667490100423 327445187914183001235150635)
        ·
          refine ⟨491167781871274501852725953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327445187914183001235150635 491167781871274501852725953)
          ·
            refine ⟨368375836403455876389544465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491167781871274501852725953 368375836403455876389544465)
            ·
              refine ⟨276281877302591907292158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368375836403455876389544465 276281877302591907292158349)
              ·
                refine ⟨103605703988471965234559381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276281877302591907292158349 103605703988471965234559381)
                ·
                  refine ⟨4856517374459623370369971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103605703988471965234559381 4856517374459623370369971)
                  ·
                    refine ⟨7284776061689435055554957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4856517374459623370369971 7284776061689435055554957)
                    ·
                      refine ⟨2731791023133538145833109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284776061689435055554957 2731791023133538145833109)
                      ·
                        rfl

theorem cell23_5320144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_5320144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320144 prefixEnd_5320144 := by exact prefixLift 5320144
  have htrace : WordTrace (prefixWord ++ tailWord_5320144) baseStart_5320144 baseEnd_5320144 := by
    simpa [prefixWord, tailWord_5320144, baseEnd_5320144] using wordTrace_append hprefix tailTrace_5320144
  have hstable : (prefixWord ++ tailWord_5320144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320144).length < 2 ^ (prefixWord ++ tailWord_5320144).sum := by decide
  have hdescent : baseEnd_5320144 < baseStart_5320144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320148 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_5320148 : Nat := 118140960795 + 5320148 * 2 ^ 59
def prefixEnd_5320148 : Nat := 4983230072969 + 3 ^ 40 * 5320148 * 2
def baseEnd_5320148 : Nat := 2731793077056156130183091

theorem tailTrace_5320148 : CollatzResearch.WordTrace tailWord_5320148 prefixEnd_5320148 2731793077056156130183091 := by
  unfold tailWord_5320148
  simp only [CollatzResearch.WordTrace]
  refine ⟨97020869365009939892728549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129361159153346586523638065 97020869365009939892728549)
  ·
    refine ⟨18191413005939363729886603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97020869365009939892728549 18191413005939363729886603)
    ·
      refine ⟨27287119508909045594829905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18191413005939363729886603 27287119508909045594829905)
      ·
        refine ⟨20465339631681784196122429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27287119508909045594829905 20465339631681784196122429)
        ·
          refine ⟨7674502361880669073545911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20465339631681784196122429 7674502361880669073545911)
          ·
            refine ⟨11511753542821003610318867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674502361880669073545911 11511753542821003610318867)
            ·
              refine ⟨17267630314231505415478301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511753542821003610318867 17267630314231505415478301)
              ·
                refine ⟨6475361367836814530804363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17267630314231505415478301 6475361367836814530804363)
                ·
                  refine ⟨9713042051755221796206545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6475361367836814530804363 9713042051755221796206545)
                  ·
                    refine ⟨7284781538816416347154909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9713042051755221796206545 7284781538816416347154909)
                    ·
                      refine ⟨2731793077056156130183091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284781538816416347154909 2731793077056156130183091)
                      ·
                        rfl

theorem cell23_5320148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_5320148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320148 prefixEnd_5320148 := by exact prefixLift 5320148
  have htrace : WordTrace (prefixWord ++ tailWord_5320148) baseStart_5320148 baseEnd_5320148 := by
    simpa [prefixWord, tailWord_5320148, baseEnd_5320148] using wordTrace_append hprefix tailTrace_5320148
  have hstable : (prefixWord ++ tailWord_5320148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320148).length < 2 ^ (prefixWord ++ tailWord_5320148).sum := by decide
  have hdescent : baseEnd_5320148 < baseStart_5320148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320161 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_5320161 : Nat := 118140960795 + 5320161 * 2 ^ 59
def prefixEnd_5320161 : Nat := 4983230072969 + 3 ^ 40 * 5320161 * 2
def baseEnd_5320161 : Nat := 2731799752304664579320531

theorem tailTrace_5320161 : CollatzResearch.WordTrace tailWord_5320161 prefixEnd_5320161 2731799752304664579320531 := by
  unfold tailWord_5320161
  simp only [CollatzResearch.WordTrace]
  refine ⟨194042212878972783005680337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129361475252648522003786891 194042212878972783005680337)
  ·
    refine ⟨145531659659229587254260253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194042212878972783005680337 145531659659229587254260253)
    ·
      refine ⟨54574372372211095220347595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145531659659229587254260253 54574372372211095220347595)
      ·
        refine ⟨81861558558316642830521393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54574372372211095220347595 81861558558316642830521393)
        ·
          refine ⟨61396168918737482122891045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81861558558316642830521393 61396168918737482122891045)
          ·
            refine ⟨11511781672263277898042071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61396168918737482122891045 11511781672263277898042071)
            ·
              refine ⟨17267672508394916847063107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511781672263277898042071 17267672508394916847063107)
              ·
                refine ⟨25901508762592375270594661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17267672508394916847063107 25901508762592375270594661)
                ·
                  refine ⟨4856532892986070363236499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25901508762592375270594661 4856532892986070363236499)
                  ·
                    refine ⟨7284799339479105544854749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4856532892986070363236499 7284799339479105544854749)
                    ·
                      refine ⟨2731799752304664579320531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284799339479105544854749 2731799752304664579320531)
                      ·
                        rfl

theorem cell23_5320161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_5320161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320161 prefixEnd_5320161 := by exact prefixLift 5320161
  have htrace : WordTrace (prefixWord ++ tailWord_5320161) baseStart_5320161 baseEnd_5320161 := by
    simpa [prefixWord, tailWord_5320161, baseEnd_5320161] using wordTrace_append hprefix tailTrace_5320161
  have hstable : (prefixWord ++ tailWord_5320161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320161).length < 2 ^ (prefixWord ++ tailWord_5320161).sum := by decide
  have hdescent : baseEnd_5320161 < baseStart_5320161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320178 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5320178 : Nat := 118140960795 + 5320178 * 2 ^ 59
def prefixEnd_5320178 : Nat := 4983230072969 + 3 ^ 40 * 5320178 * 2
def baseEnd_5320178 : Nat := 2731808481475791012807953

theorem tailTrace_5320178 : CollatzResearch.WordTrace tailWord_5320178 prefixEnd_5320178 2731808481475791012807953 := by
  unfold tailWord_5320178
  simp only [CollatzResearch.WordTrace]
  refine ⟨48510708229977798727262297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129361888613274129939366125 48510708229977798727262297)
  ·
    refine ⟨36383031172483349045446723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48510708229977798727262297 36383031172483349045446723)
    ·
      refine ⟨54574546758725023568170085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36383031172483349045446723 54574546758725023568170085)
      ·
        refine ⟨10232727517260941919031891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54574546758725023568170085 10232727517260941919031891)
        ·
          refine ⟨15349091275891412878547837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10232727517260941919031891 15349091275891412878547837)
          ·
            refine ⟨5755909228459279829455439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15349091275891412878547837 5755909228459279829455439)
            ·
              refine ⟨8633863842688919744183159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755909228459279829455439 8633863842688919744183159)
              ·
                refine ⟨12950795764033379616274739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8633863842688919744183159 12950795764033379616274739)
                ·
                  refine ⟨19426193646050069424412109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12950795764033379616274739 19426193646050069424412109)
                  ·
                    refine ⟨7284822617268776034154541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19426193646050069424412109 7284822617268776034154541)
                    ·
                      refine ⟨2731808481475791012807953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284822617268776034154541 2731808481475791012807953)
                      ·
                        rfl

theorem cell23_5320178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5320178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320178 prefixEnd_5320178 := by exact prefixLift 5320178
  have htrace : WordTrace (prefixWord ++ tailWord_5320178) baseStart_5320178 baseEnd_5320178 := by
    simpa [prefixWord, tailWord_5320178, baseEnd_5320178] using wordTrace_append hprefix tailTrace_5320178
  have hstable : (prefixWord ++ tailWord_5320178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320178).length < 2 ^ (prefixWord ++ tailWord_5320178).sum := by decide
  have hdescent : baseEnd_5320178 < baseStart_5320178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320187 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5]
def baseStart_5320187 : Nat := 118140960795 + 5320187 * 2 ^ 59
def prefixEnd_5320187 : Nat := 4983230072969 + 3 ^ 40 * 5320187 * 2
def baseEnd_5320187 : Nat := 2731813102801681477595411

theorem tailTrace_5320187 : CollatzResearch.WordTrace tailWord_5320187 prefixEnd_5320187 2731813102801681477595411 := by
  unfold tailWord_5320187
  simp only [CollatzResearch.WordTrace]
  refine ⟨194043161176878589446126815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129362107451252392964084543 194043161176878589446126815)
  ·
    refine ⟨291064741765317884169190223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194043161176878589446126815 291064741765317884169190223)
    ·
      refine ⟨436597112647976826253785335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291064741765317884169190223 436597112647976826253785335)
      ·
        refine ⟨654895668971965239380678003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436597112647976826253785335 654895668971965239380678003)
        ·
          refine ⟨982343503457947859071017005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654895668971965239380678003 982343503457947859071017005)
          ·
            refine ⟨368378813796730447151631377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 982343503457947859071017005 368378813796730447151631377)
            ·
              refine ⟨276284110347547835363723533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368378813796730447151631377 276284110347547835363723533)
              ·
                refine ⟨103606541380330438261396325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276284110347547835363723533 103606541380330438261396325)
                ·
                  refine ⟨19426226508811957174011811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103606541380330438261396325 19426226508811957174011811)
                  ·
                    refine ⟨29139339763217935761017717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19426226508811957174011811 29139339763217935761017717)
                    ·
                      refine ⟨2731813102801681477595411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29139339763217935761017717 2731813102801681477595411)
                      ·
                        rfl

theorem cell23_5320187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_5320187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320187 prefixEnd_5320187 := by exact prefixLift 5320187
  have htrace : WordTrace (prefixWord ++ tailWord_5320187) baseStart_5320187 baseEnd_5320187 := by
    simpa [prefixWord, tailWord_5320187, baseEnd_5320187] using wordTrace_append hprefix tailTrace_5320187
  have hstable : (prefixWord ++ tailWord_5320187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320187).length < 2 ^ (prefixWord ++ tailWord_5320187).sum := by decide
  have hdescent : baseEnd_5320187 < baseStart_5320187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320201 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 6, 2, 2]
def baseStart_5320201 : Nat := 118140960795 + 5320201 * 2 ^ 59
def prefixEnd_5320201 : Nat := 4983230072969 + 3 ^ 40 * 5320201 * 2
def baseEnd_5320201 : Nat := 2731820291530844422820347

theorem tailTrace_5320201 : CollatzResearch.WordTrace tailWord_5320201 prefixEnd_5320201 2731820291530844422820347 := by
  unfold tailWord_5320201
  simp only [CollatzResearch.WordTrace]
  refine ⟨194043671798827869837136457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129362447865885246558090971 194043671798827869837136457)
  ·
    refine ⟨145532753849120902377852343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194043671798827869837136457 145532753849120902377852343)
    ·
      refine ⟨218299130773681353566778515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145532753849120902377852343 218299130773681353566778515)
      ·
        refine ⟨327448696160522030350167773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218299130773681353566778515 327448696160522030350167773)
        ·
          refine ⟨122793261060195761381312915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327448696160522030350167773 122793261060195761381312915)
          ·
            refine ⟨184189891590293642071969373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122793261060195761381312915 184189891590293642071969373)
            ·
              refine ⟨69071209346360115776988515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184189891590293642071969373 69071209346360115776988515)
              ·
                refine ⟨103606814019540173665482773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69071209346360115776988515 103606814019540173665482773)
                ·
                  refine ⟨4856569407165945640569505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103606814019540173665482773 4856569407165945640569505)
                  ·
                    refine ⟨3642427055374459230427129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4856569407165945640569505 3642427055374459230427129)
                    ·
                      refine ⟨2731820291530844422820347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642427055374459230427129 2731820291530844422820347)
                      ·
                        rfl

theorem cell23_5320201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 2, 2].length) (baseStart_5320201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320201 prefixEnd_5320201 := by exact prefixLift 5320201
  have htrace : WordTrace (prefixWord ++ tailWord_5320201) baseStart_5320201 baseEnd_5320201 := by
    simpa [prefixWord, tailWord_5320201, baseEnd_5320201] using wordTrace_append hprefix tailTrace_5320201
  have hstable : (prefixWord ++ tailWord_5320201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320201).length < 2 ^ (prefixWord ++ tailWord_5320201).sum := by decide
  have hdescent : baseEnd_5320201 < baseStart_5320201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320218 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2]
def baseStart_5320218 : Nat := 118140960795 + 5320218 * 2 ^ 59
def prefixEnd_5320218 : Nat := 4983230072969 + 3 ^ 40 * 5320218 * 2
def baseEnd_5320218 : Nat := 2731829020701970856307769

theorem tailTrace_5320218 : CollatzResearch.WordTrace tailWord_5320218 prefixEnd_5320218 2731829020701970856307769 := by
  unfold tailWord_5320218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48511072959941570435126327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129362861226510854493670205 48511072959941570435126327)
  ·
    refine ⟨72766609439912355652689491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48511072959941570435126327 72766609439912355652689491)
    ·
      refine ⟨109149914159868533479034237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72766609439912355652689491 109149914159868533479034237)
      ·
        refine ⟨40931217809950700054637839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109149914159868533479034237 40931217809950700054637839)
        ·
          refine ⟨61396826714926050081956759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40931217809950700054637839 61396826714926050081956759)
          ·
            refine ⟨92095240072389075122935139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61396826714926050081956759 92095240072389075122935139)
            ·
              refine ⟨138142860108583612684402709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92095240072389075122935139 138142860108583612684402709)
              ·
                refine ⟨6475446567589856844581377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138142860108583612684402709 6475446567589856844581377)
                ·
                  refine ⟨4856584925692392633436033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6475446567589856844581377 4856584925692392633436033)
                  ·
                    refine ⟨3642438694269294475077025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4856584925692392633436033 3642438694269294475077025)
                    ·
                      refine ⟨2731829020701970856307769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642438694269294475077025 2731829020701970856307769)
                      ·
                        rfl

theorem cell23_5320218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_5320218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320218 prefixEnd_5320218 := by exact prefixLift 5320218
  have htrace : WordTrace (prefixWord ++ tailWord_5320218) baseStart_5320218 baseEnd_5320218 := by
    simpa [prefixWord, tailWord_5320218, baseEnd_5320218] using wordTrace_append hprefix tailTrace_5320218
  have hstable : (prefixWord ++ tailWord_5320218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320218).length < 2 ^ (prefixWord ++ tailWord_5320218).sum := by decide
  have hdescent : baseEnd_5320218 < baseStart_5320218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320285 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5320285 : Nat := 118140960795 + 5320285 * 2 ^ 59
def prefixEnd_5320285 : Nat := 4983230072969 + 3 ^ 40 * 5320285 * 2
def baseEnd_5320285 : Nat := 2731863423905822094169961

theorem tailTrace_5320285 : CollatzResearch.WordTrace tailWord_5320285 prefixEnd_5320285 2731863423905822094169961 := by
  unfold tailWord_5320285
  simp only [CollatzResearch.WordTrace]
  refine ⟨194046735530523552183194309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129364490353682368122129539 194046735530523552183194309)
  ·
    refine ⟨36383762911973166034348933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194046735530523552183194309 36383762911973166034348933)
    ·
      refine ⟨6821955545994968631440425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36383762911973166034348933 6821955545994968631440425)
      ·
        refine ⟨5116466659496226473580319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6821955545994968631440425 5116466659496226473580319)
        ·
          refine ⟨7674699989244339710370479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116466659496226473580319 7674699989244339710370479)
          ·
            refine ⟨11512049983866509565555719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674699989244339710370479 11512049983866509565555719)
            ·
              refine ⟨17268074975799764348333579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11512049983866509565555719 17268074975799764348333579)
              ·
                refine ⟨25902112463699646522500369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17268074975799764348333579 25902112463699646522500369)
                ·
                  refine ⟨19426584347774734891875277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25902112463699646522500369 19426584347774734891875277)
                  ·
                    refine ⟨7284969130415525584453229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19426584347774734891875277 7284969130415525584453229)
                    ·
                      refine ⟨2731863423905822094169961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7284969130415525584453229 2731863423905822094169961)
                      ·
                        rfl

theorem cell23_5320285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5320285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320285 prefixEnd_5320285 := by exact prefixLift 5320285
  have htrace : WordTrace (prefixWord ++ tailWord_5320285) baseStart_5320285 baseEnd_5320285 := by
    simpa [prefixWord, tailWord_5320285, baseEnd_5320285] using wordTrace_append hprefix tailTrace_5320285
  have hstable : (prefixWord ++ tailWord_5320285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320285).length < 2 ^ (prefixWord ++ tailWord_5320285).sum := by decide
  have hdescent : baseEnd_5320285 < baseStart_5320285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320291 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 6, 2]
def baseStart_5320291 : Nat := 118140960795 + 5320291 * 2 ^ 59
def prefixEnd_5320291 : Nat := 4983230072969 + 3 ^ 40 * 5320291 * 2
def baseEnd_5320291 : Nat := 2731866504789749070694933

theorem tailTrace_5320291 : CollatzResearch.WordTrace tailWord_5320291 prefixEnd_5320291 2731866504789749070694933 := by
  unfold tailWord_5320291
  simp only [CollatzResearch.WordTrace]
  refine ⟨194046954368501815207912727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129364636245667876805275151 194046954368501815207912727)
  ·
    refine ⟨291070431552752722811869091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194046954368501815207912727 291070431552752722811869091)
    ·
      refine ⟨436605647329129084217803637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291070431552752722811869091 436605647329129084217803637)
      ·
        refine ⟨40931779437105851645419091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 436605647329129084217803637 40931779437105851645419091)
        ·
          refine ⟨61397669155658777468128637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40931779437105851645419091 61397669155658777468128637)
          ·
            refine ⟨23024125933372041550548239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61397669155658777468128637 23024125933372041550548239)
            ·
              refine ⟨34536188900058062325822359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23024125933372041550548239 34536188900058062325822359)
              ·
                refine ⟨51804283350087093488733539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34536188900058062325822359 51804283350087093488733539)
                ·
                  refine ⟨77706425025130640233100309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51804283350087093488733539 77706425025130640233100309)
                  ·
                    refine ⟨3642488673052998760926577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77706425025130640233100309 3642488673052998760926577)
                    ·
                      refine ⟨2731866504789749070694933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642488673052998760926577 2731866504789749070694933)
                      ·
                        rfl

theorem cell23_5320291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_5320291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320291 prefixEnd_5320291 := by exact prefixLift 5320291
  have htrace : WordTrace (prefixWord ++ tailWord_5320291) baseStart_5320291 baseEnd_5320291 := by
    simpa [prefixWord, tailWord_5320291, baseEnd_5320291] using wordTrace_append hprefix tailTrace_5320291
  have hstable : (prefixWord ++ tailWord_5320291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320291).length < 2 ^ (prefixWord ++ tailWord_5320291).sum := by decide
  have hdescent : baseEnd_5320291 < baseStart_5320291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320364 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_5320364 : Nat := 118140960795 + 5320364 * 2 ^ 59
def prefixEnd_5320364 : Nat := 4983230072969 + 3 ^ 40 * 5320364 * 2
def baseEnd_5320364 : Nat := 2731903988877527285082097

theorem tailTrace_5320364 : CollatzResearch.WordTrace tailWord_5320364 prefixEnd_5320364 2731903988877527285082097 := by
  unfold tailWord_5320364
  simp only [CollatzResearch.WordTrace]
  refine ⟨97024808448618674337660073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129366411264824899116880097 97024808448618674337660073)
  ·
    refine ⟨72768606336464005753245055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97024808448618674337660073 72768606336464005753245055)
    ·
      refine ⟨109152909504696008629867583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72768606336464005753245055 109152909504696008629867583)
      ·
        refine ⟨163729364257044012944801375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109152909504696008629867583 163729364257044012944801375)
        ·
          refine ⟨245594046385566019417202063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163729364257044012944801375 245594046385566019417202063)
          ·
            refine ⟨368391069578349029125803095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245594046385566019417202063 368391069578349029125803095)
            ·
              refine ⟨552586604367523543688704643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368391069578349029125803095 552586604367523543688704643)
              ·
                refine ⟨828879906551285315533056965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552586604367523543688704643 828879906551285315533056965)
                ·
                  refine ⟨155414982478365996662448181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828879906551285315533056965 155414982478365996662448181)
                  ·
                    refine ⟨14570154607346812187104517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155414982478365996662448181 14570154607346812187104517)
                    ·
                      refine ⟨2731903988877527285082097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14570154607346812187104517 2731903988877527285082097)
                      ·
                        rfl

theorem cell23_5320364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_5320364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320364 prefixEnd_5320364 := by exact prefixLift 5320364
  have htrace : WordTrace (prefixWord ++ tailWord_5320364) baseStart_5320364 baseEnd_5320364 := by
    simpa [prefixWord, tailWord_5320364, baseEnd_5320364] using wordTrace_append hprefix tailTrace_5320364
  have hstable : (prefixWord ++ tailWord_5320364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320364).length < 2 ^ (prefixWord ++ tailWord_5320364).sum := by decide
  have hdescent : baseEnd_5320364 < baseStart_5320364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320386 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5320386 : Nat := 118140960795 + 5320386 * 2 ^ 59
def prefixEnd_5320386 : Nat := 4983230072969 + 3 ^ 40 * 5320386 * 2
def baseEnd_5320386 : Nat := 910638428483975399668999

theorem tailTrace_5320386 : CollatzResearch.WordTrace tailWord_5320386 prefixEnd_5320386 910638428483975399668999 := by
  unfold tailWord_5320386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48512604825789411608155253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129366946202105097621747341 48512604825789411608155253)
  ·
    refine ⟨4548056702417757338264555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48512604825789411608155253 4548056702417757338264555)
    ·
      refine ⟨6822085053626636007396833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4548056702417757338264555 6822085053626636007396833)
      ·
        refine ⟨5116563790219977005547625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6822085053626636007396833 5116563790219977005547625)
        ·
          refine ⟨3837422842664982754160719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5116563790219977005547625 3837422842664982754160719)
          ·
            refine ⟨5756134263997474131241079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837422842664982754160719 5756134263997474131241079)
            ·
              refine ⟨8634201395996211196861619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756134263997474131241079 8634201395996211196861619)
              ·
                refine ⟨12951302093994316795292429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8634201395996211196861619 12951302093994316795292429)
                ·
                  refine ⟨4856738285247868798234661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12951302093994316795292429 4856738285247868798234661)
                  ·
                    refine ⟨910638428483975399668999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856738285247868798234661 910638428483975399668999)
                    ·
                      rfl

theorem cell23_5320386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5320386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320386 prefixEnd_5320386 := by exact prefixLift 5320386
  have htrace : WordTrace (prefixWord ++ tailWord_5320386) baseStart_5320386 baseEnd_5320386 := by
    simpa [prefixWord, tailWord_5320386, baseEnd_5320386] using wordTrace_append hprefix tailTrace_5320386
  have hstable : (prefixWord ++ tailWord_5320386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320386).length < 2 ^ (prefixWord ++ tailWord_5320386).sum := by decide
  have hdescent : baseEnd_5320386 < baseStart_5320386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320391 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 4, 4]
def baseStart_5320391 : Nat := 118140960795 + 5320391 * 2 ^ 59
def prefixEnd_5320391 : Nat := 4983230072969 + 3 ^ 40 * 5320391 * 2
def baseEnd_5320391 : Nat := 910639284285066226481491

theorem tailTrace_5320391 : CollatzResearch.WordTrace tailWord_5320391 prefixEnd_5320391 910639284285066226481491 := by
  unfold tailWord_5320391
  simp only [CollatzResearch.WordTrace]
  refine ⟨194050601668139532286553027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129367067778759688191035351 194050601668139532286553027)
  ·
    refine ⟨291075902502209298429829541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194050601668139532286553027 291075902502209298429829541)
    ·
      refine ⟨54576731719164243455593039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291075902502209298429829541 54576731719164243455593039)
      ·
        refine ⟨81865097578746365183389559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54576731719164243455593039 81865097578746365183389559)
        ·
          refine ⟨122797646368119547775084339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81865097578746365183389559 122797646368119547775084339)
          ·
            refine ⟨184196469552179321662626509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122797646368119547775084339 184196469552179321662626509)
            ·
              refine ⟨69073676082067245623484941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184196469552179321662626509 69073676082067245623484941)
              ·
                refine ⟨25902628530775217108806853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69073676082067245623484941 25902628530775217108806853)
                ·
                  refine ⟨4856742849520353207901285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25902628530775217108806853 4856742849520353207901285)
                  ·
                    refine ⟨910639284285066226481491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856742849520353207901285 910639284285066226481491)
                    ·
                      rfl

theorem cell23_5320391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_5320391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320391 prefixEnd_5320391 := by exact prefixLift 5320391
  have htrace : WordTrace (prefixWord ++ tailWord_5320391) baseStart_5320391 baseEnd_5320391 := by
    simpa [prefixWord, tailWord_5320391, baseEnd_5320391] using wordTrace_append hprefix tailTrace_5320391
  have hstable : (prefixWord ++ tailWord_5320391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320391).length < 2 ^ (prefixWord ++ tailWord_5320391).sum := by decide
  have hdescent : baseEnd_5320391 < baseStart_5320391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320392 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_5320392 : Nat := 118140960795 + 5320392 * 2 ^ 59
def prefixEnd_5320392 : Nat := 4983230072969 + 3 ^ 40 * 5320392 * 2
def baseEnd_5320392 : Nat := 2731918366335853175531969

theorem tailTrace_5320392 : CollatzResearch.WordTrace tailWord_5320392 prefixEnd_5320392 2731918366335853175531969 := by
  unfold tailWord_5320392
  simp only [CollatzResearch.WordTrace]
  refine ⟨97025319070567954728669715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129367092094090606304892953 97025319070567954728669715)
  ·
    refine ⟨145537978605851932093004573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97025319070567954728669715 145537978605851932093004573)
    ·
      refine ⟨54576741977194474534876715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145537978605851932093004573 54576741977194474534876715)
      ·
        refine ⟨81865112965791711802315073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54576741977194474534876715 81865112965791711802315073)
        ·
          refine ⟨61398834724343783851736305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81865112965791711802315073 61398834724343783851736305)
          ·
            refine ⟨46049126043257837888802229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61398834724343783851736305 46049126043257837888802229)
            ·
              refine ⟨4317105566555422302075209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46049126043257837888802229 4317105566555422302075209)
              ·
                refine ⟨3237829174916566726556407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4317105566555422302075209 3237829174916566726556407)
                ·
                  refine ⟨4856743762374850089834611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237829174916566726556407 4856743762374850089834611)
                  ·
                    refine ⟨7285115643562275134751917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4856743762374850089834611 7285115643562275134751917)
                    ·
                      refine ⟨2731918366335853175531969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7285115643562275134751917 2731918366335853175531969)
                      ·
                        rfl

theorem cell23_5320392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_5320392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320392 prefixEnd_5320392 := by exact prefixLift 5320392
  have htrace : WordTrace (prefixWord ++ tailWord_5320392) baseStart_5320392 baseEnd_5320392 := by
    simpa [prefixWord, tailWord_5320392, baseEnd_5320392] using wordTrace_append hprefix tailTrace_5320392
  have hstable : (prefixWord ++ tailWord_5320392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320392).length < 2 ^ (prefixWord ++ tailWord_5320392).sum := by decide
  have hdescent : baseEnd_5320392 < baseStart_5320392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320401 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_5320401 : Nat := 118140960795 + 5320401 * 2 ^ 59
def prefixEnd_5320401 : Nat := 4983230072969 + 3 ^ 40 * 5320401 * 2
def baseEnd_5320401 : Nat := 2731922987661743640319427

theorem tailTrace_5320401 : CollatzResearch.WordTrace tailWord_5320401 prefixEnd_5320401 2731922987661743640319427 := by
  unfold tailWord_5320401
  simp only [CollatzResearch.WordTrace]
  refine ⟨194050966398103303994417057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129367310932068869329611371 194050966398103303994417057)
  ·
    refine ⟨145538224798577477995812793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194050966398103303994417057 145538224798577477995812793)
    ·
      refine ⟨109153668598933108496859595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145538224798577477995812793 109153668598933108496859595)
      ·
        refine ⟨163730502898399662745289393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109153668598933108496859595 163730502898399662745289393)
        ·
          refine ⟨122797877173799747058967045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163730502898399662745289393 122797877173799747058967045)
          ·
            refine ⟨23024601970087452573556321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122797877173799747058967045 23024601970087452573556321)
            ·
              refine ⟨17268451477565589430167241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23024601970087452573556321 17268451477565589430167241)
              ·
                refine ⟨12951338608174192072625431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17268451477565589430167241 12951338608174192072625431)
                ·
                  refine ⟨19427007912261288108938147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12951338608174192072625431 19427007912261288108938147)
                  ·
                    refine ⟨29140511868391932163407221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19427007912261288108938147 29140511868391932163407221)
                    ·
                      refine ⟨2731922987661743640319427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29140511868391932163407221 2731922987661743640319427)
                      ·
                        rfl

theorem cell23_5320401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_5320401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320401 prefixEnd_5320401 := by exact prefixLift 5320401
  have htrace : WordTrace (prefixWord ++ tailWord_5320401) baseStart_5320401 baseEnd_5320401 := by
    simpa [prefixWord, tailWord_5320401, baseEnd_5320401] using wordTrace_append hprefix tailTrace_5320401
  have hstable : (prefixWord ++ tailWord_5320401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320401).length < 2 ^ (prefixWord ++ tailWord_5320401).sum := by decide
  have hdescent : baseEnd_5320401 < baseStart_5320401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320408 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 2, 4]
def baseStart_5320408 : Nat := 118140960795 + 5320408 * 2 ^ 59
def prefixEnd_5320408 : Nat := 4983230072969 + 3 ^ 40 * 5320408 * 2
def baseEnd_5320408 : Nat := 910642194008775037643965

theorem tailTrace_5320408 : CollatzResearch.WordTrace tailWord_5320408 prefixEnd_5320408 910642194008775037643965 := by
  unfold tailWord_5320408
  simp only [CollatzResearch.WordTrace]
  refine ⟨97025610854538972094960939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129367481139385296126614585 97025610854538972094960939)
  ·
    refine ⟨145538416281808458142441409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97025610854538972094960939 145538416281808458142441409)
    ·
      refine ⟨109153812211356343606831057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145538416281808458142441409 109153812211356343606831057)
      ·
        refine ⟨81865359158517257705123293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109153812211356343606831057 81865359158517257705123293)
        ·
          refine ⟨30699509684443971639421235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81865359158517257705123293 30699509684443971639421235)
          ·
            refine ⟨46049264526665957459131853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30699509684443971639421235 46049264526665957459131853)
            ·
              refine ⟨17268474197499734047174445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46049264526665957459131853 17268474197499734047174445)
              ·
                refine ⟨6475677824062400267690417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17268474197499734047174445 6475677824062400267690417)
                ·
                  refine ⟨4856758368046800200767813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6475677824062400267690417 4856758368046800200767813)
                  ·
                    refine ⟨910642194008775037643965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856758368046800200767813 910642194008775037643965)
                    ·
                      rfl

theorem cell23_5320408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_5320408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320408 prefixEnd_5320408 := by exact prefixLift 5320408
  have htrace : WordTrace (prefixWord ++ tailWord_5320408) baseStart_5320408 baseEnd_5320408 := by
    simpa [prefixWord, tailWord_5320408, baseEnd_5320408] using wordTrace_append hprefix tailTrace_5320408
  have hstable : (prefixWord ++ tailWord_5320408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320408).length < 2 ^ (prefixWord ++ tailWord_5320408).sum := by decide
  have hdescent : baseEnd_5320408 < baseStart_5320408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320412 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5320412 : Nat := 118140960795 + 5320412 * 2 ^ 59
def prefixEnd_5320412 : Nat := 4983230072969 + 3 ^ 40 * 5320412 * 2
def baseEnd_5320412 : Nat := 910642878649647699093959

theorem tailTrace_5320412 : CollatzResearch.WordTrace tailWord_5320412 prefixEnd_5320412 910642878649647699093959 := by
  unfold tailWord_5320412
  simp only [CollatzResearch.WordTrace]
  refine ⟨97025683800531726436533745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129367578400708968582044993 97025683800531726436533745)
  ·
    refine ⟨72769262850398794827400309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97025683800531726436533745 72769262850398794827400309)
    ·
      refine ⟨6822118392224887015068779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72769262850398794827400309 6822118392224887015068779)
      ·
        refine ⟨10233177588337330522603169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822118392224887015068779 10233177588337330522603169)
        ·
          refine ⟨7674883191252997891952377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10233177588337330522603169 7674883191252997891952377)
          ·
            refine ⟨5756162393439748418964283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7674883191252997891952377 5756162393439748418964283)
            ·
              refine ⟨8634243590159622628446425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756162393439748418964283 8634243590159622628446425)
              ·
                refine ⟨6475682692619716971334819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8634243590159622628446425 6475682692619716971334819)
                ·
                  refine ⟨9713524038929575457002229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6475682692619716971334819 9713524038929575457002229)
                  ·
                    refine ⟨910642878649647699093959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9713524038929575457002229 910642878649647699093959)
                    ·
                      rfl

theorem cell23_5320412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5320412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320412 prefixEnd_5320412 := by exact prefixLift 5320412
  have htrace : WordTrace (prefixWord ++ tailWord_5320412) baseStart_5320412 baseEnd_5320412 := by
    simpa [prefixWord, tailWord_5320412, baseEnd_5320412] using wordTrace_append hprefix tailTrace_5320412
  have hstable : (prefixWord ++ tailWord_5320412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320412).length < 2 ^ (prefixWord ++ tailWord_5320412).sum := by decide
  have hdescent : baseEnd_5320412 < baseStart_5320412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320449 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_5320449 : Nat := 118140960795 + 5320449 * 2 ^ 59
def prefixEnd_5320449 : Nat := 4983230072969 + 3 ^ 40 * 5320449 * 2
def baseEnd_5320449 : Nat := 2731947634733159452519207

theorem tailTrace_5320449 : CollatzResearch.WordTrace tailWord_5320449 prefixEnd_5320449 2731947634733159452519207 := by
  unfold tailWord_5320449
  simp only [CollatzResearch.WordTrace]
  refine ⟨194052717101929408192164401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129368478067952938794776267 194052717101929408192164401)
  ·
    refine ⟨145539537826447056144123301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194052717101929408192164401 145539537826447056144123301)
    ·
      refine ⟨27288663342458823027023119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145539537826447056144123301 27288663342458823027023119)
      ·
        refine ⟨40932995013688234540534679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27288663342458823027023119 40932995013688234540534679)
        ·
          refine ⟨61399492520532351810802019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40932995013688234540534679 61399492520532351810802019)
          ·
            refine ⟨92099238780798527716203029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61399492520532351810802019 92099238780798527716203029)
            ·
              refine ⟨4317151817849930986697017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92099238780798527716203029 4317151817849930986697017)
              ·
                refine ⟨3237863863387448240022763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4317151817849930986697017 3237863863387448240022763)
                ·
                  refine ⟨4856795795081172360034145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237863863387448240022763 4856795795081172360034145)
                  ·
                    refine ⟨3642596846310879270025609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4856795795081172360034145 3642596846310879270025609)
                    ·
                      refine ⟨2731947634733159452519207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642596846310879270025609 2731947634733159452519207)
                      ·
                        rfl

theorem cell23_5320449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_5320449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320449 prefixEnd_5320449 := by exact prefixLift 5320449
  have htrace : WordTrace (prefixWord ++ tailWord_5320449) baseStart_5320449 baseEnd_5320449 := by
    simpa [prefixWord, tailWord_5320449, baseEnd_5320449] using wordTrace_append hprefix tailTrace_5320449
  have hstable : (prefixWord ++ tailWord_5320449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320449).length < 2 ^ (prefixWord ++ tailWord_5320449).sum := by decide
  have hdescent : baseEnd_5320449 < baseStart_5320449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320455 : List Nat := [1, 1, 4, 4, 3, 1, 1, 8]
def baseStart_5320455 : Nat := 118140960795 + 5320455 * 2 ^ 59
def prefixEnd_5320455 : Nat := 4983230072969 + 3 ^ 40 * 5320455 * 2
def baseEnd_5320455 : Nat := 101183359837669867742377

theorem tailTrace_5320455 : CollatzResearch.WordTrace tailWord_5320455 prefixEnd_5320455 101183359837669867742377 := by
  unfold tailWord_5320455
  simp only [CollatzResearch.WordTrace]
  refine ⟨194052935939907671216882819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129368623959938447477921879 194052935939907671216882819)
  ·
    refine ⟨291079403909861506825324229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194052935939907671216882819 291079403909861506825324229)
    ·
      refine ⟨54577388233099032529748293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291079403909861506825324229 54577388233099032529748293)
      ·
        refine ⟨10233260293706068599327805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54577388233099032529748293 10233260293706068599327805)
        ·
          refine ⟨3837472610139775724747927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10233260293706068599327805 3837472610139775724747927)
          ·
            refine ⟨5756208915209663587121891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837472610139775724747927 5756208915209663587121891)
            ·
              refine ⟨8634313372814495380682837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756208915209663587121891 8634313372814495380682837)
              ·
                refine ⟨101183359837669867742377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8634313372814495380682837 101183359837669867742377)
                ·
                  rfl

theorem cell23_5320455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 8].length) (baseStart_5320455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320455 prefixEnd_5320455 := by exact prefixLift 5320455
  have htrace : WordTrace (prefixWord ++ tailWord_5320455) baseStart_5320455 baseEnd_5320455 := by
    simpa [prefixWord, tailWord_5320455, baseEnd_5320455] using wordTrace_append hprefix tailTrace_5320455
  have hstable : (prefixWord ++ tailWord_5320455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320455).length < 2 ^ (prefixWord ++ tailWord_5320455).sum := by decide
  have hdescent : baseEnd_5320455 < baseStart_5320455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320492 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 1, 3, 2]
def baseStart_5320492 : Nat := 118140960795 + 5320492 * 2 ^ 59
def prefixEnd_5320492 : Nat := 4983230072969 + 3 ^ 40 * 5320492 * 2
def baseEnd_5320492 : Nat := 2731969714401302784281509

theorem tailTrace_5320492 : CollatzResearch.WordTrace tailWord_5320492 prefixEnd_5320492 2731969714401302784281509 := by
  unfold tailWord_5320492
  simp only [CollatzResearch.WordTrace]
  refine ⟨97027142720386813267989865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129369523627182417690653153 97027142720386813267989865)
  ·
    refine ⟨72770357040290109950992399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97027142720386813267989865 72770357040290109950992399)
    ·
      refine ⟨109155535560435164926488599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72770357040290109950992399 109155535560435164926488599)
      ·
        refine ⟨163733303340652747389732899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109155535560435164926488599 163733303340652747389732899)
        ·
          refine ⟨245599955010979121084599349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163733303340652747389732899 245599955010979121084599349)
          ·
            refine ⟨23024995782279292601681189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245599955010979121084599349 23024995782279292601681189)
            ·
              refine ⟨4317186709177367362815223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23024995782279292601681189 4317186709177367362815223)
              ·
                refine ⟨6475780063766051044222835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317186709177367362815223 6475780063766051044222835)
                ·
                  refine ⟨9713670095649076566334253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6475780063766051044222835 9713670095649076566334253)
                  ·
                    refine ⟨3642626285868403712375345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9713670095649076566334253 3642626285868403712375345)
                    ·
                      refine ⟨2731969714401302784281509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642626285868403712375345 2731969714401302784281509)
                      ·
                        rfl

theorem cell23_5320492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_5320492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320492 prefixEnd_5320492 := by exact prefixLift 5320492
  have htrace : WordTrace (prefixWord ++ tailWord_5320492) baseStart_5320492 baseEnd_5320492 := by
    simpa [prefixWord, tailWord_5320492, baseEnd_5320492] using wordTrace_append hprefix tailTrace_5320492
  have hstable : (prefixWord ++ tailWord_5320492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320492).length < 2 ^ (prefixWord ++ tailWord_5320492).sum := by decide
  have hdescent : baseEnd_5320492 < baseStart_5320492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320499 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 2, 1, 3]
def baseStart_5320499 : Nat := 118140960795 + 5320499 * 2 ^ 59
def prefixEnd_5320499 : Nat := 4983230072969 + 3 ^ 40 * 5320499 * 2
def baseEnd_5320499 : Nat := 2731973308765884256893977

theorem tailTrace_5320499 : CollatzResearch.WordTrace tailWord_5320499 prefixEnd_5320499 2731973308765884256893977 := by
  unfold tailWord_5320499
  simp only [CollatzResearch.WordTrace]
  refine ⟨194054540751748266731484551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129369693834498844487656367 194054540751748266731484551)
  ·
    refine ⟨291081811127622400097226827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194054540751748266731484551 291081811127622400097226827)
    ·
      refine ⟨436622716691433600145840241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291081811127622400097226827 436622716691433600145840241)
      ·
        refine ⟨327467037518575200109380181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436622716691433600145840241 327467037518575200109380181)
        ·
          refine ⟨3837504345920803126281799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 327467037518575200109380181 3837504345920803126281799)
          ·
            refine ⟨5756256518881204689422699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837504345920803126281799 5756256518881204689422699)
            ·
              refine ⟨8634384778321807034134049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756256518881204689422699 8634384778321807034134049)
              ·
                refine ⟨6475788583741355275600537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8634384778321807034134049 6475788583741355275600537)
                ·
                  refine ⟨4856841437806016456700403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6475788583741355275600537 4856841437806016456700403)
                  ·
                    refine ⟨7285262156709024685050605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4856841437806016456700403 7285262156709024685050605)
                    ·
                      refine ⟨2731973308765884256893977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7285262156709024685050605 2731973308765884256893977)
                      ·
                        rfl

theorem cell23_5320499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 1, 3].length) (baseStart_5320499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320499 prefixEnd_5320499 := by exact prefixLift 5320499
  have htrace : WordTrace (prefixWord ++ tailWord_5320499) baseStart_5320499 baseEnd_5320499 := by
    simpa [prefixWord, tailWord_5320499, baseEnd_5320499] using wordTrace_append hprefix tailTrace_5320499
  have hstable : (prefixWord ++ tailWord_5320499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320499).length < 2 ^ (prefixWord ++ tailWord_5320499).sum := by decide
  have hdescent : baseEnd_5320499 < baseStart_5320499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320565 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5320565 : Nat := 118140960795 + 5320565 * 2 ^ 59
def prefixEnd_5320565 : Nat := 4983230072969 + 3 ^ 40 * 5320565 * 2
def baseEnd_5320565 : Nat := 2732007198489080998668673

theorem tailTrace_5320565 : CollatzResearch.WordTrace tailWord_5320565 prefixEnd_5320565 2732007198489080998668673 := by
  unfold tailWord_5320565
  simp only [CollatzResearch.WordTrace]
  refine ⟨194056947969509160003387149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129371298646339440002258099 194056947969509160003387149)
  ·
    refine ⟨72771355488565935001270181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194056947969509160003387149 72771355488565935001270181)
    ·
      refine ⟨13644629154106112812738159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72771355488565935001270181 13644629154106112812738159)
      ·
        refine ⟨20466943731159169219107239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13644629154106112812738159 20466943731159169219107239)
        ·
          refine ⟨30700415596738753828660859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20466943731159169219107239 30700415596738753828660859)
          ·
            refine ⟨46050623395108130742991289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30700415596738753828660859 46050623395108130742991289)
            ·
              refine ⟨34537967546331098057243467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46050623395108130742991289 34537967546331098057243467)
              ·
                refine ⟨51806951319496647085865201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34537967546331098057243467 51806951319496647085865201)
                ·
                  refine ⟨38855213489622485314398901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51806951319496647085865201 38855213489622485314398901)
                  ·
                    refine ⟨3642676264652107998224897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38855213489622485314398901 3642676264652107998224897)
                    ·
                      refine ⟨2732007198489080998668673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642676264652107998224897 2732007198489080998668673)
                      ·
                        rfl

theorem cell23_5320565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5320565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320565 prefixEnd_5320565 := by exact prefixLift 5320565
  have htrace : WordTrace (prefixWord ++ tailWord_5320565) baseStart_5320565 baseEnd_5320565 := by
    simpa [prefixWord, tailWord_5320565, baseEnd_5320565] using wordTrace_append hprefix tailTrace_5320565
  have hstable : (prefixWord ++ tailWord_5320565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320565).length < 2 ^ (prefixWord ++ tailWord_5320565).sum := by decide
  have hdescent : baseEnd_5320565 < baseStart_5320565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320588 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_5320588 : Nat := 118140960795 + 5320588 * 2 ^ 59
def prefixEnd_5320588 : Nat := 4983230072969 + 3 ^ 40 * 5320588 * 2
def baseEnd_5320588 : Nat := 910673002848044802893689

theorem tailTrace_5320588 : CollatzResearch.WordTrace tailWord_5320588 prefixEnd_5320588 910673002848044802893689 := by
  unfold tailWord_5320588
  simp only [CollatzResearch.WordTrace]
  refine ⟨97028893424212917465737209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129371857898950556620982945 97028893424212917465737209)
  ·
    refine ⟨72771670068159688099302907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97028893424212917465737209 72771670068159688099302907)
    ·
      refine ⟨109157505102239532148954361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72771670068159688099302907 109157505102239532148954361)
      ·
        refine ⟨81868128826679649111715771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109157505102239532148954361 81868128826679649111715771)
        ·
          refine ⟨122802193240019473667573657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81868128826679649111715771 122802193240019473667573657)
          ·
            refine ⟨92101644930014605250680243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122802193240019473667573657 92101644930014605250680243)
            ·
              refine ⟨138152467395021907876020365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92101644930014605250680243 138152467395021907876020365)
              ·
                refine ⟨51807175273133215453507637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138152467395021907876020365 51807175273133215453507637)
                ·
                  refine ⟨4856922681856238948766341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51807175273133215453507637 4856922681856238948766341)
                  ·
                    refine ⟨910673002848044802893689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856922681856238948766341 910673002848044802893689)
                    ·
                      rfl

theorem cell23_5320588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_5320588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320588 prefixEnd_5320588 := by exact prefixLift 5320588
  have htrace : WordTrace (prefixWord ++ tailWord_5320588) baseStart_5320588 baseEnd_5320588 := by
    simpa [prefixWord, tailWord_5320588, baseEnd_5320588] using wordTrace_append hprefix tailTrace_5320588
  have hstable : (prefixWord ++ tailWord_5320588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320588).length < 2 ^ (prefixWord ++ tailWord_5320588).sum := by decide
  have hdescent : baseEnd_5320588 < baseStart_5320588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320601 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 10]
def baseStart_5320601 : Nat := 118140960795 + 5320601 * 2 ^ 59
def prefixEnd_5320601 : Nat := 4983230072969 + 3 ^ 40 * 5320601 * 2
def baseEnd_5320601 : Nat := 303558409310293650868723

theorem tailTrace_5320601 : CollatzResearch.WordTrace tailWord_5320601 prefixEnd_5320601 303558409310293650868723 := by
  unfold tailWord_5320601
  simp only [CollatzResearch.WordTrace]
  refine ⟨194058260997378738151697657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129372173998252492101131771 194058260997378738151697657)
  ·
    refine ⟨145543695748034053613773243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194058260997378738151697657 145543695748034053613773243)
    ·
      refine ⟨218315543622051080420659865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145543695748034053613773243 218315543622051080420659865)
      ·
        refine ⟨163736657716538310315494899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218315543622051080420659865 163736657716538310315494899)
        ·
          refine ⟨245604986574807465473242349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163736657716538310315494899 245604986574807465473242349)
          ·
            refine ⟨92101869965552799552465881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245604986574807465473242349 92101869965552799552465881)
            ·
              refine ⟨69076402474164599664349411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92101869965552799552465881 69076402474164599664349411)
              ·
                refine ⟨103614603711246899496524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69076402474164599664349411 103614603711246899496524117)
                ·
                  refine ⟨303558409310293650868723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103614603711246899496524117 303558409310293650868723)
                  ·
                    rfl

theorem cell23_5320601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_5320601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320601 prefixEnd_5320601 := by exact prefixLift 5320601
  have htrace : WordTrace (prefixWord ++ tailWord_5320601) baseStart_5320601 baseEnd_5320601 := by
    simpa [prefixWord, tailWord_5320601, baseEnd_5320601] using wordTrace_append hprefix tailTrace_5320601
  have hstable : (prefixWord ++ tailWord_5320601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320601).length < 2 ^ (prefixWord ++ tailWord_5320601).sum := by decide
  have hdescent : baseEnd_5320601 < baseStart_5320601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320655 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 1, 5, 2]
def baseStart_5320655 : Nat := 118140960795 + 5320655 * 2 ^ 59
def prefixEnd_5320655 : Nat := 4983230072969 + 3 ^ 40 * 5320655 * 2
def baseEnd_5320655 : Nat := 2732053411747985646543259

theorem tailTrace_5320655 : CollatzResearch.WordTrace tailWord_5320655 prefixEnd_5320655 2732053411747985646543259 := by
  unfold tailWord_5320655
  simp only [CollatzResearch.WordTrace]
  refine ⟨194060230539183105374163419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129373487026122070249442279 194060230539183105374163419)
  ·
    refine ⟨291090345808774658061245129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194060230539183105374163419 291090345808774658061245129)
    ·
      refine ⟨218317759356580993545933847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291090345808774658061245129 218317759356580993545933847)
      ·
        refine ⟨327476639034871490318900771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218317759356580993545933847 327476639034871490318900771)
        ·
          refine ⟨491214958552307235478351157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327476639034871490318900771 491214958552307235478351157)
          ·
            refine ⟨46051402364278803326095421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 491214958552307235478351157 46051402364278803326095421)
            ·
              refine ⟨17269275886604551247285783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46051402364278803326095421 17269275886604551247285783)
              ·
                refine ⟨25903913829906826870928675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17269275886604551247285783 25903913829906826870928675)
                ·
                  refine ⟨38855870744860240306393013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25903913829906826870928675 38855870744860240306393013)
                  ·
                    refine ⟨3642737882330647528724345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38855870744860240306393013 3642737882330647528724345)
                    ·
                      refine ⟨2732053411747985646543259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642737882330647528724345 2732053411747985646543259)
                      ·
                        rfl

theorem cell23_5320655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5, 2].length) (baseStart_5320655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320655 prefixEnd_5320655 := by exact prefixLift 5320655
  have htrace : WordTrace (prefixWord ++ tailWord_5320655) baseStart_5320655 baseEnd_5320655 := by
    simpa [prefixWord, tailWord_5320655, baseEnd_5320655] using wordTrace_append hprefix tailTrace_5320655
  have hstable : (prefixWord ++ tailWord_5320655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320655).length < 2 ^ (prefixWord ++ tailWord_5320655).sum := by decide
  have hdescent : baseEnd_5320655 < baseStart_5320655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320669 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 6]
def baseStart_5320669 : Nat := 118140960795 + 5320669 * 2 ^ 59
def prefixEnd_5320669 : Nat := 4983230072969 + 3 ^ 40 * 5320669 * 2
def baseEnd_5320669 : Nat := 303562288941905399085355

theorem tailTrace_5320669 : CollatzResearch.WordTrace tailWord_5320669 prefixEnd_5320669 303562288941905399085355 := by
  unfold tailWord_5320669
  simp only [CollatzResearch.WordTrace]
  refine ⟨194060741161132385765173061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129373827440754923843448707 194060741161132385765173061)
  ·
    refine ⟨36386388967712322330969949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194060741161132385765173061 36386388967712322330969949)
    ·
      refine ⟨13644895862892120874113731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36386388967712322330969949 13644895862892120874113731)
      ·
        refine ⟨20467343794338181311170597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13644895862892120874113731 20467343794338181311170597)
        ·
          refine ⟨3837626961438408995844487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20467343794338181311170597 3837626961438408995844487)
          ·
            refine ⟨5756440442157613493766731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837626961438408995844487 5756440442157613493766731)
            ·
              refine ⟨8634660663236420240650097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756440442157613493766731 8634660663236420240650097)
              ·
                refine ⟨6475995497427315180487573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8634660663236420240650097 6475995497427315180487573)
                ·
                  refine ⟨303562288941905399085355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6475995497427315180487573 303562288941905399085355)
                  ·
                    rfl

theorem cell23_5320669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_5320669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320669 prefixEnd_5320669 := by exact prefixLift 5320669
  have htrace : WordTrace (prefixWord ++ tailWord_5320669) baseStart_5320669 baseEnd_5320669 := by
    simpa [prefixWord, tailWord_5320669, baseEnd_5320669] using wordTrace_append hprefix tailTrace_5320669
  have hstable : (prefixWord ++ tailWord_5320669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320669).length < 2 ^ (prefixWord ++ tailWord_5320669).sum := by decide
  have hdescent : baseEnd_5320669 < baseStart_5320669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320679 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5320679 : Nat := 118140960795 + 5320679 * 2 ^ 59
def prefixEnd_5320679 : Nat := 4983230072969 + 3 ^ 40 * 5320679 * 2
def baseEnd_5320679 : Nat := 2732065735283693552643149

theorem tailTrace_5320679 : CollatzResearch.WordTrace tailWord_5320679 prefixEnd_5320679 2732065735283693552643149 := by
  unfold tailWord_5320679
  simp only [CollatzResearch.WordTrace]
  refine ⟨194061105891096157473037091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129374070594064104982024727 194061105891096157473037091)
  ·
    refine ⟨291091658836644236209555637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194061105891096157473037091 291091658836644236209555637)
    ·
      refine ⟨27289843015935397144645841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291091658836644236209555637 27289843015935397144645841)
      ·
        refine ⟨20467382261951547858484381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27289843015935397144645841 20467382261951547858484381)
        ·
          refine ⟨7675268348231830446931643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20467382261951547858484381 7675268348231830446931643)
          ·
            refine ⟨11512902522347745670397465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675268348231830446931643 11512902522347745670397465)
            ·
              refine ⟨8634676891760809252798099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11512902522347745670397465 8634676891760809252798099)
              ·
                refine ⟨12952015337641213879197149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8634676891760809252798099 12952015337641213879197149)
                ·
                  refine ⟨4857005751615455204698931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12952015337641213879197149 4857005751615455204698931)
                  ·
                    refine ⟨7285508627423182807048397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857005751615455204698931 7285508627423182807048397)
                    ·
                      refine ⟨2732065735283693552643149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7285508627423182807048397 2732065735283693552643149)
                      ·
                        rfl

theorem cell23_5320679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5320679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320679 prefixEnd_5320679 := by exact prefixLift 5320679
  have htrace : WordTrace (prefixWord ++ tailWord_5320679) baseStart_5320679 baseEnd_5320679 := by
    simpa [prefixWord, tailWord_5320679, baseEnd_5320679] using wordTrace_append hprefix tailTrace_5320679
  have hstable : (prefixWord ++ tailWord_5320679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320679).length < 2 ^ (prefixWord ++ tailWord_5320679).sum := by decide
  have hdescent : baseEnd_5320679 < baseStart_5320679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320688 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_5320688 : Nat := 118140960795 + 5320688 * 2 ^ 59
def prefixEnd_5320688 : Nat := 4983230072969 + 3 ^ 40 * 5320688 * 2
def baseEnd_5320688 : Nat := 2732070356609584017430607

theorem tailTrace_5320688 : CollatzResearch.WordTrace tailWord_5320688 prefixEnd_5320688 2732070356609584017430607 := by
  unfold tailWord_5320688
  simp only [CollatzResearch.WordTrace]
  refine ⟨97030717074031776005057359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129374289432042368006743145 97030717074031776005057359)
  ·
    refine ⟨145546075611047664007586039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97030717074031776005057359 145546075611047664007586039)
    ·
      refine ⟨218319113416571496011379059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145546075611047664007586039 218319113416571496011379059)
      ·
        refine ⟨327478670124857244017068589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218319113416571496011379059 327478670124857244017068589)
        ·
          refine ⟨122804501296821466506400721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327478670124857244017068589 122804501296821466506400721)
          ·
            refine ⟨92103375972616099879800541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122804501296821466506400721 92103375972616099879800541)
            ·
              refine ⟨34538765989731037454925203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92103375972616099879800541 34538765989731037454925203)
              ·
                refine ⟨51808148984596556182387805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34538765989731037454925203 51808148984596556182387805)
                ·
                  refine ⟨19428055869223708568395427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51808148984596556182387805 19428055869223708568395427)
                  ·
                    refine ⟨29142083803835562852593141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19428055869223708568395427 29142083803835562852593141)
                    ·
                      refine ⟨2732070356609584017430607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29142083803835562852593141 2732070356609584017430607)
                      ·
                        rfl

theorem cell23_5320688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_5320688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320688 prefixEnd_5320688 := by exact prefixLift 5320688
  have htrace : WordTrace (prefixWord ++ tailWord_5320688) baseStart_5320688 baseEnd_5320688 := by
    simpa [prefixWord, tailWord_5320688, baseEnd_5320688] using wordTrace_append hprefix tailTrace_5320688
  have hstable : (prefixWord ++ tailWord_5320688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320688).length < 2 ^ (prefixWord ++ tailWord_5320688).sum := by decide
  have hdescent : baseEnd_5320688 < baseStart_5320688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320725 : List Nat := [1, 3, 2, 1, 5, 2, 9]
def baseStart_5320725 : Nat := 118140960795 + 5320725 * 2 ^ 59
def prefixEnd_5320725 : Nat := 4983230072969 + 3 ^ 40 * 5320725 * 2
def baseEnd_5320725 : Nat := 33729498214738276205777

theorem tailTrace_5320725 : CollatzResearch.WordTrace tailWord_5320725 prefixEnd_5320725 33729498214738276205777 := by
  unfold tailWord_5320725
  simp only [CollatzResearch.WordTrace]
  refine ⟨194062783648929507329211629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129375189099286338219474419 194062783648929507329211629)
  ·
    refine ⟨72773543868348565248454361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194062783648929507329211629 72773543868348565248454361)
    ·
      refine ⟨54580157901261423936340771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72773543868348565248454361 54580157901261423936340771)
      ·
        refine ⟨81870236851892135904511157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54580157901261423936340771 81870236851892135904511157)
        ·
          refine ⟨7675334704864887741047921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81870236851892135904511157 7675334704864887741047921)
          ·
            refine ⟨5756501028648665805785941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7675334704864887741047921 5756501028648665805785941)
            ·
              refine ⟨33729498214738276205777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5756501028648665805785941 33729498214738276205777)
              ·
                rfl

theorem cell23_5320725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 9].length) (baseStart_5320725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320725 prefixEnd_5320725 := by exact prefixLift 5320725
  have htrace : WordTrace (prefixWord ++ tailWord_5320725) baseStart_5320725 baseEnd_5320725 := by
    simpa [prefixWord, tailWord_5320725, baseEnd_5320725] using wordTrace_append hprefix tailTrace_5320725
  have hstable : (prefixWord ++ tailWord_5320725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320725).length < 2 ^ (prefixWord ++ tailWord_5320725).sum := by decide
  have hdescent : baseEnd_5320725 < baseStart_5320725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320746 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_5320746 : Nat := 118140960795 + 5320746 * 2 ^ 59
def prefixEnd_5320746 : Nat := 4983230072969 + 3 ^ 40 * 5320746 * 2
def baseEnd_5320746 : Nat := 910700046162514930168447

theorem tailTrace_5320746 : CollatzResearch.WordTrace tailWord_5320746 prefixEnd_5320746 910700046162514930168447 := by
  unfold tailWord_5320746
  simp only [CollatzResearch.WordTrace]
  refine ⟨48515887395463356978931523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129375699721235618610484061 48515887395463356978931523)
  ·
    refine ⟨72773831093195035468397285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48515887395463356978931523 72773831093195035468397285)
    ·
      refine ⟨13645093329974069150324491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72773831093195035468397285 13645093329974069150324491)
      ·
        refine ⟨20467639994961103725486737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13645093329974069150324491 20467639994961103725486737)
        ·
          refine ⟨15350729996220827794115053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20467639994961103725486737 15350729996220827794115053)
          ·
            refine ⟨5756523748582810422793145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15350729996220827794115053 5756523748582810422793145)
            ·
              refine ⟨4317392811437107817094859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5756523748582810422793145 4317392811437107817094859)
              ·
                refine ⟨6476089217155661725642289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317392811437107817094859 6476089217155661725642289)
                ·
                  refine ⟨4857066912866746294231717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6476089217155661725642289 4857066912866746294231717)
                  ·
                    refine ⟨910700046162514930168447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857066912866746294231717 910700046162514930168447)
                    ·
                      rfl

theorem cell23_5320746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_5320746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320746 prefixEnd_5320746 := by exact prefixLift 5320746
  have htrace : WordTrace (prefixWord ++ tailWord_5320746) baseStart_5320746 baseEnd_5320746 := by
    simpa [prefixWord, tailWord_5320746, baseEnd_5320746] using wordTrace_append hprefix tailTrace_5320746
  have hstable : (prefixWord ++ tailWord_5320746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320746).length < 2 ^ (prefixWord ++ tailWord_5320746).sum := by decide
  have hdescent : baseEnd_5320746 < baseStart_5320746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320748 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_5320748 : Nat := 118140960795 + 5320748 * 2 ^ 59
def prefixEnd_5320748 : Nat := 4983230072969 + 3 ^ 40 * 5320748 * 2
def baseEnd_5320748 : Nat := 2732101165448853782680331

theorem tailTrace_5320748 : CollatzResearch.WordTrace tailWord_5320748 prefixEnd_5320748 2732101165448853782680331 := by
  unfold tailWord_5320748
  simp only [CollatzResearch.WordTrace]
  refine ⟨97031811263923091128649449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129375748351897454838199265 97031811263923091128649449)
  ·
    refine ⟨72773858447942318346487087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97031811263923091128649449 72773858447942318346487087)
    ·
      refine ⟨109160787671913477519730631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72773858447942318346487087 109160787671913477519730631)
      ·
        refine ⟨163741181507870216279595947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109160787671913477519730631 163741181507870216279595947)
        ·
          refine ⟨245611772261805324419393921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163741181507870216279595947 245611772261805324419393921)
          ·
            refine ⟨184208829196353993314545441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245611772261805324419393921 184208829196353993314545441)
            ·
              refine ⟨138156621897265494985909081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184208829196353993314545441 138156621897265494985909081)
              ·
                refine ⟨103617466422949121239431811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138156621897265494985909081 103617466422949121239431811)
                ·
                  refine ⟨155426199634423681859147717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103617466422949121239431811 155426199634423681859147717)
                  ·
                    refine ⟨29142412431454440348590197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155426199634423681859147717 29142412431454440348590197)
                    ·
                      refine ⟨2732101165448853782680331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29142412431454440348590197 2732101165448853782680331)
                      ·
                        rfl

theorem cell23_5320748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_5320748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320748 prefixEnd_5320748 := by exact prefixLift 5320748
  have htrace : WordTrace (prefixWord ++ tailWord_5320748) baseStart_5320748 baseEnd_5320748 := by
    simpa [prefixWord, tailWord_5320748, baseEnd_5320748] using wordTrace_append hprefix tailTrace_5320748
  have hstable : (prefixWord ++ tailWord_5320748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320748).length < 2 ^ (prefixWord ++ tailWord_5320748).sum := by decide
  have hdescent : baseEnd_5320748 < baseStart_5320748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320786 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_5320786 : Nat := 118140960795 + 5320786 * 2 ^ 59
def prefixEnd_5320786 : Nat := 4983230072969 + 3 ^ 40 * 5320786 * 2
def baseEnd_5320786 : Nat := 2732120677713724634005157

theorem tailTrace_5320786 : CollatzResearch.WordTrace tailWord_5320786 prefixEnd_5320786 2732120677713724634005157 := by
  unfold tailWord_5320786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48516252125427128686795553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129376672334472343164788141 48516252125427128686795553)
  ·
    refine ⟨36387189094070346515096665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48516252125427128686795553 36387189094070346515096665)
    ·
      refine ⟨27290391820552759886322499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36387189094070346515096665 27290391820552759886322499)
      ·
        refine ⟨40935587730829139829483749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27290391820552759886322499 40935587730829139829483749)
        ·
          refine ⟨7675422699530463718028203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40935587730829139829483749 7675422699530463718028203)
          ·
            refine ⟨11513134049295695577042305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675422699530463718028203 11513134049295695577042305)
            ·
              refine ⟨8634850536971771682781729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11513134049295695577042305 8634850536971771682781729)
              ·
                refine ⟨6476137902728828762086297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8634850536971771682781729 6476137902728828762086297)
                ·
                  refine ⟨4857103427046621571564723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6476137902728828762086297 4857103427046621571564723)
                  ·
                    refine ⟨7285655140569932357347085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857103427046621571564723 7285655140569932357347085)
                    ·
                      refine ⟨2732120677713724634005157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7285655140569932357347085 2732120677713724634005157)
                      ·
                        rfl

theorem cell23_5320786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_5320786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320786 prefixEnd_5320786 := by exact prefixLift 5320786
  have htrace : WordTrace (prefixWord ++ tailWord_5320786) baseStart_5320786 baseEnd_5320786 := by
    simpa [prefixWord, tailWord_5320786, baseEnd_5320786] using wordTrace_append hprefix tailTrace_5320786
  have hstable : (prefixWord ++ tailWord_5320786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320786).length < 2 ^ (prefixWord ++ tailWord_5320786).sum := by decide
  have hdescent : baseEnd_5320786 < baseStart_5320786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320805 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_5320805 : Nat := 118140960795 + 5320805 * 2 ^ 59
def prefixEnd_5320805 : Nat := 4983230072969 + 3 ^ 40 * 5320805 * 2
def baseEnd_5320805 : Nat := 2732130433846160059667569

theorem tailTrace_5320805 : CollatzResearch.WordTrace tailWord_5320805 prefixEnd_5320805 2732130433846160059667569 := by
  unfold tailWord_5320805
  simp only [CollatzResearch.WordTrace]
  refine ⟨194065701488639680992123869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129377134325759787328082579 194065701488639680992123869)
  ·
    refine ⟨72774638058239880372046451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194065701488639680992123869 72774638058239880372046451)
    ·
      refine ⟨109161957087359820558069677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72774638058239880372046451 109161957087359820558069677)
      ·
        refine ⟨40935733907759932709276129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109161957087359820558069677 40935733907759932709276129)
        ·
          refine ⟨30701800430819949531957097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40935733907759932709276129 30701800430819949531957097)
          ·
            refine ⟨23026350323114962148967823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30701800430819949531957097 23026350323114962148967823)
            ·
              refine ⟨34539525484672443223451735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23026350323114962148967823 34539525484672443223451735)
              ·
                refine ⟨51809288227008664835177603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34539525484672443223451735 51809288227008664835177603)
                ·
                  refine ⟨77713932340512997252766405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51809288227008664835177603 77713932340512997252766405)
                  ·
                    refine ⟨14571362313846186984893701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77713932340512997252766405 14571362313846186984893701)
                    ·
                      refine ⟨2732130433846160059667569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14571362313846186984893701 2732130433846160059667569)
                      ·
                        rfl

theorem cell23_5320805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_5320805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320805 prefixEnd_5320805 := by exact prefixLift 5320805
  have htrace : WordTrace (prefixWord ++ tailWord_5320805) baseStart_5320805 baseEnd_5320805 := by
    simpa [prefixWord, tailWord_5320805, baseEnd_5320805] using wordTrace_append hprefix tailTrace_5320805
  have hstable : (prefixWord ++ tailWord_5320805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320805).length < 2 ^ (prefixWord ++ tailWord_5320805).sum := by decide
  have hdescent : baseEnd_5320805 < baseStart_5320805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320809 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 2, 2, 2]
def baseStart_5320809 : Nat := 118140960795 + 5320809 * 2 ^ 59
def prefixEnd_5320809 : Nat := 4983230072969 + 3 ^ 40 * 5320809 * 2
def baseEnd_5320809 : Nat := 2732132487768778044017551

theorem tailTrace_5320809 : CollatzResearch.WordTrace tailWord_5320809 prefixEnd_5320809 2732132487768778044017551 := by
  unfold tailWord_5320809
  simp only [CollatzResearch.WordTrace]
  refine ⟨194065847380625189675269481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129377231587083459783512987 194065847380625189675269481)
  ·
    refine ⟨145549385535468892256452111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194065847380625189675269481 145549385535468892256452111)
    ·
      refine ⟨218324078303203338384678167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145549385535468892256452111 218324078303203338384678167)
      ·
        refine ⟨327486117454805007577017251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218324078303203338384678167 327486117454805007577017251)
        ·
          refine ⟨491229176182207511365525877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327486117454805007577017251 491229176182207511365525877)
          ·
            refine ⟨46052735267081954190518051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 491229176182207511365525877 46052735267081954190518051)
            ·
              refine ⟨69079102900622931285777077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46052735267081954190518051 69079102900622931285777077)
              ·
                refine ⟨6476165896933399808041601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69079102900622931285777077 6476165896933399808041601)
                ·
                  refine ⟨4857124422700049856031201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6476165896933399808041601 4857124422700049856031201)
                  ·
                    refine ⟨3642843317025037392023401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4857124422700049856031201 3642843317025037392023401)
                    ·
                      refine ⟨2732132487768778044017551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642843317025037392023401 2732132487768778044017551)
                      ·
                        rfl

theorem cell23_5320809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 2, 2].length) (baseStart_5320809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320809 prefixEnd_5320809 := by exact prefixLift 5320809
  have htrace : WordTrace (prefixWord ++ tailWord_5320809) baseStart_5320809 baseEnd_5320809 := by
    simpa [prefixWord, tailWord_5320809, baseEnd_5320809] using wordTrace_append hprefix tailTrace_5320809
  have hstable : (prefixWord ++ tailWord_5320809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320809).length < 2 ^ (prefixWord ++ tailWord_5320809).sum := by decide
  have hdescent : baseEnd_5320809 < baseStart_5320809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320815 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 7]
def baseStart_5320815 : Nat := 118140960795 + 5320815 * 2 ^ 59
def prefixEnd_5320815 : Nat := 4983230072969 + 3 ^ 40 * 5320815 * 2
def baseEnd_5320815 : Nat := 303570618739189446726947

theorem tailTrace_5320815 : CollatzResearch.WordTrace tailWord_5320815 prefixEnd_5320815 303570618739189446726947 := by
  unfold tailWord_5320815
  simp only [CollatzResearch.WordTrace]
  refine ⟨194066066218603452699987899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129377377479068968466658599 194066066218603452699987899)
  ·
    refine ⟨291099099327905179049981849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194066066218603452699987899 291099099327905179049981849)
    ·
      refine ⟨218324324495928884287486387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291099099327905179049981849 218324324495928884287486387)
      ·
        refine ⟨327486486743893326431229581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218324324495928884287486387 327486486743893326431229581)
        ·
          refine ⟨122807432528959997411711093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327486486743893326431229581 122807432528959997411711093)
          ·
            refine ⟨11513196799589999757347915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122807432528959997411711093 11513196799589999757347915)
            ·
              refine ⟨17269795199384999636021873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11513196799589999757347915 17269795199384999636021873)
              ·
                refine ⟨12952346399538749727016405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17269795199384999636021873 12952346399538749727016405)
                ·
                  refine ⟨303570618739189446726947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12952346399538749727016405 303570618739189446726947)
                  ·
                    rfl

theorem cell23_5320815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 7].length) (baseStart_5320815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320815 prefixEnd_5320815 := by exact prefixLift 5320815
  have htrace : WordTrace (prefixWord ++ tailWord_5320815) baseStart_5320815 baseEnd_5320815 := by
    simpa [prefixWord, tailWord_5320815, baseEnd_5320815] using wordTrace_append hprefix tailTrace_5320815
  have hstable : (prefixWord ++ tailWord_5320815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320815).length < 2 ^ (prefixWord ++ tailWord_5320815).sum := by decide
  have hdescent : baseEnd_5320815 < baseStart_5320815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320842 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_5320842 : Nat := 118140960795 + 5320842 * 2 ^ 59
def prefixEnd_5320842 : Nat := 4983230072969 + 3 ^ 40 * 5320842 * 2
def baseEnd_5320842 : Nat := 2732149432630376414904899

theorem tailTrace_5320842 : CollatzResearch.WordTrace tailWord_5320842 prefixEnd_5320842 2732149432630376414904899 := by
  unfold tailWord_5320842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48516762747376409077805195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129378033993003757540813853 48516762747376409077805195)
  ·
    refine ⟨72775144121064613616707793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48516762747376409077805195 72775144121064613616707793)
    ·
      refine ⟨54581358090798460212530845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72775144121064613616707793 54581358090798460212530845)
      ·
        refine ⟨20468009284049422579699067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54581358090798460212530845 20468009284049422579699067)
        ·
          refine ⟨30702013926074133869548601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20468009284049422579699067 30702013926074133869548601)
          ·
            refine ⟨23026510444555600402161451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30702013926074133869548601 23026510444555600402161451)
            ·
              refine ⟨34539765666833400603242177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23026510444555600402161451 34539765666833400603242177)
              ·
                refine ⟨25904824250125050452431633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34539765666833400603242177 25904824250125050452431633)
                ·
                  refine ⟨19428618187593787839323725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25904824250125050452431633 19428618187593787839323725)
                  ·
                    refine ⟨7285731820347670439746397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19428618187593787839323725 7285731820347670439746397)
                    ·
                      refine ⟨2732149432630376414904899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7285731820347670439746397 2732149432630376414904899)
                      ·
                        rfl

theorem cell23_5320842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_5320842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320842 prefixEnd_5320842 := by exact prefixLift 5320842
  have htrace : WordTrace (prefixWord ++ tailWord_5320842) baseStart_5320842 baseEnd_5320842 := by
    simpa [prefixWord, tailWord_5320842, baseEnd_5320842] using wordTrace_append hprefix tailTrace_5320842
  have hstable : (prefixWord ++ tailWord_5320842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320842).length < 2 ^ (prefixWord ++ tailWord_5320842).sum := by decide
  have hdescent : baseEnd_5320842 < baseStart_5320842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320854 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5320854 : Nat := 118140960795 + 5320854 * 2 ^ 59
def prefixEnd_5320854 : Nat := 4983230072969 + 3 ^ 40 * 5320854 * 2
def baseEnd_5320854 : Nat := 2732155594398230367954845

theorem tailTrace_5320854 : CollatzResearch.WordTrace tailWord_5320854 prefixEnd_5320854 2732155594398230367954845 := by
  unfold tailWord_5320854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129218041591385147541101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129378325776974774907105077 12129218041591385147541101)
  ·
    refine ⟨4548456765596769430327913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12129218041591385147541101 4548456765596769430327913)
    ·
      refine ⟨3411342574197577072745935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4548456765596769430327913 3411342574197577072745935)
      ·
        refine ⟨5117013861296365609118903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411342574197577072745935 5117013861296365609118903)
        ·
          refine ⟨7675520791944548413678355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117013861296365609118903 7675520791944548413678355)
          ·
            refine ⟨11513281187916822620517533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675520791944548413678355 11513281187916822620517533)
            ·
              refine ⟨4317480445468808482694075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11513281187916822620517533 4317480445468808482694075)
              ·
                refine ⟨6476220668203212724041113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317480445468808482694075 6476220668203212724041113)
                ·
                  refine ⟨4857165501152409543030835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6476220668203212724041113 4857165501152409543030835)
                  ·
                    refine ⟨7285748251728614314546253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857165501152409543030835 7285748251728614314546253)
                    ·
                      refine ⟨2732155594398230367954845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7285748251728614314546253 2732155594398230367954845)
                      ·
                        rfl

theorem cell23_5320854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5320854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320854 prefixEnd_5320854 := by exact prefixLift 5320854
  have htrace : WordTrace (prefixWord ++ tailWord_5320854) baseStart_5320854 baseEnd_5320854 := by
    simpa [prefixWord, tailWord_5320854, baseEnd_5320854] using wordTrace_append hprefix tailTrace_5320854
  have hstable : (prefixWord ++ tailWord_5320854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320854).length < 2 ^ (prefixWord ++ tailWord_5320854).sum := by decide
  have hdescent : baseEnd_5320854 < baseStart_5320854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320882 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5320882 : Nat := 118140960795 + 5320882 * 2 ^ 59
def prefixEnd_5320882 : Nat := 4983230072969 + 3 ^ 40 * 5320882 * 2
def baseEnd_5320882 : Nat := 2732169971856556258404715

theorem tailTrace_5320882 : CollatzResearch.WordTrace tailWord_5320882 prefixEnd_5320882 2732169971856556258404715 := by
  unfold tailWord_5320882
  simp only [CollatzResearch.WordTrace]
  refine ⟨48517127477340180785669225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129379006606240482095117933 48517127477340180785669225)
  ·
    refine ⟨36387845608005135589251919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48517127477340180785669225 36387845608005135589251919)
    ·
      refine ⟨54581768412007703383877879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36387845608005135589251919 54581768412007703383877879)
      ·
        refine ⟨81872652618011555075816819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54581768412007703383877879 81872652618011555075816819)
        ·
          refine ⟨122808978927017332613725229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81872652618011555075816819 122808978927017332613725229)
          ·
            refine ⟨46053367097631499730146961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122808978927017332613725229 46053367097631499730146961)
            ·
              refine ⟨34540025323223624797610221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46053367097631499730146961 34540025323223624797610221)
              ·
                refine ⟨12952509496208859299103833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34540025323223624797610221 12952509496208859299103833)
                ·
                  refine ⟨9714382122156644474327875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12952509496208859299103833 9714382122156644474327875)
                  ·
                    refine ⟨14571573183234966711491813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9714382122156644474327875 14571573183234966711491813)
                    ·
                      refine ⟨2732169971856556258404715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14571573183234966711491813 2732169971856556258404715)
                      ·
                        rfl

theorem cell23_5320882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5320882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320882 prefixEnd_5320882 := by exact prefixLift 5320882
  have htrace : WordTrace (prefixWord ++ tailWord_5320882) baseStart_5320882 baseEnd_5320882 := by
    simpa [prefixWord, tailWord_5320882, baseEnd_5320882] using wordTrace_append hprefix tailTrace_5320882
  have hstable : (prefixWord ++ tailWord_5320882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320882).length < 2 ^ (prefixWord ++ tailWord_5320882).sum := by decide
  have hdescent : baseEnd_5320882 < baseStart_5320882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
