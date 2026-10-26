import V185TrunkScan23Chunk0640

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3790448 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 5]
def baseStart_3790448 : Nat := 118140960795 + 3790448 * 2 ^ 59
def prefixEnd_3790448 : Nat := 4983230072969 + 3 ^ 40 * 3790448 * 2
def baseEnd_3790448 : Nat := 216257968874832343163117

theorem tailTrace_3790448 : CollatzResearch.WordTrace tailWord_3790448 prefixEnd_3790448 216257968874832343163117 := by
  unfold tailWord_3790448
  simp only [CollatzResearch.WordTrace]
  refine ⟨69124498085930863912393999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92165997447907818549858665 69124498085930863912393999)
  ·
    refine ⟨103686747128896295868590999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69124498085930863912393999 103686747128896295868590999)
    ·
      refine ⟨155530120693344443802886499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103686747128896295868590999 155530120693344443802886499)
      ·
        refine ⟨233295181040016665704329749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155530120693344443802886499 233295181040016665704329749)
        ·
          refine ⟨10935711611250781204890457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233295181040016665704329749 10935711611250781204890457)
          ·
            refine ⟨8201783708438085903667843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10935711611250781204890457 8201783708438085903667843)
            ·
              refine ⟨12302675562657128855501765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201783708438085903667843 12302675562657128855501765)
              ·
                refine ⟨2306751667998211660406581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12302675562657128855501765 2306751667998211660406581)
                ·
                  refine ⟨216257968874832343163117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306751667998211660406581 216257968874832343163117)
                  ·
                    rfl

theorem cell23_3790448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 5].length) (baseStart_3790448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790448 prefixEnd_3790448 := by exact prefixLift 3790448
  have htrace : WordTrace (prefixWord ++ tailWord_3790448) baseStart_3790448 baseEnd_3790448 := by
    simpa [prefixWord, tailWord_3790448, baseEnd_3790448] using wordTrace_append hprefix tailTrace_3790448
  have hstable : (prefixWord ++ tailWord_3790448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790448).length < 2 ^ (prefixWord ++ tailWord_3790448).sum := by decide
  have hdescent : baseEnd_3790448 < baseStart_3790448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790478 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_3790478 : Nat := 118140960795 + 3790478 * 2 ^ 59
def prefixEnd_3790478 : Nat := 4983230072969 + 3 ^ 40 * 3790478 * 2
def baseEnd_3790478 : Nat := 648779041431041990364305

theorem tailTrace_3790478 : CollatzResearch.WordTrace tailWord_3790478 prefixEnd_3790478 648779041431041990364305 := by
  unfold tailWord_3790478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281261295219130368547511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92166726907835361965586725 17281261295219130368547511)
  ·
    refine ⟨25921891942828695552821267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17281261295219130368547511 25921891942828695552821267)
    ·
      refine ⟨38882837914243043329231901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25921891942828695552821267 38882837914243043329231901)
      ·
        refine ⟨14581064217841141248461963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38882837914243043329231901 14581064217841141248461963)
        ·
          refine ⟨21871596326761711872692945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14581064217841141248461963 21871596326761711872692945)
          ·
            refine ⟨16403697245071283904519709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21871596326761711872692945 16403697245071283904519709)
            ·
              refine ⟨6151386466901731464194891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16403697245071283904519709 6151386466901731464194891)
              ·
                refine ⟨9227079700352597196292337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151386466901731464194891 9227079700352597196292337)
                ·
                  refine ⟨6920309775264447897219253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9227079700352597196292337 6920309775264447897219253)
                  ·
                    refine ⟨648779041431041990364305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6920309775264447897219253 648779041431041990364305)
                    ·
                      rfl

theorem cell23_3790478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_3790478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790478 prefixEnd_3790478 := by exact prefixLift 3790478
  have htrace : WordTrace (prefixWord ++ tailWord_3790478) baseStart_3790478 baseEnd_3790478 := by
    simpa [prefixWord, tailWord_3790478, baseEnd_3790478] using wordTrace_append hprefix tailTrace_3790478
  have hstable : (prefixWord ++ tailWord_3790478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790478).length < 2 ^ (prefixWord ++ tailWord_3790478).sum := by decide
  have hdescent : baseEnd_3790478 < baseStart_3790478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790481 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_3790481 : Nat := 118140960795 + 3790481 * 2 ^ 59
def prefixEnd_3790481 : Nat := 4983230072969 + 3 ^ 40 * 3790481 * 2
def baseEnd_3790481 : Nat := 1946338664735089459355401

theorem tailTrace_3790481 : CollatzResearch.WordTrace tailWord_3790481 prefixEnd_3790481 1946338664735089459355401 := by
  unfold tailWord_3790481
  simp only [CollatzResearch.WordTrace]
  refine ⟨138250199780742174460739297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92166799853828116307159531 138250199780742174460739297)
  ·
    refine ⟨103687649835556630845554473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138250199780742174460739297 103687649835556630845554473)
    ·
      refine ⟨77765737376667473134165855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103687649835556630845554473 77765737376667473134165855)
      ·
        refine ⟨116648606065001209701248783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77765737376667473134165855 116648606065001209701248783)
        ·
          refine ⟨174972909097501814551873175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116648606065001209701248783 174972909097501814551873175)
          ·
            refine ⟨262459363646252721827809763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174972909097501814551873175 262459363646252721827809763)
            ·
              refine ⟨393689045469379082741714645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262459363646252721827809763 393689045469379082741714645)
              ·
                refine ⟨9227087003188572251758937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 393689045469379082741714645 9227087003188572251758937)
                ·
                  refine ⟨6920315252391429188819203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9227087003188572251758937 6920315252391429188819203)
                  ·
                    refine ⟨10380472878587143783228805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6920315252391429188819203 10380472878587143783228805)
                    ·
                      refine ⟨1946338664735089459355401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10380472878587143783228805 1946338664735089459355401)
                      ·
                        rfl

theorem cell23_3790481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_3790481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790481 prefixEnd_3790481 := by exact prefixLift 3790481
  have htrace : WordTrace (prefixWord ++ tailWord_3790481) baseStart_3790481 baseEnd_3790481 := by
    simpa [prefixWord, tailWord_3790481, baseEnd_3790481] using wordTrace_append hprefix tailTrace_3790481
  have hstable : (prefixWord ++ tailWord_3790481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790481).length < 2 ^ (prefixWord ++ tailWord_3790481).sum := by decide
  have hdescent : baseEnd_3790481 < baseStart_3790481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790521 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 6]
def baseStart_3790521 : Nat := 118140960795 + 3790521 * 2 ^ 59
def prefixEnd_3790521 : Nat := 4983230072969 + 3 ^ 40 * 3790521 * 2
def baseEnd_3790521 : Nat := 216262133773474366983913

theorem tailTrace_3790521 : CollatzResearch.WordTrace tailWord_3790521 prefixEnd_3790521 216262133773474366983913 := by
  unfold tailWord_3790521
  simp only [CollatzResearch.WordTrace]
  refine ⟨138251658700597261292195417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92167772467064840861463611 138251658700597261292195417)
  ·
    refine ⟨103688744025447945969146563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138251658700597261292195417 103688744025447945969146563)
    ·
      refine ⟨155533116038171918953719845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103688744025447945969146563 155533116038171918953719845)
      ·
        refine ⟨29162459257157234803822471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155533116038171918953719845 29162459257157234803822471)
        ·
          refine ⟨43743688885735852205733707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29162459257157234803822471 43743688885735852205733707)
          ·
            refine ⟨65615533328603778308600561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43743688885735852205733707 65615533328603778308600561)
            ·
              refine ⟨49211649996452833731450421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65615533328603778308600561 49211649996452833731450421)
              ·
                refine ⟨4613592187167453162323477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49211649996452833731450421 4613592187167453162323477)
                ·
                  refine ⟨216262133773474366983913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4613592187167453162323477 216262133773474366983913)
                  ·
                    rfl

theorem cell23_3790521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_3790521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790521 prefixEnd_3790521 := by exact prefixLift 3790521
  have htrace : WordTrace (prefixWord ++ tailWord_3790521) baseStart_3790521 baseEnd_3790521 := by
    simpa [prefixWord, tailWord_3790521, baseEnd_3790521] using wordTrace_append hprefix tailTrace_3790521
  have hstable : (prefixWord ++ tailWord_3790521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790521).length < 2 ^ (prefixWord ++ tailWord_3790521).sum := by decide
  have hdescent : baseEnd_3790521 < baseStart_3790521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790588 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3790588 : Nat := 118140960795 + 3790588 * 2 ^ 59
def prefixEnd_3790588 : Nat := 4983230072969 + 3 ^ 40 * 3790588 * 2
def baseEnd_3790588 : Nat := 1946393607165120540717409

theorem tailTrace_3790588 : CollatzResearch.WordTrace tailWord_3790588 prefixEnd_3790588 1946393607165120540717409 := by
  unfold tailWord_3790588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69127051195677265867442209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92169401594236354489922945 69127051195677265867442209)
  ·
    refine ⟨51845288396757949400581657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69127051195677265867442209 51845288396757949400581657)
    ·
      refine ⟨38883966297568462050436243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51845288396757949400581657 38883966297568462050436243)
      ·
        refine ⟨58325949446352693075654365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38883966297568462050436243 58325949446352693075654365)
        ·
          refine ⟨21872231042382259903370387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58325949446352693075654365 21872231042382259903370387)
          ·
            refine ⟨32808346563573389855055581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21872231042382259903370387 32808346563573389855055581)
            ·
              refine ⟨12303129961340021195645843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32808346563573389855055581 12303129961340021195645843)
              ·
                refine ⟨18454694942010031793468765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12303129961340021195645843 18454694942010031793468765)
                ·
                  refine ⟨6920510603253761922550787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18454694942010031793468765 6920510603253761922550787)
                  ·
                    refine ⟨10380765904880642883826181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6920510603253761922550787 10380765904880642883826181)
                    ·
                      refine ⟨1946393607165120540717409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10380765904880642883826181 1946393607165120540717409)
                      ·
                        rfl

theorem cell23_3790588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3790588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790588 prefixEnd_3790588 := by exact prefixLift 3790588
  have htrace : WordTrace (prefixWord ++ tailWord_3790588) baseStart_3790588 baseEnd_3790588 := by
    simpa [prefixWord, tailWord_3790588, baseEnd_3790588] using wordTrace_append hprefix tailTrace_3790588
  have hstable : (prefixWord ++ tailWord_3790588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790588).length < 2 ^ (prefixWord ++ tailWord_3790588).sum := by decide
  have hdescent : baseEnd_3790588 < baseStart_3790588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790591 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_3790591 : Nat := 118140960795 + 3790591 * 2 ^ 59
def prefixEnd_3790591 : Nat := 4983230072969 + 3 ^ 40 * 3790591 * 2
def baseEnd_3790591 : Nat := 1946395147607084028979895

theorem tailTrace_3790591 : CollatzResearch.WordTrace tailWord_3790591 prefixEnd_3790591 1946395147607084028979895 := by
  unfold tailWord_3790591
  simp only [CollatzResearch.WordTrace]
  refine ⟨138254211810343663247243627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92169474540229108831495751 138254211810343663247243627)
  ·
    refine ⟨207381317715515494870865441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138254211810343663247243627 207381317715515494870865441)
    ·
      refine ⟨155535988286636621153149081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207381317715515494870865441 155535988286636621153149081)
      ·
        refine ⟨116651991214977465864861811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155535988286636621153149081 116651991214977465864861811)
        ·
          refine ⟨174977986822466198797292717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116651991214977465864861811 174977986822466198797292717)
          ·
            refine ⟨65616745058424824548984769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174977986822466198797292717 65616745058424824548984769)
            ·
              refine ⟨49212558793818618411738577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65616745058424824548984769 49212558793818618411738577)
              ·
                refine ⟨36909419095363963808803933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49212558793818618411738577 36909419095363963808803933)
                ·
                  refine ⟨13841032160761486428301475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36909419095363963808803933 13841032160761486428301475)
                  ·
                    refine ⟨20761548241142229642452213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13841032160761486428301475 20761548241142229642452213)
                    ·
                      refine ⟨1946395147607084028979895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20761548241142229642452213 1946395147607084028979895)
                      ·
                        rfl

theorem cell23_3790591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_3790591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790591 prefixEnd_3790591 := by exact prefixLift 3790591
  have htrace : WordTrace (prefixWord ++ tailWord_3790591) baseStart_3790591 baseEnd_3790591 := by
    simpa [prefixWord, tailWord_3790591, baseEnd_3790591] using wordTrace_append hprefix tailTrace_3790591
  have hstable : (prefixWord ++ tailWord_3790591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790591).length < 2 ^ (prefixWord ++ tailWord_3790591).sum := by decide
  have hdescent : baseEnd_3790591 < baseStart_3790591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790615 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 2, 4]
def baseStart_3790615 : Nat := 118140960795 + 3790615 * 2 ^ 59
def prefixEnd_3790615 : Nat := 4983230072969 + 3 ^ 40 * 3790615 * 2
def baseEnd_3790615 : Nat := 648802490380930645026595

theorem tailTrace_3790615 : CollatzResearch.WordTrace tailWord_3790615 prefixEnd_3790615 648802490380930645026595 := by
  unfold tailWord_3790615
  simp only [CollatzResearch.WordTrace]
  refine ⟨138255087162256715346117299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92170058108171143564078199 138255087162256715346117299)
  ·
    refine ⟨207382630743385073019175949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138255087162256715346117299 207382630743385073019175949)
    ·
      refine ⟨77768486528769402382190981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207382630743385073019175949 77768486528769402382190981)
      ·
        refine ⟨14581591224144262946660809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77768486528769402382190981 14581591224144262946660809)
        ·
          refine ⟨10936193418108197209995607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14581591224144262946660809 10936193418108197209995607)
          ·
            refine ⟨16404290127162295814993411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936193418108197209995607 16404290127162295814993411)
            ·
              refine ⟨24606435190743443722490117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16404290127162295814993411 24606435190743443722490117)
              ·
                refine ⟨4613706598264395697966897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24606435190743443722490117 4613706598264395697966897)
                ·
                  refine ⟨3460279948698296773475173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4613706598264395697966897 3460279948698296773475173)
                  ·
                    refine ⟨648802490380930645026595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460279948698296773475173 648802490380930645026595)
                    ·
                      rfl

theorem cell23_3790615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_3790615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790615 prefixEnd_3790615 := by exact prefixLift 3790615
  have htrace : WordTrace (prefixWord ++ tailWord_3790615) baseStart_3790615 baseEnd_3790615 := by
    simpa [prefixWord, tailWord_3790615, baseEnd_3790615] using wordTrace_append hprefix tailTrace_3790615
  have hstable : (prefixWord ++ tailWord_3790615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790615).length < 2 ^ (prefixWord ++ tailWord_3790615).sum := by decide
  have hdescent : baseEnd_3790615 < baseStart_3790615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790628 : List Nat := [2, 3, 1, 3, 2, 1, 3, 8]
def baseStart_3790628 : Nat := 118140960795 + 3790628 * 2 ^ 59
def prefixEnd_3790628 : Nat := 4983230072969 + 3 ^ 40 * 3790628 * 2
def baseEnd_3790628 : Nat := 72089412829307421637675

theorem tailTrace_3790628 : CollatzResearch.WordTrace tailWord_3790628 prefixEnd_3790628 72089412829307421637675 := by
  unfold tailWord_3790628
  simp only [CollatzResearch.WordTrace]
  refine ⟨69127780655604809283170269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92170374207473079044227025 69127780655604809283170269)
  ·
    refine ⟨25922917745851803481188851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69127780655604809283170269 25922917745851803481188851)
    ·
      refine ⟨38884376618777705221783277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25922917745851803481188851 38884376618777705221783277)
      ·
        refine ⟨14581641232041639458168729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38884376618777705221783277 14581641232041639458168729)
        ·
          refine ⟨10936230924031229593626547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14581641232041639458168729 10936230924031229593626547)
          ·
            refine ⟨16404346386046844390439821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936230924031229593626547 16404346386046844390439821)
            ·
              refine ⟨6151629894767566646414933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16404346386046844390439821 6151629894767566646414933)
              ·
                refine ⟨72089412829307421637675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6151629894767566646414933 72089412829307421637675)
                ·
                  rfl

theorem cell23_3790628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 8].length) (baseStart_3790628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790628 prefixEnd_3790628 := by exact prefixLift 3790628
  have htrace : WordTrace (prefixWord ++ tailWord_3790628) baseStart_3790628 baseEnd_3790628 := by
    simpa [prefixWord, tailWord_3790628, baseEnd_3790628] using wordTrace_append hprefix tailTrace_3790628
  have hstable : (prefixWord ++ tailWord_3790628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790628).length < 2 ^ (prefixWord ++ tailWord_3790628).sum := by decide
  have hdescent : baseEnd_3790628 < baseStart_3790628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790645 : List Nat := [1, 3, 3, 1, 4, 1, 3, 7]
def baseStart_3790645 : Nat := 118140960795 + 3790645 * 2 ^ 59
def prefixEnd_3790645 : Nat := 4983230072969 + 3 ^ 40 * 3790645 * 2
def baseEnd_3790645 : Nat := 72089736131941733989061

theorem tailTrace_3790645 : CollatzResearch.WordTrace tailWord_3790645 prefixEnd_3790645 72089736131941733989061 := by
  unfold tailWord_3790645
  simp only [CollatzResearch.WordTrace]
  refine ⟨138256181352148030469709389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92170787568098686979806259 138256181352148030469709389)
  ·
    refine ⟨51846068007055511426141021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138256181352148030469709389 51846068007055511426141021)
    ·
      refine ⟨19442275502645816784802883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51846068007055511426141021 19442275502645816784802883)
      ·
        refine ⟨29163413253968725177204325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19442275502645816784802883 29163413253968725177204325)
        ·
          refine ⟨5468139985119135970725811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29163413253968725177204325 5468139985119135970725811)
          ·
            refine ⟨8202209977678703956088717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468139985119135970725811 8202209977678703956088717)
            ·
              refine ⟨3075828741629513983533269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8202209977678703956088717 3075828741629513983533269)
              ·
                refine ⟨72089736131941733989061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3075828741629513983533269 72089736131941733989061)
                ·
                  rfl

theorem cell23_3790645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 7].length) (baseStart_3790645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790645 prefixEnd_3790645 := by exact prefixLift 3790645
  have htrace : WordTrace (prefixWord ++ tailWord_3790645) baseStart_3790645 baseEnd_3790645 := by
    simpa [prefixWord, tailWord_3790645, baseEnd_3790645] using wordTrace_append hprefix tailTrace_3790645
  have hstable : (prefixWord ++ tailWord_3790645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790645).length < 2 ^ (prefixWord ++ tailWord_3790645).sum := by decide
  have hdescent : baseEnd_3790645 < baseStart_3790645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790688 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_3790688 : Nat := 118140960795 + 3790688 * 2 ^ 59
def prefixEnd_3790688 : Nat := 4983230072969 + 3 ^ 40 * 3790688 * 2
def baseEnd_3790688 : Nat := 648814985076856716488983

theorem tailTrace_3790688 : CollatzResearch.WordTrace tailWord_3790688 prefixEnd_3790688 648814985076856716488983 := by
  unfold tailWord_3790688
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128874845496124406762359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92171833127328165875683145 69128874845496124406762359)
  ·
    refine ⟨103693312268244186610143539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69128874845496124406762359 103693312268244186610143539)
    ·
      refine ⟨155539968402366279915215309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103693312268244186610143539 155539968402366279915215309)
      ·
        refine ⟨58327488150887354968205741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155539968402366279915215309 58327488150887354968205741)
        ·
          refine ⟨21872808056582758113077153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58327488150887354968205741 21872808056582758113077153)
          ·
            refine ⟨16404606042437068584807865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21872808056582758113077153 16404606042437068584807865)
            ·
              refine ⟨12303454531827801438605899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16404606042437068584807865 12303454531827801438605899)
              ·
                refine ⟨18455181797741702157908849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12303454531827801438605899 18455181797741702157908849)
                ·
                  refine ⟨13841386348306276618431637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18455181797741702157908849 13841386348306276618431637)
                  ·
                    refine ⟨648814985076856716488983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13841386348306276618431637 648814985076856716488983)
                    ·
                      rfl

theorem cell23_3790688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_3790688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790688 prefixEnd_3790688 := by exact prefixLift 3790688
  have htrace : WordTrace (prefixWord ++ tailWord_3790688) baseStart_3790688 baseEnd_3790688 := by
    simpa [prefixWord, tailWord_3790688, baseEnd_3790688] using wordTrace_append hprefix tailTrace_3790688
  have hstable : (prefixWord ++ tailWord_3790688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790688).length < 2 ^ (prefixWord ++ tailWord_3790688).sum := by decide
  have hdescent : baseEnd_3790688 < baseStart_3790688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790746 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3790746 : Nat := 118140960795 + 3790746 * 2 ^ 59
def prefixEnd_3790746 : Nat := 4983230072969 + 3 ^ 40 * 3790746 * 2
def baseEnd_3790746 : Nat := 1946474737108530922541683

theorem tailTrace_3790746 : CollatzResearch.WordTrace tailWord_3790746 prefixEnd_3790746 1946474737108530922541683 := by
  unfold tailWord_3790746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564966281195531179784023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92173243416521416479424061 34564966281195531179784023)
  ·
    refine ⟨51847449421793296769676035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34564966281195531179784023 51847449421793296769676035)
    ·
      refine ⟨77771174132689945154514053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51847449421793296769676035 77771174132689945154514053)
      ·
        refine ⟨14582095149879364716471385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77771174132689945154514053 14582095149879364716471385)
        ·
          refine ⟨10936571362409523537353539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14582095149879364716471385 10936571362409523537353539)
          ·
            refine ⟨16404857043614285306030309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936571362409523537353539 16404857043614285306030309)
            ·
              refine ⟨3075910695677678494880683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16404857043614285306030309 3075910695677678494880683)
              ·
                refine ⟨4613866043516517742321025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075910695677678494880683 4613866043516517742321025)
                ·
                  refine ⟨3460399532637388306740769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4613866043516517742321025 3460399532637388306740769)
                  ·
                    refine ⟨2595299649478041230055577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460399532637388306740769 2595299649478041230055577)
                    ·
                      refine ⟨1946474737108530922541683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595299649478041230055577 1946474737108530922541683)
                      ·
                        rfl

theorem cell23_3790746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3790746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790746 prefixEnd_3790746 := by exact prefixLift 3790746
  have htrace : WordTrace (prefixWord ++ tailWord_3790746) baseStart_3790746 baseEnd_3790746 := by
    simpa [prefixWord, tailWord_3790746, baseEnd_3790746] using wordTrace_append hprefix tailTrace_3790746
  have hstable : (prefixWord ++ tailWord_3790746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790746).length < 2 ^ (prefixWord ++ tailWord_3790746).sum := by decide
  have hdescent : baseEnd_3790746 < baseStart_3790746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790750 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3790750 : Nat := 118140960795 + 3790750 * 2 ^ 59
def prefixEnd_3790750 : Nat := 4983230072969 + 3 ^ 40 * 3790750 * 2
def baseEnd_3790750 : Nat := 1946476791031148906891665

theorem tailTrace_3790750 : CollatzResearch.WordTrace tailWord_3790750 prefixEnd_3790750 1946476791031148906891665 := by
  unfold tailWord_3790750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17282501377095954175285213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92173340677845088934854469 17282501377095954175285213)
  ·
    refine ⟨6480938016410982815731955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17282501377095954175285213 6480938016410982815731955)
    ·
      refine ⟨9721407024616474223597933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480938016410982815731955 9721407024616474223597933)
      ·
        refine ⟨3645527634231177833849225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9721407024616474223597933 3645527634231177833849225)
        ·
          refine ⟨2734145725673383375386919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645527634231177833849225 2734145725673383375386919)
          ·
            refine ⟨4101218588510075063080379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734145725673383375386919 4101218588510075063080379)
            ·
              refine ⟨6151827882765112594620569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101218588510075063080379 6151827882765112594620569)
              ·
                refine ⟨4613870912073834445965427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6151827882765112594620569 4613870912073834445965427)
                ·
                  refine ⟨6920806368110751668948141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613870912073834445965427 6920806368110751668948141)
                  ·
                    refine ⟨2595302388041531875855553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6920806368110751668948141 2595302388041531875855553)
                    ·
                      refine ⟨1946476791031148906891665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595302388041531875855553 1946476791031148906891665)
                      ·
                        rfl

theorem cell23_3790750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3790750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790750 prefixEnd_3790750 := by exact prefixLift 3790750
  have htrace : WordTrace (prefixWord ++ tailWord_3790750) baseStart_3790750 baseEnd_3790750 := by
    simpa [prefixWord, tailWord_3790750, baseEnd_3790750] using wordTrace_append hprefix tailTrace_3790750
  have hstable : (prefixWord ++ tailWord_3790750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790750).length < 2 ^ (prefixWord ++ tailWord_3790750).sum := by decide
  have hdescent : baseEnd_3790750 < baseStart_3790750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790795 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 3, 4]
def baseStart_3790795 : Nat := 118140960795 + 3790795 * 2 ^ 59
def prefixEnd_3790795 : Nat := 4983230072969 + 3 ^ 40 * 3790795 * 2
def baseEnd_3790795 : Nat := 648833299220200410276319

theorem tailTrace_3790795 : CollatzResearch.WordTrace tailWord_3790795 prefixEnd_3790795 648833299220200410276319 := by
  unfold tailWord_3790795
  simp only [CollatzResearch.WordTrace]
  refine ⟨138261652301604606087669839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92174434867736404058446559 138261652301604606087669839)
  ·
    refine ⟨207392478452406909131504759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138261652301604606087669839 207392478452406909131504759)
    ·
      refine ⟨311088717678610363697257139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207392478452406909131504759 311088717678610363697257139)
      ·
        refine ⟨466633076517915545545885709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311088717678610363697257139 466633076517915545545885709)
        ·
          refine ⟨174987403694218329579707141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466633076517915545545885709 174987403694218329579707141)
          ·
            refine ⟨32810138192665936796195089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174987403694218329579707141 32810138192665936796195089)
            ·
              refine ⟨24607603644499452597146317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32810138192665936796195089 24607603644499452597146317)
              ·
                refine ⟨9227851366687294723929869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24607603644499452597146317 9227851366687294723929869)
                ·
                  refine ⟨3460444262507735521473701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9227851366687294723929869 3460444262507735521473701)
                  ·
                    refine ⟨648833299220200410276319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460444262507735521473701 648833299220200410276319)
                    ·
                      rfl

theorem cell23_3790795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 4].length) (baseStart_3790795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790795 prefixEnd_3790795 := by exact prefixLift 3790795
  have htrace : WordTrace (prefixWord ++ tailWord_3790795) baseStart_3790795 baseEnd_3790795 := by
    simpa [prefixWord, tailWord_3790795, baseEnd_3790795] using wordTrace_append hprefix tailTrace_3790795
  have hstable : (prefixWord ++ tailWord_3790795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790795).length < 2 ^ (prefixWord ++ tailWord_3790795).sum := by decide
  have hdescent : baseEnd_3790795 < baseStart_3790795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790828 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_3790828 : Nat := 118140960795 + 3790828 * 2 ^ 59
def prefixEnd_3790828 : Nat := 4983230072969 + 3 ^ 40 * 3790828 * 2
def baseEnd_3790828 : Nat := 1946516842522199601716305

theorem tailTrace_3790828 : CollatzResearch.WordTrace tailWord_3790828 prefixEnd_3790828 1946516842522199601716305 := by
  unfold tailWord_3790828
  simp only [CollatzResearch.WordTrace]
  refine ⟨69131427955242526361810569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92175237273656701815747425 69131427955242526361810569)
  ·
    refine ⟨51848570966431894771357927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69131427955242526361810569 51848570966431894771357927)
    ·
      refine ⟨77772856449647842157036891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51848570966431894771357927 77772856449647842157036891)
      ·
        refine ⟨116659284674471763235555337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77772856449647842157036891 116659284674471763235555337)
        ·
          refine ⟨87494463505853822426666503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116659284674471763235555337 87494463505853822426666503)
          ·
            refine ⟨131241695258780733639999755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87494463505853822426666503 131241695258780733639999755)
            ·
              refine ⟨196862542888171100459999633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131241695258780733639999755 196862542888171100459999633)
              ·
                refine ⟨147646907166128325344999725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196862542888171100459999633 147646907166128325344999725)
                ·
                  refine ⟨55367590187298122004374897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147646907166128325344999725 55367590187298122004374897)
                  ·
                    refine ⟨41525692640473591503281173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55367590187298122004374897 41525692640473591503281173)
                    ·
                      refine ⟨1946516842522199601716305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41525692640473591503281173 1946516842522199601716305)
                      ·
                        rfl

theorem cell23_3790828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_3790828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790828 prefixEnd_3790828 := by exact prefixLift 3790828
  have htrace : WordTrace (prefixWord ++ tailWord_3790828) baseStart_3790828 baseEnd_3790828 := by
    simpa [prefixWord, tailWord_3790828, baseEnd_3790828] using wordTrace_append hprefix tailTrace_3790828
  have hstable : (prefixWord ++ tailWord_3790828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790828).length < 2 ^ (prefixWord ++ tailWord_3790828).sum := by decide
  have hdescent : baseEnd_3790828 < baseStart_3790828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790846 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3790846 : Nat := 118140960795 + 3790846 * 2 ^ 59
def prefixEnd_3790846 : Nat := 4983230072969 + 3 ^ 40 * 3790846 * 2
def baseEnd_3790846 : Nat := 648842028391326843763741

theorem tailTrace_3790846 : CollatzResearch.WordTrace tailWord_3790846 prefixEnd_3790846 648842028391326843763741 := by
  unfold tailWord_3790846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17282939053052480224722049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92175674949613227865184261 17282939053052480224722049)
  ·
    refine ⟨12962204289789360168541537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17282939053052480224722049 12962204289789360168541537)
    ·
      refine ⟨9721653217342020126406153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12962204289789360168541537 9721653217342020126406153)
      ·
        refine ⟨7291239913006515094804615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9721653217342020126406153 7291239913006515094804615)
        ·
          refine ⟨10936859869509772642206923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291239913006515094804615 10936859869509772642206923)
          ·
            refine ⟨16405289804264658963310385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936859869509772642206923 16405289804264658963310385)
            ·
              refine ⟨12303967353198494222482789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16405289804264658963310385 12303967353198494222482789)
              ·
                refine ⟨2306993878724717666715523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12303967353198494222482789 2306993878724717666715523)
                ·
                  refine ⟨3460490818087076500073285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306993878724717666715523 3460490818087076500073285)
                  ·
                    refine ⟨648842028391326843763741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460490818087076500073285 648842028391326843763741)
                    ·
                      rfl

theorem cell23_3790846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3790846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790846 prefixEnd_3790846 := by exact prefixLift 3790846
  have htrace : WordTrace (prefixWord ++ tailWord_3790846) baseStart_3790846 baseEnd_3790846 := by
    simpa [prefixWord, tailWord_3790846, baseEnd_3790846] using wordTrace_append hprefix tailTrace_3790846
  have hstable : (prefixWord ++ tailWord_3790846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790846).length < 2 ^ (prefixWord ++ tailWord_3790846).sum := by decide
  have hdescent : baseEnd_3790846 < baseStart_3790846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790848 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_3790848 : Nat := 118140960795 + 3790848 * 2 ^ 59
def prefixEnd_3790848 : Nat := 4983230072969 + 3 ^ 40 * 3790848 * 2
def baseEnd_3790848 : Nat := 1946527112135289523466213

theorem tailTrace_3790848 : CollatzResearch.WordTrace tailWord_3790848 prefixEnd_3790848 1946527112135289523466213 := by
  unfold tailWord_3790848
  simp only [CollatzResearch.WordTrace]
  refine ⟨69131792685206298069674599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92175723580275064092899465 69131792685206298069674599)
  ·
    refine ⟨103697689027809447104511899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69131792685206298069674599 103697689027809447104511899)
    ·
      refine ⟨155546533541714170656767849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103697689027809447104511899 155546533541714170656767849)
      ·
        refine ⟨116659900156285627992575887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155546533541714170656767849 116659900156285627992575887)
        ·
          refine ⟨174989850234428441988863831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116659900156285627992575887 174989850234428441988863831)
          ·
            refine ⟨262484775351642662983295747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174989850234428441988863831 262484775351642662983295747)
            ·
              refine ⟨393727163027463994474943621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262484775351642662983295747 393727163027463994474943621)
              ·
                refine ⟨73823843067649498964051929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393727163027463994474943621 73823843067649498964051929)
                ·
                  refine ⟨55367882300737124223038947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73823843067649498964051929 55367882300737124223038947)
                  ·
                    refine ⟨83051823451105686334558421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55367882300737124223038947 83051823451105686334558421)
                    ·
                      refine ⟨1946527112135289523466213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83051823451105686334558421 1946527112135289523466213)
                      ·
                        rfl

theorem cell23_3790848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_3790848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790848 prefixEnd_3790848 := by exact prefixLift 3790848
  have htrace : WordTrace (prefixWord ++ tailWord_3790848) baseStart_3790848 baseEnd_3790848 := by
    simpa [prefixWord, tailWord_3790848, baseEnd_3790848] using wordTrace_append hprefix tailTrace_3790848
  have hstable : (prefixWord ++ tailWord_3790848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790848).length < 2 ^ (prefixWord ++ tailWord_3790848).sum := by decide
  have hdescent : baseEnd_3790848 < baseStart_3790848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790862 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_3790862 : Nat := 118140960795 + 3790862 * 2 ^ 59
def prefixEnd_3790862 : Nat := 4983230072969 + 3 ^ 40 * 3790862 * 2
def baseEnd_3790862 : Nat := 1946534300864452468691149

theorem tailTrace_3790862 : CollatzResearch.WordTrace tailWord_3790862 prefixEnd_3790862 1946534300864452468691149 := by
  unfold tailWord_3790862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17283011999045234566294855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92176063994907917686905893 17283011999045234566294855)
  ·
    refine ⟨25924517998567851849442283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17283011999045234566294855 25924517998567851849442283)
    ·
      refine ⟨38886776997851777774163425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25924517998567851849442283 38886776997851777774163425)
      ·
        refine ⟨29165082748388833330622569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38886776997851777774163425 29165082748388833330622569)
        ·
          refine ⟨21873812061291624997966927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29165082748388833330622569 21873812061291624997966927)
          ·
            refine ⟨32810718091937437496950391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21873812061291624997966927 32810718091937437496950391)
            ·
              refine ⟨49216077137906156245425587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32810718091937437496950391 49216077137906156245425587)
              ·
                refine ⟨73824115706859234368138381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49216077137906156245425587 73824115706859234368138381)
                ·
                  refine ⟨27684043390072212888051893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73824115706859234368138381 27684043390072212888051893)
                  ·
                    refine ⟨2595379067819269958254865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27684043390072212888051893 2595379067819269958254865)
                    ·
                      refine ⟨1946534300864452468691149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595379067819269958254865 1946534300864452468691149)
                      ·
                        rfl

theorem cell23_3790862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_3790862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790862 prefixEnd_3790862 := by exact prefixLift 3790862
  have htrace : WordTrace (prefixWord ++ tailWord_3790862) baseStart_3790862 baseEnd_3790862 := by
    simpa [prefixWord, tailWord_3790862, baseEnd_3790862] using wordTrace_append hprefix tailTrace_3790862
  have hstable : (prefixWord ++ tailWord_3790862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790862).length < 2 ^ (prefixWord ++ tailWord_3790862).sum := by decide
  have hdescent : baseEnd_3790862 < baseStart_3790862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790872 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 1, 5]
def baseStart_3790872 : Nat := 118140960795 + 3790872 * 2 ^ 59
def prefixEnd_3790872 : Nat := 4983230072969 + 3 ^ 40 * 3790872 * 2
def baseEnd_3790872 : Nat := 648846478556999143188701

theorem tailTrace_3790872 : CollatzResearch.WordTrace tailWord_3790872 prefixEnd_3790872 648846478556999143188701 := by
  unfold tailWord_3790872
  simp only [CollatzResearch.WordTrace]
  refine ⟨69132230361162824119111435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92176307148217098825481913 69132230361162824119111435)
  ·
    refine ⟨103698345541744236178667153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69132230361162824119111435 103698345541744236178667153)
    ·
      refine ⟨77773759156308177134000365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103698345541744236178667153 77773759156308177134000365)
      ·
        refine ⟨29165159683615566425250137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77773759156308177134000365 29165159683615566425250137)
        ·
          refine ⟨21873869762711674818937603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29165159683615566425250137 21873869762711674818937603)
          ·
            refine ⟨32810804644067512228406405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21873869762711674818937603 32810804644067512228406405)
            ·
              refine ⟨6152025870762658542826201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32810804644067512228406405 6152025870762658542826201)
              ·
                refine ⟨4614019403071993907119651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6152025870762658542826201 4614019403071993907119651)
                ·
                  refine ⟨6921029104607990860679477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614019403071993907119651 6921029104607990860679477)
                  ·
                    refine ⟨648846478556999143188701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6921029104607990860679477 648846478556999143188701)
                    ·
                      rfl

theorem cell23_3790872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_3790872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790872 prefixEnd_3790872 := by exact prefixLift 3790872
  have htrace : WordTrace (prefixWord ++ tailWord_3790872) baseStart_3790872 baseEnd_3790872 := by
    simpa [prefixWord, tailWord_3790872, baseEnd_3790872] using wordTrace_append hprefix tailTrace_3790872
  have hstable : (prefixWord ++ tailWord_3790872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790872).length < 2 ^ (prefixWord ++ tailWord_3790872).sum := by decide
  have hdescent : baseEnd_3790872 < baseStart_3790872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790946 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3790946 : Nat := 118140960795 + 3790946 * 2 ^ 59
def prefixEnd_3790946 : Nat := 4983230072969 + 3 ^ 40 * 3790946 * 2
def baseEnd_3790946 : Nat := 1946577433239430140040763

theorem tailTrace_3790946 : CollatzResearch.WordTrace tailWord_3790946 prefixEnd_3790946 1946577433239430140040763 := by
  unfold tailWord_3790946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34566789931014389719104173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92178106482705039250944461 34566789931014389719104173)
  ·
    refine ⟨12962546224130396144664065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34566789931014389719104173 12962546224130396144664065)
    ·
      refine ⟨9721909668097797108498049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12962546224130396144664065 9721909668097797108498049)
      ·
        refine ⟨7291432251073347831373537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9721909668097797108498049 7291432251073347831373537)
        ·
          refine ⟨5468574188305010873530153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7291432251073347831373537 5468574188305010873530153)
          ·
            refine ⟨4101430641228758155147615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468574188305010873530153 4101430641228758155147615)
            ·
              refine ⟨6152145961843137232721423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101430641228758155147615 6152145961843137232721423)
              ·
                refine ⟨9228218942764705849082135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152145961843137232721423 9228218942764705849082135)
                ·
                  refine ⟨13842328414147058773623203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9228218942764705849082135 13842328414147058773623203)
                  ·
                    refine ⟨20763492621220588160434805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13842328414147058773623203 20763492621220588160434805)
                    ·
                      refine ⟨1946577433239430140040763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20763492621220588160434805 1946577433239430140040763)
                      ·
                        rfl

theorem cell23_3790946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3790946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790946 prefixEnd_3790946 := by exact prefixLift 3790946
  have htrace : WordTrace (prefixWord ++ tailWord_3790946) baseStart_3790946 baseEnd_3790946 := by
    simpa [prefixWord, tailWord_3790946, baseEnd_3790946] using wordTrace_append hprefix tailTrace_3790946
  have hstable : (prefixWord ++ tailWord_3790946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790946).length < 2 ^ (prefixWord ++ tailWord_3790946).sum := by decide
  have hdescent : baseEnd_3790946 < baseStart_3790946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790959 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 3]
def baseStart_3790959 : Nat := 118140960795 + 3790959 * 2 ^ 59
def prefixEnd_3790959 : Nat := 4983230072969 + 3 ^ 40 * 3790959 * 2
def baseEnd_3790959 : Nat := 1946584108487938589178203

theorem tailTrace_3790959 : CollatzResearch.WordTrace tailWord_3790959 prefixEnd_3790959 1946584108487938589178203 := by
  unfold tailWord_3790959
  simp only [CollatzResearch.WordTrace]
  refine ⟨138267633873010462096639931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92178422582006974731093287 138267633873010462096639931)
  ·
    refine ⟨207401450809515693144959897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138267633873010462096639931 207401450809515693144959897)
    ·
      refine ⟨155551088107136769858719923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207401450809515693144959897 155551088107136769858719923)
      ·
        refine ⟨233326632160705154788079885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155551088107136769858719923 233326632160705154788079885)
        ·
          refine ⟨87497487060264433045529957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233326632160705154788079885 87497487060264433045529957)
          ·
            refine ⟨16405778823799581196036867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87497487060264433045529957 16405778823799581196036867)
            ·
              refine ⟨24608668235699371794055301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16405778823799581196036867 24608668235699371794055301)
              ·
                refine ⟨4614125294193632211385369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24608668235699371794055301 4614125294193632211385369)
                ·
                  refine ⟨3460593970645224158539027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614125294193632211385369 3460593970645224158539027)
                  ·
                    refine ⟨5190890955967836237808541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3460593970645224158539027 5190890955967836237808541)
                    ·
                      refine ⟨1946584108487938589178203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5190890955967836237808541 1946584108487938589178203)
                      ·
                        rfl

theorem cell23_3790959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_3790959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790959 prefixEnd_3790959 := by exact prefixLift 3790959
  have htrace : WordTrace (prefixWord ++ tailWord_3790959) baseStart_3790959 baseEnd_3790959 := by
    simpa [prefixWord, tailWord_3790959, baseEnd_3790959] using wordTrace_append hprefix tailTrace_3790959
  have hstable : (prefixWord ++ tailWord_3790959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790959).length < 2 ^ (prefixWord ++ tailWord_3790959).sum := by decide
  have hdescent : baseEnd_3790959 < baseStart_3790959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790960 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 1, 2, 2]
def baseStart_3790960 : Nat := 118140960795 + 3790960 * 2 ^ 59
def prefixEnd_3790960 : Nat := 4983230072969 + 3 ^ 40 * 3790960 * 2
def baseEnd_3790960 : Nat := 1946584621968593085265699

theorem tailTrace_3790960 : CollatzResearch.WordTrace tailWord_3790960 prefixEnd_3790960 1946584621968593085265699 := by
  unfold tailWord_3790960
  simp only [CollatzResearch.WordTrace]
  refine ⟨69133835173003419633713167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92178446897337892844950889 69133835173003419633713167)
  ·
    refine ⟨103700752759505129450569751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69133835173003419633713167 103700752759505129450569751)
    ·
      refine ⟨155551129139257694175854627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103700752759505129450569751 155551129139257694175854627)
      ·
        refine ⟨233326693708886541263781941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155551129139257694175854627 233326693708886541263781941)
        ·
          refine ⟨21874377535208113243479557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233326693708886541263781941 21874377535208113243479557)
          ·
            refine ⟨4101445787851521233152417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21874377535208113243479557 4101445787851521233152417)
            ·
              refine ⟨3076084340888640924864313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101445787851521233152417 3076084340888640924864313)
              ·
                refine ⟨2307063255666480693648235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076084340888640924864313 2307063255666480693648235)
                ·
                  refine ⟨3460594883499721040472353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307063255666480693648235 3460594883499721040472353)
                  ·
                    refine ⟨2595446162624790780354265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460594883499721040472353 2595446162624790780354265)
                    ·
                      refine ⟨1946584621968593085265699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595446162624790780354265 1946584621968593085265699)
                      ·
                        rfl

theorem cell23_3790960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 2, 2].length) (baseStart_3790960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790960 prefixEnd_3790960 := by exact prefixLift 3790960
  have htrace : WordTrace (prefixWord ++ tailWord_3790960) baseStart_3790960 baseEnd_3790960 := by
    simpa [prefixWord, tailWord_3790960, baseEnd_3790960] using wordTrace_append hprefix tailTrace_3790960
  have hstable : (prefixWord ++ tailWord_3790960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790960).length < 2 ^ (prefixWord ++ tailWord_3790960).sum := by decide
  have hdescent : baseEnd_3790960 < baseStart_3790960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790969 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 3, 3, 2]
def baseStart_3790969 : Nat := 118140960795 + 3790969 * 2 ^ 59
def prefixEnd_3790969 : Nat := 4983230072969 + 3 ^ 40 * 3790969 * 2
def baseEnd_3790969 : Nat := 1946589243294483550053157

theorem tailTrace_3790969 : CollatzResearch.WordTrace tailWord_3790969 prefixEnd_3790969 1946589243294483550053157 := by
  unfold tailWord_3790969
  simp only [CollatzResearch.WordTrace]
  refine ⟨138267998602974233804503961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92178665735316155869669307 138267998602974233804503961)
  ·
    refine ⟨103700998952230675353377971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138267998602974233804503961 103700998952230675353377971)
    ·
      refine ⟨155551498428346013030066957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103700998952230675353377971 155551498428346013030066957)
      ·
        refine ⟨58331811910629754886275109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155551498428346013030066957 58331811910629754886275109)
        ·
          refine ⟨10937214733243079041176583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58331811910629754886275109 10937214733243079041176583)
          ·
            refine ⟨16405822099864618561764875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937214733243079041176583 16405822099864618561764875)
            ·
              refine ⟨24608733149796927842647313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16405822099864618561764875 24608733149796927842647313)
              ·
                refine ⟨18456549862347695881985485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24608733149796927842647313 18456549862347695881985485)
                ·
                  refine ⟨6921206198380385955744557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18456549862347695881985485 6921206198380385955744557)
                  ·
                    refine ⟨2595452324392644733404209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6921206198380385955744557 2595452324392644733404209)
                    ·
                      refine ⟨1946589243294483550053157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595452324392644733404209 1946589243294483550053157)
                      ·
                        rfl

theorem cell23_3790969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_3790969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790969 prefixEnd_3790969 := by exact prefixLift 3790969
  have htrace : WordTrace (prefixWord ++ tailWord_3790969) baseStart_3790969 baseEnd_3790969 := by
    simpa [prefixWord, tailWord_3790969, baseEnd_3790969] using wordTrace_append hprefix tailTrace_3790969
  have hstable : (prefixWord ++ tailWord_3790969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790969).length < 2 ^ (prefixWord ++ tailWord_3790969).sum := by decide
  have hdescent : baseEnd_3790969 < baseStart_3790969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790995 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4]
def baseStart_3790995 : Nat := 118140960795 + 3790995 * 2 ^ 59
def prefixEnd_3790995 : Nat := 4983230072969 + 3 ^ 40 * 3790995 * 2
def baseEnd_3790995 : Nat := 1946602593791500448328037

theorem tailTrace_3790995 : CollatzResearch.WordTrace tailWord_3790995 prefixEnd_3790995 1946602593791500448328037 := by
  unfold tailWord_3790995
  simp only [CollatzResearch.WordTrace]
  refine ⟨138268946900880040244950439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92179297933920026829966959 138268946900880040244950439)
  ·
    refine ⟨207403420351320060367425659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138268946900880040244950439 207403420351320060367425659)
    ·
      refine ⟨311105130526980090551138489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207403420351320060367425659 311105130526980090551138489)
      ·
        refine ⟨233328847895235067913353867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311105130526980090551138489 233328847895235067913353867)
        ·
          refine ⟨349993271842852601870030801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233328847895235067913353867 349993271842852601870030801)
          ·
            refine ⟨262494953882139451402523101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349993271842852601870030801 262494953882139451402523101)
            ·
              refine ⟨98435607705802294275946163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262494953882139451402523101 98435607705802294275946163)
              ·
                refine ⟨147653411558703441413919245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98435607705802294275946163 147653411558703441413919245)
                ·
                  refine ⟨55370029334513790530219717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147653411558703441413919245 55370029334513790530219717)
                  ·
                    refine ⟨10381880500221335724416197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55370029334513790530219717 10381880500221335724416197)
                    ·
                      refine ⟨1946602593791500448328037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10381880500221335724416197 1946602593791500448328037)
                      ·
                        rfl

theorem cell23_3790995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_3790995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790995 prefixEnd_3790995 := by exact prefixLift 3790995
  have htrace : WordTrace (prefixWord ++ tailWord_3790995) baseStart_3790995 baseEnd_3790995 := by
    simpa [prefixWord, tailWord_3790995, baseEnd_3790995] using wordTrace_append hprefix tailTrace_3790995
  have hstable : (prefixWord ++ tailWord_3790995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790995).length < 2 ^ (prefixWord ++ tailWord_3790995).sum := by decide
  have hdescent : baseEnd_3790995 < baseStart_3790995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791032 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_3791032 : Nat := 118140960795 + 3791032 * 2 ^ 59
def prefixEnd_3791032 : Nat := 4983230072969 + 3 ^ 40 * 3791032 * 2
def baseEnd_3791032 : Nat := 1946621592575716803565367

theorem tailTrace_3791032 : CollatzResearch.WordTrace tailWord_3791032 prefixEnd_3791032 1946621592575716803565367 := by
  unfold tailWord_3791032
  simp only [CollatzResearch.WordTrace]
  refine ⟨69135148200872997782023675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92180197601163997042698233 69135148200872997782023675)
  ·
    refine ⟨103702722301309496673035513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69135148200872997782023675 103702722301309496673035513)
    ·
      refine ⟨77777041725982122504776635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103702722301309496673035513 77777041725982122504776635)
      ·
        refine ⟨116665562588973183757164953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77777041725982122504776635 116665562588973183757164953)
        ·
          refine ⟨87499171941729887817873715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116665562588973183757164953 87499171941729887817873715)
          ·
            refine ⟨131248757912594831726810573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87499171941729887817873715 131248757912594831726810573)
            ·
              refine ⟨49218284217223061897553965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131248757912594831726810573 49218284217223061897553965)
              ·
                refine ⟨18456856581458648211582737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49218284217223061897553965 18456856581458648211582737)
                ·
                  refine ⟨13842642436093986158687053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18456856581458648211582737 13842642436093986158687053)
                  ·
                    refine ⟨5190990913535244809507645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13842642436093986158687053 5190990913535244809507645)
                    ·
                      refine ⟨1946621592575716803565367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5190990913535244809507645 1946621592575716803565367)
                      ·
                        rfl

theorem cell23_3791032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_3791032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791032 prefixEnd_3791032 := by exact prefixLift 3791032
  have htrace : WordTrace (prefixWord ++ tailWord_3791032) baseStart_3791032 baseEnd_3791032 := by
    simpa [prefixWord, tailWord_3791032, baseEnd_3791032] using wordTrace_append hprefix tailTrace_3791032
  have hstable : (prefixWord ++ tailWord_3791032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791032).length < 2 ^ (prefixWord ++ tailWord_3791032).sum := by decide
  have hdescent : baseEnd_3791032 < baseStart_3791032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791033 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 2, 2, 2]
def baseStart_3791033 : Nat := 118140960795 + 3791033 * 2 ^ 59
def prefixEnd_3791033 : Nat := 4983230072969 + 3 ^ 40 * 3791033 * 2
def baseEnd_3791033 : Nat := 1946622106056371299652863

theorem tailTrace_3791033 : CollatzResearch.WordTrace tailWord_3791033 prefixEnd_3791033 1946622106056371299652863 := by
  unfold tailWord_3791033
  simp only [CollatzResearch.WordTrace]
  refine ⟨138270332874742372734833753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92180221916494915156555835 138270332874742372734833753)
  ·
    refine ⟨103702749656056779551125315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138270332874742372734833753 103702749656056779551125315)
    ·
      refine ⟨155554124484085169326687973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103702749656056779551125315 155554124484085169326687973)
      ·
        refine ⟨29166398340765969248753995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155554124484085169326687973 29166398340765969248753995)
        ·
          refine ⟨43749597511148953873130993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29166398340765969248753995 43749597511148953873130993)
          ·
            refine ⟨32812198133361715404848245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43749597511148953873130993 32812198133361715404848245)
            ·
              refine ⟨3076143575002660819204523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32812198133361715404848245 3076143575002660819204523)
              ·
                refine ⟨4614215362503991228806785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076143575002660819204523 4614215362503991228806785)
                ·
                  refine ⟨3460661521877993421605089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614215362503991228806785 3460661521877993421605089)
                  ·
                    refine ⟨2595496141408495066203817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460661521877993421605089 2595496141408495066203817)
                    ·
                      refine ⟨1946622106056371299652863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595496141408495066203817 1946622106056371299652863)
                      ·
                        rfl

theorem cell23_3791033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_3791033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791033 prefixEnd_3791033 := by exact prefixLift 3791033
  have htrace : WordTrace (prefixWord ++ tailWord_3791033) baseStart_3791033 baseEnd_3791033 := by
    simpa [prefixWord, tailWord_3791033, baseEnd_3791033] using wordTrace_append hprefix tailTrace_3791033
  have hstable : (prefixWord ++ tailWord_3791033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791033).length < 2 ^ (prefixWord ++ tailWord_3791033).sum := by decide
  have hdescent : baseEnd_3791033 < baseStart_3791033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791035 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 3, 7]
def baseStart_3791035 : Nat := 118140960795 + 3791035 * 2 ^ 59
def prefixEnd_3791035 : Nat := 4983230072969 + 3 ^ 40 * 3791035 * 2
def baseEnd_3791035 : Nat := 648874377672560097275951

theorem tailTrace_3791035 : CollatzResearch.WordTrace tailWord_3791035 prefixEnd_3791035 648874377672560097275951 := by
  unfold tailWord_3791035
  simp only [CollatzResearch.WordTrace]
  refine ⟨138270405820735127076406559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92180270547156751384271039 138270405820735127076406559)
  ·
    refine ⟨207405608731102690614609839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138270405820735127076406559 207405608731102690614609839)
    ·
      refine ⟨311108413096654035921914759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207405608731102690614609839 311108413096654035921914759)
      ·
        refine ⟨466662619644981053882872139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311108413096654035921914759 466662619644981053882872139)
        ·
          refine ⟨699993929467471580824308209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466662619644981053882872139 699993929467471580824308209)
          ·
            refine ⟨524995447100603685618231157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699993929467471580824308209 524995447100603685618231157)
            ·
              refine ⟨49218323165681595526709171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 524995447100603685618231157 49218323165681595526709171)
              ·
                refine ⟨73827484748522393290063757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49218323165681595526709171 73827484748522393290063757)
                ·
                  refine ⟨27685306780695897483773909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73827484748522393290063757 27685306780695897483773909)
                  ·
                    refine ⟨648874377672560097275951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27685306780695897483773909 648874377672560097275951)
                    ·
                      rfl

theorem cell23_3791035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_3791035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791035 prefixEnd_3791035 := by exact prefixLift 3791035
  have htrace : WordTrace (prefixWord ++ tailWord_3791035) baseStart_3791035 baseEnd_3791035 := by
    simpa [prefixWord, tailWord_3791035, baseEnd_3791035] using wordTrace_append hprefix tailTrace_3791035
  have hstable : (prefixWord ++ tailWord_3791035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791035).length < 2 ^ (prefixWord ++ tailWord_3791035).sum := by decide
  have hdescent : baseEnd_3791035 < baseStart_3791035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791069 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3791069 : Nat := 118140960795 + 3791069 * 2 ^ 59
def prefixEnd_3791069 : Nat := 4983230072969 + 3 ^ 40 * 3791069 * 2
def baseEnd_3791069 : Nat := 648880197119977719600899

theorem tailTrace_3791069 : CollatzResearch.WordTrace tailWord_3791069 prefixEnd_3791069 648880197119977719600899 := by
  unfold tailWord_3791069
  simp only [CollatzResearch.WordTrace]
  refine ⟨138271645902611950883144261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92181097268407967255429507 138271645902611950883144261)
  ·
    refine ⟨25925933606739740790589549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138271645902611950883144261 25925933606739740790589549)
    ·
      refine ⟨9722225102527402796471081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25925933606739740790589549 9722225102527402796471081)
      ·
        refine ⟨7291668826895552097353311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9722225102527402796471081 7291668826895552097353311)
        ·
          refine ⟨10937503240343328146029967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291668826895552097353311 10937503240343328146029967)
          ·
            refine ⟨16406254860514992219044951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937503240343328146029967 16406254860514992219044951)
            ·
              refine ⟨24609382290772488328567427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16406254860514992219044951 24609382290772488328567427)
              ·
                refine ⟨36914073436158732492851141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24609382290772488328567427 36914073436158732492851141)
                ·
                  refine ⟨6921388769279762342409589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36914073436158732492851141 6921388769279762342409589)
                  ·
                    refine ⟨648880197119977719600899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6921388769279762342409589 648880197119977719600899)
                    ·
                      rfl

theorem cell23_3791069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3791069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791069 prefixEnd_3791069 := by exact prefixLift 3791069
  have htrace : WordTrace (prefixWord ++ tailWord_3791069) baseStart_3791069 baseEnd_3791069 := by
    simpa [prefixWord, tailWord_3791069, baseEnd_3791069] using wordTrace_append hprefix tailTrace_3791069
  have hstable : (prefixWord ++ tailWord_3791069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791069).length < 2 ^ (prefixWord ++ tailWord_3791069).sum := by decide
  have hdescent : baseEnd_3791069 < baseStart_3791069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791079 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3791079 : Nat := 118140960795 + 3791079 * 2 ^ 59
def prefixEnd_3791079 : Nat := 4983230072969 + 3 ^ 40 * 3791079 * 2
def baseEnd_3791079 : Nat := 1946645726166478119677651

theorem tailTrace_3791079 : CollatzResearch.WordTrace tailWord_3791079 prefixEnd_3791079 1946645726166478119677651 := by
  unfold tailWord_3791079
  simp only [CollatzResearch.WordTrace]
  refine ⟨138272010632575722591008291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92181340421717148394005527 138272010632575722591008291)
  ·
    refine ⟨207408015948863583886512437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138272010632575722591008291 207408015948863583886512437)
    ·
      refine ⟨19444501495205960989360541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207408015948863583886512437 19444501495205960989360541)
      ·
        refine ⟨7291688060702235371010203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19444501495205960989360541 7291688060702235371010203)
        ·
          refine ⟨10937532091053353056515305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291688060702235371010203 10937532091053353056515305)
          ·
            refine ⟨8203149068290014792386479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10937532091053353056515305 8203149068290014792386479)
            ·
              refine ⟨12304723602435022188579719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203149068290014792386479 12304723602435022188579719)
              ·
                refine ⟨18457085403652533282869579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12304723602435022188579719 18457085403652533282869579)
                ·
                  refine ⟨27685628105478799924304369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18457085403652533282869579 27685628105478799924304369)
                  ·
                    refine ⟨20764221079109099943228277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27685628105478799924304369 20764221079109099943228277)
                    ·
                      refine ⟨1946645726166478119677651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20764221079109099943228277 1946645726166478119677651)
                      ·
                        rfl

theorem cell23_3791079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3791079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791079 prefixEnd_3791079 := by exact prefixLift 3791079
  have htrace : WordTrace (prefixWord ++ tailWord_3791079) baseStart_3791079 baseEnd_3791079 := by
    simpa [prefixWord, tailWord_3791079, baseEnd_3791079] using wordTrace_append hprefix tailTrace_3791079
  have hstable : (prefixWord ++ tailWord_3791079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791079).length < 2 ^ (prefixWord ++ tailWord_3791079).sum := by decide
  have hdescent : baseEnd_3791079 < baseStart_3791079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791089 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 2, 4, 2]
def baseStart_3791089 : Nat := 118140960795 + 3791089 * 2 ^ 59
def prefixEnd_3791089 : Nat := 4983230072969 + 3 ^ 40 * 3791089 * 2
def baseEnd_3791089 : Nat := 1946650860973023080552605

theorem tailTrace_3791089 : CollatzResearch.WordTrace tailWord_3791089 prefixEnd_3791089 1946650860973023080552605 := by
  unfold tailWord_3791089
  simp only [CollatzResearch.WordTrace]
  refine ⟨138272375362539494298872321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92181583575026329532581547 138272375362539494298872321)
  ·
    refine ⟨103704281521904620724154241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138272375362539494298872321 103704281521904620724154241)
    ·
      refine ⟨77778211141428465543115681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103704281521904620724154241 77778211141428465543115681)
      ·
        refine ⟨58333658356071349157336761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77778211141428465543115681 58333658356071349157336761)
        ·
          refine ⟨43750243767053511868002571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58333658356071349157336761 43750243767053511868002571)
          ·
            refine ⟨65625365650580267802003857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43750243767053511868002571 65625365650580267802003857)
            ·
              refine ⟨49219024237935200851502893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65625365650580267802003857 49219024237935200851502893)
              ·
                refine ⟨18457134089225700319313585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49219024237935200851502893 18457134089225700319313585)
                ·
                  refine ⟨13842850566919275239485189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18457134089225700319313585 13842850566919275239485189)
                  ·
                    refine ⟨2595534481297364107403473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13842850566919275239485189 2595534481297364107403473)
                    ·
                      refine ⟨1946650860973023080552605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595534481297364107403473 1946650860973023080552605)
                      ·
                        rfl

theorem cell23_3791089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_3791089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791089 prefixEnd_3791089 := by exact prefixLift 3791089
  have htrace : WordTrace (prefixWord ++ tailWord_3791089) baseStart_3791089 baseEnd_3791089 := by
    simpa [prefixWord, tailWord_3791089, baseEnd_3791089] using wordTrace_append hprefix tailTrace_3791089
  have hstable : (prefixWord ++ tailWord_3791089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791089).length < 2 ^ (prefixWord ++ tailWord_3791089).sum := by decide
  have hdescent : baseEnd_3791089 < baseStart_3791089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791106 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3791106 : Nat := 118140960795 + 3791106 * 2 ^ 59
def prefixEnd_3791106 : Nat := 4983230072969 + 3 ^ 40 * 3791106 * 2
def baseEnd_3791106 : Nat := 1946659590144149514040027

theorem tailTrace_3791106 : CollatzResearch.WordTrace tailWord_3791106 prefixEnd_3791106 1946659590144149514040027 := by
  unfold tailWord_3791106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34568248850869476550560293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92181996935651937468160781 34568248850869476550560293)
  ·
    refine ⟨6481546659538026853230055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34568248850869476550560293 6481546659538026853230055)
    ·
      refine ⟨9722319989307040279845083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6481546659538026853230055 9722319989307040279845083)
      ·
        refine ⟨14583479983960560419767625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722319989307040279845083 14583479983960560419767625)
        ·
          refine ⟨10937609987970420314825719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14583479983960560419767625 10937609987970420314825719)
          ·
            refine ⟨16406414981955630472238579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937609987970420314825719 16406414981955630472238579)
            ·
              refine ⟨24609622472933445708357869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16406414981955630472238579 24609622472933445708357869)
              ·
                refine ⟨9228608427350042140634201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24609622472933445708357869 9228608427350042140634201)
                ·
                  refine ⟨6921456320512531605475651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9228608427350042140634201 6921456320512531605475651)
                  ·
                    refine ⟨10382184480768797408213477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6921456320512531605475651 10382184480768797408213477)
                    ·
                      refine ⟨1946659590144149514040027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10382184480768797408213477 1946659590144149514040027)
                      ·
                        rfl

theorem cell23_3791106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3791106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791106 prefixEnd_3791106 := by exact prefixLift 3791106
  have htrace : WordTrace (prefixWord ++ tailWord_3791106) baseStart_3791106 baseEnd_3791106 := by
    simpa [prefixWord, tailWord_3791106, baseEnd_3791106] using wordTrace_append hprefix tailTrace_3791106
  have hstable : (prefixWord ++ tailWord_3791106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791106).length < 2 ^ (prefixWord ++ tailWord_3791106).sum := by decide
  have hdescent : baseEnd_3791106 < baseStart_3791106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791116 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_3791116 : Nat := 118140960795 + 3791116 * 2 ^ 59
def prefixEnd_3791116 : Nat := 4983230072969 + 3 ^ 40 * 3791116 * 2
def baseEnd_3791116 : Nat := 648888241650231491638327

theorem tailTrace_3791116 : CollatzResearch.WordTrace tailWord_3791116 prefixEnd_3791116 648888241650231491638327 := by
  unfold tailWord_3791116
  simp only [CollatzResearch.WordTrace]
  refine ⟨69136680066720838955052601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92182240088961118606736801 69136680066720838955052601)
  ·
    refine ⟨51852510050040629216289451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69136680066720838955052601 51852510050040629216289451)
    ·
      refine ⟨77778765075060943824434177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51852510050040629216289451 77778765075060943824434177)
      ·
        refine ⟨58334073806295707868325633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77778765075060943824434177 58334073806295707868325633)
        ·
          refine ⟨43750555354721780901244225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58334073806295707868325633 43750555354721780901244225)
          ·
            refine ⟨32812916516041335675933169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43750555354721780901244225 32812916516041335675933169)
            ·
              refine ⟨24609687387031001756949877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32812916516041335675933169 24609687387031001756949877)
              ·
                refine ⟨2307158192534156414714051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24609687387031001756949877 2307158192534156414714051)
                ·
                  refine ⟨3460737288801234622071077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307158192534156414714051 3460737288801234622071077)
                  ·
                    refine ⟨648888241650231491638327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460737288801234622071077 648888241650231491638327)
                    ·
                      rfl

theorem cell23_3791116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_3791116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791116 prefixEnd_3791116 := by exact prefixLift 3791116
  have htrace : WordTrace (prefixWord ++ tailWord_3791116) baseStart_3791116 baseEnd_3791116 := by
    simpa [prefixWord, tailWord_3791116, baseEnd_3791116] using wordTrace_append hprefix tailTrace_3791116
  have hstable : (prefixWord ++ tailWord_3791116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791116).length < 2 ^ (prefixWord ++ tailWord_3791116).sum := by decide
  have hdescent : baseEnd_3791116 < baseStart_3791116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791132 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3791132 : Nat := 118140960795 + 3791132 * 2 ^ 59
def prefixEnd_3791132 : Nat := 4983230072969 + 3 ^ 40 * 3791132 * 2
def baseEnd_3791132 : Nat := 1946672940641166412314907

theorem tailTrace_3791132 : CollatzResearch.WordTrace tailWord_3791132 prefixEnd_3791132 1946672940641166412314907 := by
  unfold tailWord_3791132
  simp only [CollatzResearch.WordTrace]
  refine ⟨69136971850691856321343825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92182629134255808428458433 69136971850691856321343825)
  ·
    refine ⟨51852728888018892241007869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69136971850691856321343825 51852728888018892241007869)
    ·
      refine ⟨19444773333007084590377951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51852728888018892241007869 19444773333007084590377951)
      ·
        refine ⟨29167159999510626885566927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19444773333007084590377951 29167159999510626885566927)
        ·
          refine ⟨43750739999265940328350391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29167159999510626885566927 43750739999265940328350391)
          ·
            refine ⟨65626109998898910492525587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43750739999265940328350391 65626109998898910492525587)
            ·
              refine ⟨98439164998348365738788381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65626109998898910492525587 98439164998348365738788381)
              ·
                refine ⟨36914686874380637152045643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98439164998348365738788381 36914686874380637152045643)
                ·
                  refine ⟨55372030311570955728068465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36914686874380637152045643 55372030311570955728068465)
                  ·
                    refine ⟨41529022733678216796051349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55372030311570955728068465 41529022733678216796051349)
                    ·
                      refine ⟨1946672940641166412314907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41529022733678216796051349 1946672940641166412314907)
                      ·
                        rfl

theorem cell23_3791132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3791132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791132 prefixEnd_3791132 := by exact prefixLift 3791132
  have htrace : WordTrace (prefixWord ++ tailWord_3791132) baseStart_3791132 baseEnd_3791132 := by
    simpa [prefixWord, tailWord_3791132, baseEnd_3791132] using wordTrace_append hprefix tailTrace_3791132
  have hstable : (prefixWord ++ tailWord_3791132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791132).length < 2 ^ (prefixWord ++ tailWord_3791132).sum := by decide
  have hdescent : baseEnd_3791132 < baseStart_3791132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791176 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 1, 5]
def baseStart_3791176 : Nat := 118140960795 + 3791176 * 2 ^ 59
def prefixEnd_3791176 : Nat := 4983230072969 + 3 ^ 40 * 3791176 * 2
def baseEnd_3791176 : Nat := 648898511263321413388235

theorem tailTrace_3791176 : CollatzResearch.WordTrace tailWord_3791176 prefixEnd_3791176 648898511263321413388235 := by
  unfold tailWord_3791176
  simp only [CollatzResearch.WordTrace]
  refine ⟨69137774256612154078644691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92183699008816205438192921 69137774256612154078644691)
  ·
    refine ⟨103706661384918231117967037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69137774256612154078644691 103706661384918231117967037)
    ·
      refine ⟨38889998019344336669237639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103706661384918231117967037 38889998019344336669237639)
      ·
        refine ⟨58334997029016505003856459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38889998019344336669237639 58334997029016505003856459)
        ·
          refine ⟨87502495543524757505784689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58334997029016505003856459 87502495543524757505784689)
          ·
            refine ⟨65626871657643568129338517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87502495543524757505784689 65626871657643568129338517)
            ·
              refine ⟨3076259608952042256062743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65626871657643568129338517 3076259608952042256062743)
              ·
                refine ⟨4614389413428063384094115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076259608952042256062743 4614389413428063384094115)
                ·
                  refine ⟨6921584120142095076141173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614389413428063384094115 6921584120142095076141173)
                  ·
                    refine ⟨648898511263321413388235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6921584120142095076141173 648898511263321413388235)
                    ·
                      rfl

theorem cell23_3791176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_3791176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791176 prefixEnd_3791176 := by exact prefixLift 3791176
  have htrace : WordTrace (prefixWord ++ tailWord_3791176) baseStart_3791176 baseEnd_3791176 := by
    simpa [prefixWord, tailWord_3791176, baseEnd_3791176] using wordTrace_append hprefix tailTrace_3791176
  have hstable : (prefixWord ++ tailWord_3791176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791176).length < 2 ^ (prefixWord ++ tailWord_3791176).sum := by decide
  have hdescent : baseEnd_3791176 < baseStart_3791176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791199 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_3791199 : Nat := 118140960795 + 3791199 * 2 ^ 59
def prefixEnd_3791199 : Nat := 4983230072969 + 3 ^ 40 * 3791199 * 2
def baseEnd_3791199 : Nat := 1946707343845017650177099

theorem tailTrace_3791199 : CollatzResearch.WordTrace tailWord_3791199 prefixEnd_3791199 1946707343845017650177099 := by
  unfold tailWord_3791199
  simp only [CollatzResearch.WordTrace]
  refine ⟨138276387392140983085376651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92184258261427322056917767 138276387392140983085376651)
  ·
    refine ⟨207414581088211474628064977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138276387392140983085376651 207414581088211474628064977)
    ·
      refine ⟨155560935816158605971048733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207414581088211474628064977 155560935816158605971048733)
      ·
        refine ⟨58335350931059477239143275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155560935816158605971048733 58335350931059477239143275)
        ·
          refine ⟨87503026396589215858714913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58335350931059477239143275 87503026396589215858714913)
          ·
            refine ⟨65627269797441911894036185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87503026396589215858714913 65627269797441911894036185)
            ·
              refine ⟨49220452348081433920527139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65627269797441911894036185 49220452348081433920527139)
              ·
                refine ⟨73830678522122150880790709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49220452348081433920527139 73830678522122150880790709)
                ·
                  refine ⟨6921626111448951645074129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73830678522122150880790709 6921626111448951645074129)
                  ·
                    refine ⟨5191219583586713733805597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6921626111448951645074129 5191219583586713733805597)
                    ·
                      refine ⟨1946707343845017650177099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5191219583586713733805597 1946707343845017650177099)
                      ·
                        rfl

theorem cell23_3791199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_3791199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791199 prefixEnd_3791199 := by exact prefixLift 3791199
  have htrace : WordTrace (prefixWord ++ tailWord_3791199) baseStart_3791199 baseEnd_3791199 := by
    simpa [prefixWord, tailWord_3791199, baseEnd_3791199] using wordTrace_append hprefix tailTrace_3791199
  have hstable : (prefixWord ++ tailWord_3791199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791199).length < 2 ^ (prefixWord ++ tailWord_3791199).sum := by decide
  have hdescent : baseEnd_3791199 < baseStart_3791199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791213 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_3791213 : Nat := 118140960795 + 3791213 * 2 ^ 59
def prefixEnd_3791213 : Nat := 4983230072969 + 3 ^ 40 * 3791213 * 2
def baseEnd_3791213 : Nat := 1946714532574180595402035

theorem tailTrace_3791213 : CollatzResearch.WordTrace tailWord_3791213 prefixEnd_3791213 1946714532574180595402035 := by
  unfold tailWord_3791213
  simp only [CollatzResearch.WordTrace]
  refine ⟨138276898014090263476386293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92184598676060175650924195 138276898014090263476386293)
  ·
    refine ⟨12963459188820962200911215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138276898014090263476386293 12963459188820962200911215)
    ·
      refine ⟨19445188783231443301366823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12963459188820962200911215 19445188783231443301366823)
      ·
        refine ⟨29167783174847164952050235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19445188783231443301366823 29167783174847164952050235)
        ·
          refine ⟨43751674762270747428075353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29167783174847164952050235 43751674762270747428075353)
          ·
            refine ⟨32813756071703060571056515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43751674762270747428075353 32813756071703060571056515)
            ·
              refine ⟨49220634107554590856584773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32813756071703060571056515 49220634107554590856584773)
              ·
                refine ⟨9228868895166485785609645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49220634107554590856584773 9228868895166485785609645)
                ·
                  refine ⟨3460825835687432169603617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9228868895166485785609645 3460825835687432169603617)
                  ·
                    refine ⟨2595619376765574127202713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460825835687432169603617 2595619376765574127202713)
                    ·
                      refine ⟨1946714532574180595402035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595619376765574127202713 1946714532574180595402035)
                      ·
                        rfl

theorem cell23_3791213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_3791213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791213 prefixEnd_3791213 := by exact prefixLift 3791213
  have htrace : WordTrace (prefixWord ++ tailWord_3791213) baseStart_3791213 baseEnd_3791213 := by
    simpa [prefixWord, tailWord_3791213, baseEnd_3791213] using wordTrace_append hprefix tailTrace_3791213
  have hstable : (prefixWord ++ tailWord_3791213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791213).length < 2 ^ (prefixWord ++ tailWord_3791213).sum := by decide
  have hdescent : baseEnd_3791213 < baseStart_3791213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791216 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3]
def baseStart_3791216 : Nat := 118140960795 + 3791216 * 2 ^ 59
def prefixEnd_3791216 : Nat := 4983230072969 + 3 ^ 40 * 3791216 * 2
def baseEnd_3791216 : Nat := 1946716073016144083664521

theorem tailTrace_3791216 : CollatzResearch.WordTrace tailWord_3791216 prefixEnd_3791216 1946716073016144083664521 := by
  unfold tailWord_3791216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69138503716539697494372751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92184671622052929992497001 69138503716539697494372751)
  ·
    refine ⟨103707755574809546241559127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69138503716539697494372751 103707755574809546241559127)
    ·
      refine ⟨155561633362214319362338691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103707755574809546241559127 155561633362214319362338691)
      ·
        refine ⟨233342450043321479043508037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155561633362214319362338691 233342450043321479043508037)
        ·
          refine ⟨43751709383122777320657757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233342450043321479043508037 43751709383122777320657757)
          ·
            refine ⟨16406891018671041495246659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43751709383122777320657757 16406891018671041495246659)
            ·
              refine ⟨24610336528006562242869989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16406891018671041495246659 24610336528006562242869989)
              ·
                refine ⟨4614438099001230420538123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24610336528006562242869989 4614438099001230420538123)
                ·
                  refine ⟨6921657148501845630807185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614438099001230420538123 6921657148501845630807185)
                  ·
                    refine ⟨5191242861376384223105389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6921657148501845630807185 5191242861376384223105389)
                    ·
                      refine ⟨1946716073016144083664521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5191242861376384223105389 1946716073016144083664521)
                      ·
                        rfl

theorem cell23_3791216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_3791216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791216 prefixEnd_3791216 := by exact prefixLift 3791216
  have htrace : WordTrace (prefixWord ++ tailWord_3791216) baseStart_3791216 baseEnd_3791216 := by
    simpa [prefixWord, tailWord_3791216, baseEnd_3791216] using wordTrace_append hprefix tailTrace_3791216
  have hstable : (prefixWord ++ tailWord_3791216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791216).length < 2 ^ (prefixWord ++ tailWord_3791216).sum := by decide
  have hdescent : baseEnd_3791216 < baseStart_3791216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791232 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_3791232 : Nat := 118140960795 + 3791232 * 2 ^ 59
def prefixEnd_3791232 : Nat := 4983230072969 + 3 ^ 40 * 3791232 * 2
def baseEnd_3791232 : Nat := 648908096235538673688149

theorem tailTrace_3791232 : CollatzResearch.WordTrace tailWord_3791232 prefixEnd_3791232 648908096235538673688149 := by
  unfold tailWord_3791232
  simp only [CollatzResearch.WordTrace]
  refine ⟨69138795500510714860663975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92185060667347619814218633 69138795500510714860663975)
  ·
    refine ⟨103708193250766072290995963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69138795500510714860663975 103708193250766072290995963)
    ·
      refine ⟨155562289876149108436493945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103708193250766072290995963 155562289876149108436493945)
      ·
        refine ⟨116671717407111831327370459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155562289876149108436493945 116671717407111831327370459)
        ·
          refine ⟨175007576110667746991055689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116671717407111831327370459 175007576110667746991055689)
          ·
            refine ⟨131255682083000810243291767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175007576110667746991055689 131255682083000810243291767)
            ·
              refine ⟨196883523124501215364937651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131255682083000810243291767 196883523124501215364937651)
              ·
                refine ⟨295325284686751823047406477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196883523124501215364937651 295325284686751823047406477)
                ·
                  refine ⟨110746981757531933642777429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295325284686751823047406477 110746981757531933642777429)
                  ·
                    refine ⟨648908096235538673688149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 110746981757531933642777429 648908096235538673688149)
                    ·
                      rfl

theorem cell23_3791232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_3791232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791232 prefixEnd_3791232 := by exact prefixLift 3791232
  have htrace : WordTrace (prefixWord ++ tailWord_3791232) baseStart_3791232 baseEnd_3791232 := by
    simpa [prefixWord, tailWord_3791232, baseEnd_3791232] using wordTrace_append hprefix tailTrace_3791232
  have hstable : (prefixWord ++ tailWord_3791232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791232).length < 2 ^ (prefixWord ++ tailWord_3791232).sum := by decide
  have hdescent : baseEnd_3791232 < baseStart_3791232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791233 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3791233 : Nat := 118140960795 + 3791233 * 2 ^ 59
def prefixEnd_3791233 : Nat := 4983230072969 + 3 ^ 40 * 3791233 * 2
def baseEnd_3791233 : Nat := 1946724802187270517151943

theorem tailTrace_3791233 : CollatzResearch.WordTrace tailWord_3791233 prefixEnd_3791233 1946724802187270517151943 := by
  unfold tailWord_3791233
  simp only [CollatzResearch.WordTrace]
  refine ⟨138277627474017806892114353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92185084982678537928076235 138277627474017806892114353)
  ·
    refine ⟨103708220605513355169085765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138277627474017806892114353 103708220605513355169085765)
    ·
      refine ⟨19445291363533754094203581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103708220605513355169085765 19445291363533754094203581)
      ·
        refine ⟨7291984261325157785326343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19445291363533754094203581 7291984261325157785326343)
        ·
          refine ⟨10937976391987736677989515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291984261325157785326343 10937976391987736677989515)
          ·
            refine ⟨16406964587981605016984273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937976391987736677989515 16406964587981605016984273)
            ·
              refine ⟨12305223440986203762738205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16406964587981605016984273 12305223440986203762738205)
              ·
                refine ⟨4614458790369826411026827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12305223440986203762738205 4614458790369826411026827)
                ·
                  refine ⟨6921688185554739616540241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614458790369826411026827 6921688185554739616540241)
                  ·
                    refine ⟨5191266139166054712405181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6921688185554739616540241 5191266139166054712405181)
                    ·
                      refine ⟨1946724802187270517151943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5191266139166054712405181 1946724802187270517151943)
                      ·
                        rfl

theorem cell23_3791233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3791233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791233 prefixEnd_3791233 := by exact prefixLift 3791233
  have htrace : WordTrace (prefixWord ++ tailWord_3791233) baseStart_3791233 baseEnd_3791233 := by
    simpa [prefixWord, tailWord_3791233, baseEnd_3791233] using wordTrace_append hprefix tailTrace_3791233
  have hstable : (prefixWord ++ tailWord_3791233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791233).length < 2 ^ (prefixWord ++ tailWord_3791233).sum := by decide
  have hdescent : baseEnd_3791233 < baseStart_3791233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791263 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3791263 : Nat := 118140960795 + 3791263 * 2 ^ 59
def prefixEnd_3791263 : Nat := 4983230072969 + 3 ^ 40 * 3791263 * 2
def baseEnd_3791263 : Nat := 1946740206606905399776805

theorem tailTrace_3791263 : CollatzResearch.WordTrace tailWord_3791263 prefixEnd_3791263 1946740206606905399776805 := by
  unfold tailWord_3791263
  simp only [CollatzResearch.WordTrace]
  refine ⟨138278721663909122015706443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92185814442606081343804295 138278721663909122015706443)
  ·
    refine ⟨207418082495863683023559665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138278721663909122015706443 207418082495863683023559665)
    ·
      refine ⟨155563561871897762267669749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207418082495863683023559665 155563561871897762267669749)
      ·
        refine ⟨14584083925490415212594039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155563561871897762267669749 14584083925490415212594039)
        ·
          refine ⟨21876125888235622818891059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14584083925490415212594039 21876125888235622818891059)
          ·
            refine ⟨32814188832353434228336589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21876125888235622818891059 32814188832353434228336589)
            ·
              refine ⟨12305320812132537835626221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32814188832353434228336589 12305320812132537835626221)
              ·
                refine ⟨4614495304549701688359833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12305320812132537835626221 4614495304549701688359833)
                ·
                  refine ⟨3460871478412276266269875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614495304549701688359833 3460871478412276266269875)
                  ·
                    refine ⟨5191307217618414399404813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3460871478412276266269875 5191307217618414399404813)
                    ·
                      refine ⟨1946740206606905399776805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5191307217618414399404813 1946740206606905399776805)
                      ·
                        rfl

theorem cell23_3791263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3791263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791263 prefixEnd_3791263 := by exact prefixLift 3791263
  have htrace : WordTrace (prefixWord ++ tailWord_3791263) baseStart_3791263 baseEnd_3791263 := by
    simpa [prefixWord, tailWord_3791263, baseEnd_3791263] using wordTrace_append hprefix tailTrace_3791263
  have hstable : (prefixWord ++ tailWord_3791263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791263).length < 2 ^ (prefixWord ++ tailWord_3791263).sum := by decide
  have hdescent : baseEnd_3791263 < baseStart_3791263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791284 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3791284 : Nat := 118140960795 + 3791284 * 2 ^ 59
def prefixEnd_3791284 : Nat := 4983230072969 + 3 ^ 40 * 3791284 * 2
def baseEnd_3791284 : Nat := 1946750989700649817614209

theorem tailTrace_3791284 : CollatzResearch.WordTrace tailWord_3791284 prefixEnd_3791284 1946750989700649817614209 := by
  unfold tailWord_3791284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69139743798416521301110453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92186325064555361734813937 69139743798416521301110453)
  ·
    refine ⟨6481850981101548871979105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69139743798416521301110453 6481850981101548871979105)
    ·
      refine ⟨4861388235826161653984329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6481850981101548871979105 4861388235826161653984329)
      ·
        refine ⟨3646041176869621240488247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4861388235826161653984329 3646041176869621240488247)
        ·
          refine ⟨5469061765304431860732371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646041176869621240488247 5469061765304431860732371)
          ·
            refine ⟨8203592647956647791098557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469061765304431860732371 8203592647956647791098557)
            ·
              refine ⟨3076347242983742921661959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8203592647956647791098557 3076347242983742921661959)
              ·
                refine ⟨4614520864475614382492939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076347242983742921661959 4614520864475614382492939)
                ·
                  refine ⟨6921781296713421573739409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614520864475614382492939 6921781296713421573739409)
                  ·
                    refine ⟨5191335972535066180304557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6921781296713421573739409 5191335972535066180304557)
                    ·
                      refine ⟨1946750989700649817614209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5191335972535066180304557 1946750989700649817614209)
                      ·
                        rfl

theorem cell23_3791284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3791284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791284 prefixEnd_3791284 := by exact prefixLift 3791284
  have htrace : WordTrace (prefixWord ++ tailWord_3791284) baseStart_3791284 baseEnd_3791284 := by
    simpa [prefixWord, tailWord_3791284, baseEnd_3791284] using wordTrace_append hprefix tailTrace_3791284
  have hstable : (prefixWord ++ tailWord_3791284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791284).length < 2 ^ (prefixWord ++ tailWord_3791284).sum := by decide
  have hdescent : baseEnd_3791284 < baseStart_3791284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791299 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4]
def baseStart_3791299 : Nat := 118140960795 + 3791299 * 2 ^ 59
def prefixEnd_3791299 : Nat := 4983230072969 + 3 ^ 40 * 3791299 * 2
def baseEnd_3791299 : Nat := 1946758691910467258926639

theorem tailTrace_3791299 : CollatzResearch.WordTrace tailWord_3791299 prefixEnd_3791299 1946758691910467258926639 := by
  unfold tailWord_3791299
  simp only [CollatzResearch.WordTrace]
  refine ⟨138280034691778700164016951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92186689794519133442677967 138280034691778700164016951)
  ·
    refine ⟨207420052037668050246025427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138280034691778700164016951 207420052037668050246025427)
    ·
      refine ⟨311130078056502075369038141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207420052037668050246025427 311130078056502075369038141)
      ·
        refine ⟨116673779271188278263389303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311130078056502075369038141 116673779271188278263389303)
        ·
          refine ⟨175010668906782417395083955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116673779271188278263389303 175010668906782417395083955)
          ·
            refine ⟨262516003360173626092625933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175010668906782417395083955 262516003360173626092625933)
            ·
              refine ⟨98443501260065109784734725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262516003360173626092625933 98443501260065109784734725)
              ·
                refine ⟨18458156486262208084637761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98443501260065109784734725 18458156486262208084637761)
                ·
                  refine ⟨13843617364696656063478321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18458156486262208084637761 13843617364696656063478321)
                  ·
                    refine ⟨10382713023522492047608741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13843617364696656063478321 10382713023522492047608741)
                    ·
                      refine ⟨1946758691910467258926639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10382713023522492047608741 1946758691910467258926639)
                      ·
                        rfl

theorem cell23_3791299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_3791299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791299 prefixEnd_3791299 := by exact prefixLift 3791299
  have htrace : WordTrace (prefixWord ++ tailWord_3791299) baseStart_3791299 baseEnd_3791299 := by
    simpa [prefixWord, tailWord_3791299, baseEnd_3791299] using wordTrace_append hprefix tailTrace_3791299
  have hstable : (prefixWord ++ tailWord_3791299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791299).length < 2 ^ (prefixWord ++ tailWord_3791299).sum := by decide
  have hdescent : baseEnd_3791299 < baseStart_3791299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791316 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3791316 : Nat := 118140960795 + 3791316 * 2 ^ 59
def prefixEnd_3791316 : Nat := 4983230072969 + 3 ^ 40 * 3791316 * 2
def baseEnd_3791316 : Nat := 1946767421081593692414061

theorem tailTrace_3791316 : CollatzResearch.WordTrace tailWord_3791316 prefixEnd_3791316 1946767421081593692414061 := by
  unfold tailWord_3791316
  simp only [CollatzResearch.WordTrace]
  refine ⟨69140327366358556033692901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92187103155144741378257201 69140327366358556033692901)
  ·
    refine ⟨12963811381192229256317419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69140327366358556033692901 12963811381192229256317419)
    ·
      refine ⟨19445717071788343884476129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12963811381192229256317419 19445717071788343884476129)
      ·
        refine ⟨14584287803841257913357097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19445717071788343884476129 14584287803841257913357097)
        ·
          refine ⟨10938215852880943435017823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14584287803841257913357097 10938215852880943435017823)
          ·
            refine ⟨16407323779321415152526735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938215852880943435017823 16407323779321415152526735)
            ·
              refine ⟨24610985668982122728790103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16407323779321415152526735 24610985668982122728790103)
              ·
                refine ⟨36916478503473184093185155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24610985668982122728790103 36916478503473184093185155)
                ·
                  refine ⟨55374717755209776139777733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36916478503473184093185155 55374717755209776139777733)
                  ·
                    refine ⟨10382759579101833026208325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55374717755209776139777733 10382759579101833026208325)
                    ·
                      refine ⟨1946767421081593692414061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10382759579101833026208325 1946767421081593692414061)
                      ·
                        rfl

theorem cell23_3791316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3791316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791316 prefixEnd_3791316 := by exact prefixLift 3791316
  have htrace : WordTrace (prefixWord ++ tailWord_3791316) baseStart_3791316 baseEnd_3791316 := by
    simpa [prefixWord, tailWord_3791316, baseEnd_3791316] using wordTrace_append hprefix tailTrace_3791316
  have hstable : (prefixWord ++ tailWord_3791316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791316).length < 2 ^ (prefixWord ++ tailWord_3791316).sum := by decide
  have hdescent : baseEnd_3791316 < baseStart_3791316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791339 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 1, 7]
def baseStart_3791339 : Nat := 118140960795 + 3791339 * 2 ^ 59
def prefixEnd_3791339 : Nat := 4983230072969 + 3 ^ 40 * 3791339 * 2
def baseEnd_3791339 : Nat := 648926410378882367475485

theorem tailTrace_3791339 : CollatzResearch.WordTrace tailWord_3791339 prefixEnd_3791339 648926410378882367475485 := by
  unfold tailWord_3791339
  simp only [CollatzResearch.WordTrace]
  refine ⟨138281493611633786995473071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92187662407755857996982047 138281493611633786995473071)
  ·
    refine ⟨207422240417450680493209607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138281493611633786995473071 207422240417450680493209607)
    ·
      refine ⟨311133360626176020739814411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207422240417450680493209607 311133360626176020739814411)
      ·
        refine ⟨466700040939264031109721617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311133360626176020739814411 466700040939264031109721617)
        ·
          refine ⟨350025030704448023332291213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466700040939264031109721617 350025030704448023332291213)
          ·
            refine ⟨131259386514168008749609205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350025030704448023332291213 131259386514168008749609205)
            ·
              refine ⟨12305567485703250820275863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131259386514168008749609205 12305567485703250820275863)
              ·
                refine ⟨18458351228554876230413795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12305567485703250820275863 18458351228554876230413795)
                ·
                  refine ⟨27687526842832314345620693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18458351228554876230413795 27687526842832314345620693)
                  ·
                    refine ⟨648926410378882367475485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27687526842832314345620693 648926410378882367475485)
                    ·
                      rfl

theorem cell23_3791339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_3791339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791339 prefixEnd_3791339 := by exact prefixLift 3791339
  have htrace : WordTrace (prefixWord ++ tailWord_3791339) baseStart_3791339 baseEnd_3791339 := by
    simpa [prefixWord, tailWord_3791339, baseEnd_3791339] using wordTrace_append hprefix tailTrace_3791339
  have hstable : (prefixWord ++ tailWord_3791339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791339).length < 2 ^ (prefixWord ++ tailWord_3791339).sum := by decide
  have hdescent : baseEnd_3791339 < baseStart_3791339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791376 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 6, 2]
def baseStart_3791376 : Nat := 118140960795 + 3791376 * 2 ^ 59
def prefixEnd_3791376 : Nat := 4983230072969 + 3 ^ 40 * 3791376 * 2
def baseEnd_3791376 : Nat := 1946798229920863457663785

theorem tailTrace_3791376 : CollatzResearch.WordTrace tailWord_3791376 prefixEnd_3791376 1946798229920863457663785 := by
  unfold tailWord_3791376
  simp only [CollatzResearch.WordTrace]
  refine ⟨69141421556249871157284991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92188562074999828209713321 69141421556249871157284991)
  ·
    refine ⟨103712132334374806735927487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69141421556249871157284991 103712132334374806735927487)
    ·
      refine ⟨155568198501562210103891231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103712132334374806735927487 155568198501562210103891231)
      ·
        refine ⟨233352297752343315155836847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155568198501562210103891231 233352297752343315155836847)
        ·
          refine ⟨350028446628514972733755271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233352297752343315155836847 350028446628514972733755271)
          ·
            refine ⟨525042669942772459100632907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350028446628514972733755271 525042669942772459100632907)
            ·
              refine ⟨787564004914158688650949361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525042669942772459100632907 787564004914158688650949361)
              ·
                refine ⟨590673003685619016488212021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787564004914158688650949361 590673003685619016488212021)
                ·
                  refine ⟨55375594095526782795769877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 590673003685619016488212021 55375594095526782795769877)
                  ·
                    refine ⟨2595730973227817943551713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55375594095526782795769877 2595730973227817943551713)
                    ·
                      refine ⟨1946798229920863457663785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595730973227817943551713 1946798229920863457663785)
                      ·
                        rfl

theorem cell23_3791376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 6, 2].length) (baseStart_3791376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791376 prefixEnd_3791376 := by exact prefixLift 3791376
  have htrace : WordTrace (prefixWord ++ tailWord_3791376) baseStart_3791376 baseEnd_3791376 := by
    simpa [prefixWord, tailWord_3791376, baseEnd_3791376] using wordTrace_append hprefix tailTrace_3791376
  have hstable : (prefixWord ++ tailWord_3791376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791376).length < 2 ^ (prefixWord ++ tailWord_3791376).sum := by decide
  have hdescent : baseEnd_3791376 < baseStart_3791376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791413 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_3791413 : Nat := 118140960795 + 3791413 * 2 ^ 59
def prefixEnd_3791413 : Nat := 4983230072969 + 3 ^ 40 * 3791413 * 2
def baseEnd_3791413 : Nat := 1946817228705079812901115

theorem tailTrace_3791413 : CollatzResearch.WordTrace tailWord_3791413 prefixEnd_3791413 1946817228705079812901115 := by
  unfold tailWord_3791413
  simp only [CollatzResearch.WordTrace]
  refine ⟨138284192613365697633666893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92189461742243798422444595 138284192613365697633666893)
  ·
    refine ⟨51856572230012136612625085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138284192613365697633666893 51856572230012136612625085)
    ·
      refine ⟨19446214586254551229734407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51856572230012136612625085 19446214586254551229734407)
      ·
        refine ⟨29169321879381826844601611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19446214586254551229734407 29169321879381826844601611)
        ·
          refine ⟨43753982819072740266902417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29169321879381826844601611 43753982819072740266902417)
          ·
            refine ⟨32815487114304555200176813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43753982819072740266902417 32815487114304555200176813)
            ·
              refine ⟨12305807667864208200066305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32815487114304555200176813 12305807667864208200066305)
              ·
                refine ⟨9229355750898156150049729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12305807667864208200066305 9229355750898156150049729)
                ·
                  refine ⟨6922016813173617112537297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9229355750898156150049729 6922016813173617112537297)
                  ·
                    refine ⟨5191512609880212834402973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6922016813173617112537297 5191512609880212834402973)
                    ·
                      refine ⟨1946817228705079812901115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5191512609880212834402973 1946817228705079812901115)
                      ·
                        rfl

theorem cell23_3791413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_3791413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791413 prefixEnd_3791413 := by exact prefixLift 3791413
  have htrace : WordTrace (prefixWord ++ tailWord_3791413) baseStart_3791413 baseEnd_3791413 := by
    simpa [prefixWord, tailWord_3791413, baseEnd_3791413] using wordTrace_append hprefix tailTrace_3791413
  have hstable : (prefixWord ++ tailWord_3791413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791413).length < 2 ^ (prefixWord ++ tailWord_3791413).sum := by decide
  have hdescent : baseEnd_3791413 < baseStart_3791413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791416 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 6]
def baseStart_3791416 : Nat := 118140960795 + 3791416 * 2 ^ 59
def prefixEnd_3791416 : Nat := 4983230072969 + 3 ^ 40 * 3791416 * 2
def baseEnd_3791416 : Nat := 216313196571893700129289

theorem tailTrace_3791416 : CollatzResearch.WordTrace tailWord_3791416 prefixEnd_3791416 216313196571893700129289 := by
  unfold tailWord_3791416
  simp only [CollatzResearch.WordTrace]
  refine ⟨69142151016177414573013051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92189534688236552764017401 69142151016177414573013051)
  ·
    refine ⟨103713226524266121859519577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69142151016177414573013051 103713226524266121859519577)
    ·
      refine ⟨77784919893199591394639683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103713226524266121859519577 77784919893199591394639683)
      ·
        refine ⟨116677379839799387091959525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77784919893199591394639683 116677379839799387091959525)
        ·
          refine ⟨21877008719962385079742411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116677379839799387091959525 21877008719962385079742411)
          ·
            refine ⟨32815513079943577619613617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21877008719962385079742411 32815513079943577619613617)
            ·
              refine ⟨24611634809957683214710213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32815513079943577619613617 24611634809957683214710213)
              ·
                refine ⟨4614681526867065602758165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24611634809957683214710213 4614681526867065602758165)
                ·
                  refine ⟨216313196571893700129289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4614681526867065602758165 216313196571893700129289)
                  ·
                    rfl

theorem cell23_3791416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 6].length) (baseStart_3791416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791416 prefixEnd_3791416 := by exact prefixLift 3791416
  have htrace : WordTrace (prefixWord ++ tailWord_3791416) baseStart_3791416 baseEnd_3791416 := by
    simpa [prefixWord, tailWord_3791416, baseEnd_3791416] using wordTrace_append hprefix tailTrace_3791416
  have hstable : (prefixWord ++ tailWord_3791416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791416).length < 2 ^ (prefixWord ++ tailWord_3791416).sum := by decide
  have hdescent : baseEnd_3791416 < baseStart_3791416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791419 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_3791419 : Nat := 118140960795 + 3791419 * 2 ^ 59
def prefixEnd_3791419 : Nat := 4983230072969 + 3 ^ 40 * 3791419 * 2
def baseEnd_3791419 : Nat := 1946820309589006789426087

theorem tailTrace_3791419 : CollatzResearch.WordTrace tailWord_3791419 prefixEnd_3791419 1946820309589006789426087 := by
  unfold tailWord_3791419
  simp only [CollatzResearch.WordTrace]
  refine ⟨138284411451343960658385311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92189607634229307105590207 138284411451343960658385311)
  ·
    refine ⟨207426617177015940987577967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138284411451343960658385311 207426617177015940987577967)
    ·
      refine ⟨311139925765523911481366951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207426617177015940987577967 311139925765523911481366951)
      ·
        refine ⟨466709888648285867222050427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311139925765523911481366951 466709888648285867222050427)
        ·
          refine ⟨700064832972428800833075641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466709888648285867222050427 700064832972428800833075641)
          ·
            refine ⟨525048624729321600624806731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700064832972428800833075641 525048624729321600624806731)
            ·
              refine ⟨787572937093982400937210097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525048624729321600624806731 787572937093982400937210097)
              ·
                refine ⟨590679702820486800702907573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787572937093982400937210097 590679702820486800702907573)
                ·
                  refine ⟨55376222139420637565897585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 590679702820486800702907573 55376222139420637565897585)
                  ·
                    refine ⟨41532166604565478174423189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55376222139420637565897585 41532166604565478174423189)
                    ·
                      refine ⟨1946820309589006789426087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41532166604565478174423189 1946820309589006789426087)
                      ·
                        rfl

theorem cell23_3791419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_3791419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791419 prefixEnd_3791419 := by exact prefixLift 3791419
  have htrace : WordTrace (prefixWord ++ tailWord_3791419) baseStart_3791419 baseEnd_3791419 := by
    simpa [prefixWord, tailWord_3791419, baseEnd_3791419] using wordTrace_append hprefix tailTrace_3791419
  have hstable : (prefixWord ++ tailWord_3791419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791419).length < 2 ^ (prefixWord ++ tailWord_3791419).sum := by decide
  have hdescent : baseEnd_3791419 < baseStart_3791419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791420 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_3791420 : Nat := 118140960795 + 3791420 * 2 ^ 59
def prefixEnd_3791420 : Nat := 4983230072969 + 3 ^ 40 * 3791420 * 2
def baseEnd_3791420 : Nat := 648940274356553761837861

theorem tailTrace_3791420 : CollatzResearch.WordTrace tailWord_3791420 prefixEnd_3791420 648940274356553761837861 := by
  unfold tailWord_3791420
  simp only [CollatzResearch.WordTrace]
  refine ⟨69142223962170168914585857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92189631949560225219447809 69142223962170168914585857)
  ·
    refine ⟨51856667971627626685939393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69142223962170168914585857 51856667971627626685939393)
    ·
      refine ⟨38892500978720720014454545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51856667971627626685939393 38892500978720720014454545)
      ·
        refine ⟨29169375734040540010840909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38892500978720720014454545 29169375734040540010840909)
        ·
          refine ⟨10938515900265202504065341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29169375734040540010840909 10938515900265202504065341)
          ·
            refine ⟨4101943462599450939024503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10938515900265202504065341 4101943462599450939024503)
            ·
              refine ⟨6152915193899176408536755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101943462599450939024503 6152915193899176408536755)
              ·
                refine ⟨9229372790848764612805133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152915193899176408536755 9229372790848764612805133)
                ·
                  refine ⟨3461014796568286729801925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9229372790848764612805133 3461014796568286729801925)
                  ·
                    refine ⟨648940274356553761837861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3461014796568286729801925 648940274356553761837861)
                    ·
                      rfl

theorem cell23_3791420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_3791420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791420 prefixEnd_3791420 := by exact prefixLift 3791420
  have htrace : WordTrace (prefixWord ++ tailWord_3791420) baseStart_3791420 baseEnd_3791420 := by
    simpa [prefixWord, tailWord_3791420, baseEnd_3791420] using wordTrace_append hprefix tailTrace_3791420
  have hstable : (prefixWord ++ tailWord_3791420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791420).length < 2 ^ (prefixWord ++ tailWord_3791420).sum := by decide
  have hdescent : baseEnd_3791420 < baseStart_3791420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791493 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_3791493 : Nat := 118140960795 + 3791493 * 2 ^ 59
def prefixEnd_3791493 : Nat := 4983230072969 + 3 ^ 40 * 3791493 * 2
def baseEnd_3791493 : Nat := 648952769052479833300249

theorem tailTrace_3791493 : CollatzResearch.WordTrace tailWord_3791493 prefixEnd_3791493 648952769052479833300249 := by
  unfold tailWord_3791493
  simp only [CollatzResearch.WordTrace]
  refine ⟨138287110453075871296579133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92191406968717247531052755 138287110453075871296579133)
  ·
    refine ⟨51857666419903451736217175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138287110453075871296579133 51857666419903451736217175)
    ·
      refine ⟨77786499629855177604325763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51857666419903451736217175 77786499629855177604325763)
      ·
        refine ⟨116679749444782766406488645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77786499629855177604325763 116679749444782766406488645)
        ·
          refine ⟨21877453020896768701216621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116679749444782766406488645 21877453020896768701216621)
          ·
            refine ⟨8204044882836288262956233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21877453020896768701216621 8204044882836288262956233)
            ·
              refine ⟨6153033662127216197217175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8204044882836288262956233 6153033662127216197217175)
              ·
                refine ⟨9229550493190824295825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6153033662127216197217175 9229550493190824295825763)
                ·
                  refine ⟨13844325739786236443738645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9229550493190824295825763 13844325739786236443738645)
                  ·
                    refine ⟨648952769052479833300249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13844325739786236443738645 648952769052479833300249)
                    ·
                      rfl

theorem cell23_3791493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_3791493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791493 prefixEnd_3791493 := by exact prefixLift 3791493
  have htrace : WordTrace (prefixWord ++ tailWord_3791493) baseStart_3791493 baseEnd_3791493 := by
    simpa [prefixWord, tailWord_3791493, baseEnd_3791493] using wordTrace_append hprefix tailTrace_3791493
  have hstable : (prefixWord ++ tailWord_3791493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791493).length < 2 ^ (prefixWord ++ tailWord_3791493).sum := by decide
  have hdescent : baseEnd_3791493 < baseStart_3791493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791514 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_3791514 : Nat := 118140960795 + 3791514 * 2 ^ 59
def prefixEnd_3791514 : Nat := 4983230072969 + 3 ^ 40 * 3791514 * 2
def baseEnd_3791514 : Nat := 648956363417061305912717

theorem tailTrace_3791514 : CollatzResearch.WordTrace tailWord_3791514 prefixEnd_3791514 648956363417061305912717 := by
  unfold tailWord_3791514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34571969096499947970773399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92191917590666527922062397 34571969096499947970773399)
  ·
    refine ⟨51857953644749921956160099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34571969096499947970773399 51857953644749921956160099)
    ·
      refine ⟨77786930467124882934240149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51857953644749921956160099 77786930467124882934240149)
      ·
        refine ⟨3646262365646478887542507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77786930467124882934240149 3646262365646478887542507)
        ·
          refine ⟨5469393548469718331313761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646262365646478887542507 5469393548469718331313761)
          ·
            refine ⟨4102045161352288748485321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5469393548469718331313761 4102045161352288748485321)
            ·
              refine ⟨3076533871014216561363991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102045161352288748485321 3076533871014216561363991)
              ·
                refine ⟨4614800806521324842045987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076533871014216561363991 4614800806521324842045987)
                ·
                  refine ⟨6922201209781987263068981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614800806521324842045987 6922201209781987263068981)
                  ·
                    refine ⟨648956363417061305912717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6922201209781987263068981 648956363417061305912717)
                    ·
                      rfl

theorem cell23_3791514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_3791514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791514 prefixEnd_3791514 := by exact prefixLift 3791514
  have htrace : WordTrace (prefixWord ++ tailWord_3791514) baseStart_3791514 baseEnd_3791514 := by
    simpa [prefixWord, tailWord_3791514, baseEnd_3791514] using wordTrace_append hprefix tailTrace_3791514
  have hstable : (prefixWord ++ tailWord_3791514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791514).length < 2 ^ (prefixWord ++ tailWord_3791514).sum := by decide
  have hdescent : baseEnd_3791514 < baseStart_3791514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791527 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3791527 : Nat := 118140960795 + 3791527 * 2 ^ 59
def prefixEnd_3791527 : Nat := 4983230072969 + 3 ^ 40 * 3791527 * 2
def baseEnd_3791527 : Nat := 648958588499897455625197

theorem tailTrace_3791527 : CollatzResearch.WordTrace tailWord_3791527 prefixEnd_3791527 648958588499897455625197 := by
  unfold tailWord_3791527
  simp only [CollatzResearch.WordTrace]
  refine ⟨138288350534952695103316835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92192233689968463402211223 138288350534952695103316835)
  ·
    refine ⟨207432525802429042654975253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138288350534952695103316835 207432525802429042654975253)
    ·
      refine ⟨9723399646988861374451965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207432525802429042654975253 9723399646988861374451965)
      ·
        refine ⟨3646274867620823015419487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9723399646988861374451965 3646274867620823015419487)
        ·
          refine ⟨5469412301431234523129231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646274867620823015419487 5469412301431234523129231)
          ·
            refine ⟨8204118452146851784693847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469412301431234523129231 8204118452146851784693847)
            ·
              refine ⟨12306177678220277677040771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204118452146851784693847 12306177678220277677040771)
              ·
                refine ⟨18459266517330416515561157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306177678220277677040771 18459266517330416515561157)
                ·
                  refine ⟨3461112471999453096667717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18459266517330416515561157 3461112471999453096667717)
                  ·
                    refine ⟨648958588499897455625197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3461112471999453096667717 648958588499897455625197)
                    ·
                      rfl

theorem cell23_3791527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3791527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791527 prefixEnd_3791527 := by exact prefixLift 3791527
  have htrace : WordTrace (prefixWord ++ tailWord_3791527) baseStart_3791527 baseEnd_3791527 := by
    simpa [prefixWord, tailWord_3791527, baseEnd_3791527] using wordTrace_append hprefix tailTrace_3791527
  have hstable : (prefixWord ++ tailWord_3791527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791527).length < 2 ^ (prefixWord ++ tailWord_3791527).sum := by decide
  have hdescent : baseEnd_3791527 < baseStart_3791527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791534 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3791534 : Nat := 118140960795 + 3791534 * 2 ^ 59
def prefixEnd_3791534 : Nat := 4983230072969 + 3 ^ 40 * 3791534 * 2
def baseEnd_3791534 : Nat := 1946879359864273839488059

theorem tailTrace_3791534 : CollatzResearch.WordTrace tailWord_3791534 prefixEnd_3791534 1946879359864273839488059 := by
  unfold tailWord_3791534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17286075730740916912352707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92192403897284890199214437 17286075730740916912352707)
  ·
    refine ⟨25929113596111375368529061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17286075730740916912352707 25929113596111375368529061)
    ·
      refine ⟨4861708799270882881599199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25929113596111375368529061 4861708799270882881599199)
      ·
        refine ⟨7292563198906324322398799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861708799270882881599199 7292563198906324322398799)
        ·
          refine ⟨10938844798359486483598199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292563198906324322398799 10938844798359486483598199)
          ·
            refine ⟨16408267197539229725397299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938844798359486483598199 16408267197539229725397299)
            ·
              refine ⟨24612400796308844588095949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16408267197539229725397299 24612400796308844588095949)
              ·
                refine ⟨9229650298615816720535981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24612400796308844588095949 9229650298615816720535981)
                ·
                  refine ⟨3461118861980931270200993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9229650298615816720535981 3461118861980931270200993)
                  ·
                    refine ⟨2595839146485698452650745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461118861980931270200993 2595839146485698452650745)
                    ·
                      refine ⟨1946879359864273839488059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595839146485698452650745 1946879359864273839488059)
                      ·
                        rfl

theorem cell23_3791534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3791534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791534 prefixEnd_3791534 := by exact prefixLift 3791534
  have htrace : WordTrace (prefixWord ++ tailWord_3791534) baseStart_3791534 baseEnd_3791534 := by
    simpa [prefixWord, tailWord_3791534, baseEnd_3791534] using wordTrace_append hprefix tailTrace_3791534
  have hstable : (prefixWord ++ tailWord_3791534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791534).length < 2 ^ (prefixWord ++ tailWord_3791534).sum := by decide
  have hdescent : baseEnd_3791534 < baseStart_3791534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791630 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_3791630 : Nat := 118140960795 + 3791630 * 2 ^ 59
def prefixEnd_3791630 : Nat := 4983230072969 + 3 ^ 40 * 3791630 * 2
def baseEnd_3791630 : Nat := 216325406000789495987513

theorem tailTrace_3791630 : CollatzResearch.WordTrace tailWord_3791630 prefixEnd_3791630 216325406000789495987513 := by
  unfold tailWord_3791630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17286513406697442961789543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92194738169053029129544229 17286513406697442961789543)
  ·
    refine ⟨25929770110046164442684315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17286513406697442961789543 25929770110046164442684315)
    ·
      refine ⟨38894655165069246664026473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25929770110046164442684315 38894655165069246664026473)
      ·
        refine ⟨29170991373801934998019855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38894655165069246664026473 29170991373801934998019855)
        ·
          refine ⟨43756487060702902497029783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29170991373801934998019855 43756487060702902497029783)
          ·
            refine ⟨65634730591054353745544675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43756487060702902497029783 65634730591054353745544675)
            ·
              refine ⟨98452095886581530618317013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65634730591054353745544675 98452095886581530618317013)
              ·
                refine ⟨2307470997341754623866805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98452095886581530618317013 2307470997341754623866805)
                ·
                  refine ⟨216325406000789495987513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307470997341754623866805 216325406000789495987513)
                  ·
                    rfl

theorem cell23_3791630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_3791630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791630 prefixEnd_3791630 := by exact prefixLift 3791630
  have htrace : WordTrace (prefixWord ++ tailWord_3791630) baseStart_3791630 baseEnd_3791630 := by
    simpa [prefixWord, tailWord_3791630, baseEnd_3791630] using wordTrace_append hprefix tailTrace_3791630
  have hstable : (prefixWord ++ tailWord_3791630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791630).length < 2 ^ (prefixWord ++ tailWord_3791630).sum := by decide
  have hdescent : baseEnd_3791630 < baseStart_3791630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791647 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 5]
def baseStart_3791647 : Nat := 118140960795 + 3791647 * 2 ^ 59
def prefixEnd_3791647 : Nat := 4983230072969 + 3 ^ 40 * 3791647 * 2
def baseEnd_3791647 : Nat := 216326375908692433041671

theorem tailTrace_3791647 : CollatzResearch.WordTrace tailWord_3791647 prefixEnd_3791647 216326375908692433041671 := by
  unfold tailWord_3791647
  simp only [CollatzResearch.WordTrace]
  refine ⟨138292727294517955597685195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92195151529678637065123463 138292727294517955597685195)
  ·
    refine ⟨207439090941776933396527793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138292727294517955597685195 207439090941776933396527793)
    ·
      refine ⟨155579318206332700047395845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207439090941776933396527793 155579318206332700047395845)
      ·
        refine ⟨29171122163687381258886721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155579318206332700047395845 29171122163687381258886721)
        ·
          refine ⟨21878341622765535944165041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29171122163687381258886721 21878341622765535944165041)
          ·
            refine ⟨16408756217074151958123781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21878341622765535944165041 16408756217074151958123781)
            ·
              refine ⟨3076641790701403492148209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16408756217074151958123781 3076641790701403492148209)
              ·
                refine ⟨2307481343026052619111157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076641790701403492148209 2307481343026052619111157)
                ·
                  refine ⟨216326375908692433041671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307481343026052619111157 216326375908692433041671)
                  ·
                    rfl

theorem cell23_3791647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 5].length) (baseStart_3791647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791647 prefixEnd_3791647 := by exact prefixLift 3791647
  have htrace : WordTrace (prefixWord ++ tailWord_3791647) baseStart_3791647 baseEnd_3791647 := by
    simpa [prefixWord, tailWord_3791647, baseEnd_3791647] using wordTrace_append hprefix tailTrace_3791647
  have hstable : (prefixWord ++ tailWord_3791647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791647).length < 2 ^ (prefixWord ++ tailWord_3791647).sum := by decide
  have hdescent : baseEnd_3791647 < baseStart_3791647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791653 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3791653 : Nat := 118140960795 + 3791653 * 2 ^ 59
def prefixEnd_3791653 : Nat := 4983230072969 + 3 ^ 40 * 3791653 * 2
def baseEnd_3791653 : Nat := 1946940464062158873900011

theorem tailTrace_3791653 : CollatzResearch.WordTrace tailWord_3791653 prefixEnd_3791653 1946940464062158873900011 := by
  unfold tailWord_3791653
  simp only [CollatzResearch.WordTrace]
  refine ⟨138292946132496218622403613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92195297421664145748269075 138292946132496218622403613)
  ·
    refine ⟨51859854799686081983401355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138292946132496218622403613 51859854799686081983401355)
    ·
      refine ⟨77789782199529122975102033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51859854799686081983401355 77789782199529122975102033)
      ·
        refine ⟨58342336649646842231326525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77789782199529122975102033 58342336649646842231326525)
        ·
          refine ⟨21878376243617565836747447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58342336649646842231326525 21878376243617565836747447)
          ·
            refine ⟨32817564365426348755121171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21878376243617565836747447 32817564365426348755121171)
            ·
              refine ⟨49226346548139523132681757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32817564365426348755121171 49226346548139523132681757)
              ·
                refine ⟨18459879955552321174755659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49226346548139523132681757 18459879955552321174755659)
                ·
                  refine ⟨27689819933328481762133489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18459879955552321174755659 27689819933328481762133489)
                  ·
                    refine ⟨20767364949996361321600117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27689819933328481762133489 20767364949996361321600117)
                    ·
                      refine ⟨1946940464062158873900011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20767364949996361321600117 1946940464062158873900011)
                      ·
                        rfl

theorem cell23_3791653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3791653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791653 prefixEnd_3791653 := by exact prefixLift 3791653
  have htrace : WordTrace (prefixWord ++ tailWord_3791653) baseStart_3791653 baseEnd_3791653 := by
    simpa [prefixWord, tailWord_3791653, baseEnd_3791653] using wordTrace_append hprefix tailTrace_3791653
  have hstable : (prefixWord ++ tailWord_3791653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791653).length < 2 ^ (prefixWord ++ tailWord_3791653).sum := by decide
  have hdescent : baseEnd_3791653 < baseStart_3791653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791763 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 5, 6]
def baseStart_3791763 : Nat := 118140960795 + 3791763 * 2 ^ 59
def prefixEnd_3791763 : Nat := 4983230072969 + 3 ^ 40 * 3791763 * 2
def baseEnd_3791763 : Nat := 648998982311384481174835

theorem tailTrace_3791763 : CollatzResearch.WordTrace tailWord_3791763 prefixEnd_3791763 648998982311384481174835 := by
  unfold tailWord_3791763
  simp only [CollatzResearch.WordTrace]
  refine ⟨138296958162097707408907943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92197972108065138272605295 138296958162097707408907943)
  ·
    refine ⟨207445437243146561113361915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138296958162097707408907943 207445437243146561113361915)
    ·
      refine ⟨311168155864719841670042873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207445437243146561113361915 311168155864719841670042873)
      ·
        refine ⟨233376116898539881252532155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311168155864719841670042873 233376116898539881252532155)
        ·
          refine ⟨350064175347809821878798233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233376116898539881252532155 350064175347809821878798233)
          ·
            refine ⟨262548131510857366409098675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350064175347809821878798233 262548131510857366409098675)
            ·
              refine ⟨393822197266286049613648013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262548131510857366409098675 393822197266286049613648013)
              ·
                refine ⟨147683323974857268605118005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393822197266286049613648013 147683323974857268605118005)
                ·
                  refine ⟨13845311622642868931729813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147683323974857268605118005 13845311622642868931729813)
                  ·
                    refine ⟨648998982311384481174835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13845311622642868931729813 648998982311384481174835)
                    ·
                      rfl

theorem cell23_3791763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 6].length) (baseStart_3791763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791763 prefixEnd_3791763 := by exact prefixLift 3791763
  have htrace : WordTrace (prefixWord ++ tailWord_3791763) baseStart_3791763 baseEnd_3791763 := by
    simpa [prefixWord, tailWord_3791763, baseEnd_3791763] using wordTrace_append hprefix tailTrace_3791763
  have hstable : (prefixWord ++ tailWord_3791763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791763).length < 2 ^ (prefixWord ++ tailWord_3791763).sum := by decide
  have hdescent : baseEnd_3791763 < baseStart_3791763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791780 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_3791780 : Nat := 118140960795 + 3791780 * 2 ^ 59
def prefixEnd_3791780 : Nat := 4983230072969 + 3 ^ 40 * 3791780 * 2
def baseEnd_3791780 : Nat := 649001892035093292337309

theorem tailTrace_3791780 : CollatzResearch.WordTrace tailWord_3791780 prefixEnd_3791780 649001892035093292337309 := by
  unfold tailWord_3791780
  simp only [CollatzResearch.WordTrace]
  refine ⟨69148789101518059656138397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92198385468690746208184529 69148789101518059656138397)
  ·
    refine ⟨25930795913069272371051899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69148789101518059656138397 25930795913069272371051899)
    ·
      refine ⟨38896193869603908556577849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25930795913069272371051899 38896193869603908556577849)
      ·
        refine ⟨29172145402202931417433387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38896193869603908556577849 29172145402202931417433387)
        ·
          refine ⟨43758218103304397126150081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29172145402202931417433387 43758218103304397126150081)
          ·
            refine ⟨32818663577478297844612561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43758218103304397126150081 32818663577478297844612561)
            ·
              refine ⟨24613997683108723383459421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32818663577478297844612561 24613997683108723383459421)
              ·
                refine ⟨9230249131165771268797283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24613997683108723383459421 9230249131165771268797283)
                ·
                  refine ⟨13845373696748656903195925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9230249131165771268797283 13845373696748656903195925)
                  ·
                    refine ⟨649001892035093292337309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13845373696748656903195925 649001892035093292337309)
                    ·
                      rfl

theorem cell23_3791780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_3791780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791780 prefixEnd_3791780 := by exact prefixLift 3791780
  have htrace : WordTrace (prefixWord ++ tailWord_3791780) baseStart_3791780 baseEnd_3791780 := by
    simpa [prefixWord, tailWord_3791780, baseEnd_3791780] using wordTrace_append hprefix tailTrace_3791780
  have hstable : (prefixWord ++ tailWord_3791780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791780).length < 2 ^ (prefixWord ++ tailWord_3791780).sum := by decide
  have hdescent : baseEnd_3791780 < baseStart_3791780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791800 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_3791800 : Nat := 118140960795 + 3791800 * 2 ^ 59
def prefixEnd_3791800 : Nat := 4983230072969 + 3 ^ 40 * 3791800 * 2
def baseEnd_3791800 : Nat := 1947015945718369798761835

theorem tailTrace_3791800 : CollatzResearch.WordTrace tailWord_3791800 prefixEnd_3791800 1947015945718369798761835 := by
  unfold tailWord_3791800
  simp only [CollatzResearch.WordTrace]
  refine ⟨69149153831481831364002427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92198871775309108485336569 69149153831481831364002427)
  ·
    refine ⟨103723730747222747046003641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69149153831481831364002427 103723730747222747046003641)
    ·
      refine ⟨77792798060417060284502731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103723730747222747046003641 77792798060417060284502731)
      ·
        refine ⟨116689197090625590426754097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77792798060417060284502731 116689197090625590426754097)
        ·
          refine ⟨87516897817969192820065573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116689197090625590426754097 87516897817969192820065573)
          ·
            refine ⟨16409418340869223653762295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87516897817969192820065573 16409418340869223653762295)
            ·
              refine ⟨24614127511303835480643443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16409418340869223653762295 24614127511303835480643443)
              ·
                refine ⟨36921191266955753220965165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24614127511303835480643443 36921191266955753220965165)
                ·
                  refine ⟨13845446725108407457861937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36921191266955753220965165 13845446725108407457861937)
                  ·
                    refine ⟨10384085043831305593396453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13845446725108407457861937 10384085043831305593396453)
                    ·
                      refine ⟨1947015945718369798761835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10384085043831305593396453 1947015945718369798761835)
                      ·
                        rfl

theorem cell23_3791800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_3791800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791800 prefixEnd_3791800 := by exact prefixLift 3791800
  have htrace : WordTrace (prefixWord ++ tailWord_3791800) baseStart_3791800 baseEnd_3791800 := by
    simpa [prefixWord, tailWord_3791800, baseEnd_3791800] using wordTrace_append hprefix tailTrace_3791800
  have hstable : (prefixWord ++ tailWord_3791800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791800).length < 2 ^ (prefixWord ++ tailWord_3791800).sum := by decide
  have hdescent : baseEnd_3791800 < baseStart_3791800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791803 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_3791803 : Nat := 118140960795 + 3791803 * 2 ^ 59
def prefixEnd_3791803 : Nat := 4983230072969 + 3 ^ 40 * 3791803 * 2
def baseEnd_3791803 : Nat := 1947017486160333287024321

theorem tailTrace_3791803 : CollatzResearch.WordTrace tailWord_3791803 prefixEnd_3791803 1947017486160333287024321 := by
  unfold tailWord_3791803
  simp only [CollatzResearch.WordTrace]
  refine ⟨138298417081952794240364063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92198944721301862826909375 138298417081952794240364063)
  ·
    refine ⟨207447625622929191360546095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138298417081952794240364063 207447625622929191360546095)
    ·
      refine ⟨311171438434393787040819143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207447625622929191360546095 311171438434393787040819143)
      ·
        refine ⟨466757157651590680561228715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311171438434393787040819143 466757157651590680561228715)
        ·
          refine ⟨700135736477386020841843073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466757157651590680561228715 700135736477386020841843073)
          ·
            refine ⟨525101802358039515631382305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700135736477386020841843073 525101802358039515631382305)
            ·
              refine ⟨393826351768529636723536729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525101802358039515631382305 393826351768529636723536729)
              ·
                refine ⟨295369763826397227542652547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393826351768529636723536729 295369763826397227542652547)
                ·
                  refine ⟨443054645739595841313978821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295369763826397227542652547 443054645739595841313978821)
                  ·
                    refine ⟨83072746076174220246371029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443054645739595841313978821 83072746076174220246371029)
                    ·
                      refine ⟨1947017486160333287024321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83072746076174220246371029 1947017486160333287024321)
                      ·
                        rfl

theorem cell23_3791803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_3791803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791803 prefixEnd_3791803 := by exact prefixLift 3791803
  have htrace : WordTrace (prefixWord ++ tailWord_3791803) baseStart_3791803 baseEnd_3791803 := by
    simpa [prefixWord, tailWord_3791803, baseEnd_3791803] using wordTrace_append hprefix tailTrace_3791803
  have hstable : (prefixWord ++ tailWord_3791803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791803).length < 2 ^ (prefixWord ++ tailWord_3791803).sum := by decide
  have hdescent : baseEnd_3791803 < baseStart_3791803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791810 : List Nat := [3, 5, 15]
def baseStart_3791810 : Nat := 118140960795 + 3791810 * 2 ^ 59
def prefixEnd_3791810 : Nat := 4983230072969 + 3 ^ 40 * 3791810 * 2
def baseEnd_3791810 : Nat := 296756756671988227349

theorem tailTrace_3791810 : CollatzResearch.WordTrace tailWord_3791810 prefixEnd_3791810 296756756671988227349 := by
  unfold tailWord_3791810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34574668098231858608967221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92199114928618289623912589 34574668098231858608967221)
  ·
    refine ⟨3241375134209236744590677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34574668098231858608967221 3241375134209236744590677)
    ·
      refine ⟨296756756671988227349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 3241375134209236744590677 296756756671988227349)
      ·
        rfl

theorem cell23_3791810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 15].length) (baseStart_3791810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791810 prefixEnd_3791810 := by exact prefixLift 3791810
  have htrace : WordTrace (prefixWord ++ tailWord_3791810) baseStart_3791810 baseEnd_3791810 := by
    simpa [prefixWord, tailWord_3791810, baseEnd_3791810] using wordTrace_append hprefix tailTrace_3791810
  have hstable : (prefixWord ++ tailWord_3791810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791810).length < 2 ^ (prefixWord ++ tailWord_3791810).sum := by decide
  have hdescent : baseEnd_3791810 < baseStart_3791810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791914 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3791914 : Nat := 118140960795 + 3791914 * 2 ^ 59
def prefixEnd_3791914 : Nat := 4983230072969 + 3 ^ 40 * 3791914 * 2
def baseEnd_3791914 : Nat := 1947074482512982352736311

theorem tailTrace_3791914 : CollatzResearch.WordTrace tailWord_3791914 prefixEnd_3791914 1947074482512982352736311 := by
  unfold tailWord_3791914
  simp only [CollatzResearch.WordTrace]
  refine ⟨34575616396137665049413699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92201643723033773465103197 34575616396137665049413699)
  ·
    refine ⟨51863424594206497574120549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34575616396137665049413699 51863424594206497574120549)
    ·
      refine ⟨9724392111413718295147603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51863424594206497574120549 9724392111413718295147603)
      ·
        refine ⟨14586588167120577442721405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9724392111413718295147603 14586588167120577442721405)
        ·
          refine ⟨5469970562670216541020527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14586588167120577442721405 5469970562670216541020527)
          ·
            refine ⟨8204955844005324811530791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469970562670216541020527 8204955844005324811530791)
            ·
              refine ⟨12307433766007987217296187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204955844005324811530791 12307433766007987217296187)
              ·
                refine ⟨18461150649011980825944281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307433766007987217296187 18461150649011980825944281)
                ·
                  refine ⟨13845862986758985619458211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18461150649011980825944281 13845862986758985619458211)
                  ·
                    refine ⟨20768794480138478429187317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13845862986758985619458211 20768794480138478429187317)
                    ·
                      refine ⟨1947074482512982352736311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20768794480138478429187317 1947074482512982352736311)
                      ·
                        rfl

theorem cell23_3791914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3791914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791914 prefixEnd_3791914 := by exact prefixLift 3791914
  have htrace : WordTrace (prefixWord ++ tailWord_3791914) baseStart_3791914 baseEnd_3791914 := by
    simpa [prefixWord, tailWord_3791914, baseEnd_3791914] using wordTrace_append hprefix tailTrace_3791914
  have hstable : (prefixWord ++ tailWord_3791914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791914).length < 2 ^ (prefixWord ++ tailWord_3791914).sum := by decide
  have hdescent : baseEnd_3791914 < baseStart_3791914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791934 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_3791934 : Nat := 118140960795 + 3791934 * 2 ^ 59
def prefixEnd_3791934 : Nat := 4983230072969 + 3 ^ 40 * 3791934 * 2
def baseEnd_3791934 : Nat := 216342750236230252720691

theorem tailTrace_3791934 : CollatzResearch.WordTrace tailWord_3791934 prefixEnd_3791934 216342750236230252720691 := by
  unfold tailWord_3791934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17287899380559775451672857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92202130029652135742255237 17287899380559775451672857)
  ·
    refine ⟨12965924535419831588754643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17287899380559775451672857 12965924535419831588754643)
    ·
      refine ⟨19448886803129747383131965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12965924535419831588754643 19448886803129747383131965)
      ·
        refine ⟨7293332551173655268674487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19448886803129747383131965 7293332551173655268674487)
        ·
          refine ⟨10939998826760482903011731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293332551173655268674487 10939998826760482903011731)
          ·
            refine ⟨16409998240140724354517597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10939998826760482903011731 16409998240140724354517597)
            ·
              refine ⟨6153749340052771632944099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16409998240140724354517597 6153749340052771632944099)
              ·
                refine ⟨9230624010079157449416149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6153749340052771632944099 9230624010079157449416149)
                ·
                  refine ⟨216342750236230252720691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9230624010079157449416149 216342750236230252720691)
                  ·
                    rfl

theorem cell23_3791934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_3791934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791934 prefixEnd_3791934 := by exact prefixLift 3791934
  have htrace : WordTrace (prefixWord ++ tailWord_3791934) baseStart_3791934 baseEnd_3791934 := by
    simpa [prefixWord, tailWord_3791934, baseEnd_3791934] using wordTrace_append hprefix tailTrace_3791934
  have hstable : (prefixWord ++ tailWord_3791934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791934).length < 2 ^ (prefixWord ++ tailWord_3791934).sum := by decide
  have hdescent : baseEnd_3791934 < baseStart_3791934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791964 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3791964 : Nat := 118140960795 + 3791964 * 2 ^ 59
def prefixEnd_3791964 : Nat := 4983230072969 + 3 ^ 40 * 3791964 * 2
def baseEnd_3791964 : Nat := 649033385515235719037027

theorem tailTrace_3791964 : CollatzResearch.WordTrace tailWord_3791964 prefixEnd_3791964 649033385515235719037027 := by
  unfold tailWord_3791964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69152144617184759368487473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92202859489579679157983297 69152144617184759368487473)
  ·
    refine ⟨51864108462888569526365605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69152144617184759368487473 51864108462888569526365605)
    ·
      refine ⟨9724520336791606786193551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51864108462888569526365605 9724520336791606786193551)
      ·
        refine ⟨14586780505187410179290327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9724520336791606786193551 14586780505187410179290327)
        ·
          refine ⟨21880170757781115268935491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14586780505187410179290327 21880170757781115268935491)
          ·
            refine ⟨32820256136671672903403237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21880170757781115268935491 32820256136671672903403237)
            ·
              refine ⟨6153798025625938669388107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32820256136671672903403237 6153798025625938669388107)
              ·
                refine ⟨9230697038438908004082161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6153798025625938669388107 9230697038438908004082161)
                ·
                  refine ⟨6923022778829181003061621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9230697038438908004082161 6923022778829181003061621)
                  ·
                    refine ⟨649033385515235719037027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6923022778829181003061621 649033385515235719037027)
                    ·
                      rfl

theorem cell23_3791964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3791964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791964 prefixEnd_3791964 := by exact prefixLift 3791964
  have htrace : WordTrace (prefixWord ++ tailWord_3791964) baseStart_3791964 baseEnd_3791964 := by
    simpa [prefixWord, tailWord_3791964, baseEnd_3791964] using wordTrace_append hprefix tailTrace_3791964
  have hstable : (prefixWord ++ tailWord_3791964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791964).length < 2 ^ (prefixWord ++ tailWord_3791964).sum := by decide
  have hdescent : baseEnd_3791964 < baseStart_3791964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791984 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 2, 4, 2]
def baseStart_3791984 : Nat := 118140960795 + 3791984 * 2 ^ 59
def prefixEnd_3791984 : Nat := 4983230072969 + 3 ^ 40 * 3791984 * 2
def baseEnd_3791984 : Nat := 1947110426158797078860989

theorem tailTrace_3791984 : CollatzResearch.WordTrace tailWord_3791984 prefixEnd_3791984 1947110426158797078860989 := by
  unfold tailWord_3791984
  simp only [CollatzResearch.WordTrace]
  refine ⟨69152509347148531076351503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92203345796198041435135337 69152509347148531076351503)
  ·
    refine ⟨103728764020722796614527255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69152509347148531076351503 103728764020722796614527255)
    ·
      refine ⟨155593146031084194921790883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103728764020722796614527255 155593146031084194921790883)
      ·
        refine ⟨233389719046626292382686325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155593146031084194921790883 233389719046626292382686325)
        ·
          refine ⟨21880286160621214910876843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233389719046626292382686325 21880286160621214910876843)
          ·
            refine ⟨32820429240931822366315265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21880286160621214910876843 32820429240931822366315265)
            ·
              refine ⟨24615321930698866774736449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32820429240931822366315265 24615321930698866774736449)
              ·
                refine ⟨18461491448024150081052337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24615321930698866774736449 18461491448024150081052337)
                ·
                  refine ⟨13846118586018112560789253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18461491448024150081052337 13846118586018112560789253)
                  ·
                    refine ⟨2596147234878396105147985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13846118586018112560789253 2596147234878396105147985)
                    ·
                      refine ⟨1947110426158797078860989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596147234878396105147985 1947110426158797078860989)
                      ·
                        rfl

theorem cell23_3791984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 4, 2].length) (baseStart_3791984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3791984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3791984 prefixEnd_3791984 := by exact prefixLift 3791984
  have htrace : WordTrace (prefixWord ++ tailWord_3791984) baseStart_3791984 baseEnd_3791984 := by
    simpa [prefixWord, tailWord_3791984, baseEnd_3791984] using wordTrace_append hprefix tailTrace_3791984
  have hstable : (prefixWord ++ tailWord_3791984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791984).length < 2 ^ (prefixWord ++ tailWord_3791984).sum := by decide
  have hdescent : baseEnd_3791984 < baseStart_3791984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792001 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_3792001 : Nat := 118140960795 + 3792001 * 2 ^ 59
def prefixEnd_3792001 : Nat := 4983230072969 + 3 ^ 40 * 3792001 * 2
def baseEnd_3792001 : Nat := 1947119155329923512348411

theorem tailTrace_3792001 : CollatzResearch.WordTrace tailWord_3792001 prefixEnd_3792001 1947119155329923512348411 := by
  unfold tailWord_3792001
  simp only [CollatzResearch.WordTrace]
  refine ⟨138305638735235474056071857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92203759156823649370714571 138305638735235474056071857)
  ·
    refine ⟨103729229051426605542053893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138305638735235474056071857 103729229051426605542053893)
    ·
      refine ⟨19449230447142488539135105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103729229051426605542053893 19449230447142488539135105)
      ·
        refine ⟨14586922835356866404351329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19449230447142488539135105 14586922835356866404351329)
        ·
          refine ⟨10940192126517649803263497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14586922835356866404351329 10940192126517649803263497)
          ·
            refine ⟨8205144094888237352447623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10940192126517649803263497 8205144094888237352447623)
            ·
              refine ⟨12307716142332356028671435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8205144094888237352447623 12307716142332356028671435)
              ·
                refine ⟨18461574213498534043007153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307716142332356028671435 18461574213498534043007153)
                ·
                  refine ⟨13846180660123900532255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18461574213498534043007153 13846180660123900532255365)
                  ·
                    refine ⟨2596158873773231349797881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13846180660123900532255365 2596158873773231349797881)
                    ·
                      refine ⟨1947119155329923512348411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596158873773231349797881 1947119155329923512348411)
                      ·
                        rfl

theorem cell23_3792001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_3792001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792001 prefixEnd_3792001 := by exact prefixLift 3792001
  have htrace : WordTrace (prefixWord ++ tailWord_3792001) baseStart_3792001 baseEnd_3792001 := by
    simpa [prefixWord, tailWord_3792001, baseEnd_3792001] using wordTrace_append hprefix tailTrace_3792001
  have hstable : (prefixWord ++ tailWord_3792001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792001).length < 2 ^ (prefixWord ++ tailWord_3792001).sum := by decide
  have hdescent : baseEnd_3792001 < baseStart_3792001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792028 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_3792028 : Nat := 118140960795 + 3792028 * 2 ^ 59
def prefixEnd_3792028 : Nat := 4983230072969 + 3 ^ 40 * 3792028 * 2
def baseEnd_3792028 : Nat := 649044339769198302236929

theorem tailTrace_3792028 : CollatzResearch.WordTrace tailWord_3792028 prefixEnd_3792028 649044339769198302236929 := by
  unfold tailWord_3792028
  simp only [CollatzResearch.WordTrace]
  refine ⟨69153311753068828833652369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92204415670758438444869825 69153311753068828833652369)
  ·
    refine ⟨51864983814801621625239277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69153311753068828833652369 51864983814801621625239277)
    ·
      refine ⟨19449368930550608109464729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51864983814801621625239277 19449368930550608109464729)
      ·
        refine ⟨14587026697912956082098547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19449368930550608109464729 14587026697912956082098547)
        ·
          refine ⟨21880540046869434123147821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14587026697912956082098547 21880540046869434123147821)
          ·
            refine ⟨8205202517576037796180433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21880540046869434123147821 8205202517576037796180433)
            ·
              refine ⟨6153901888182028347135325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8205202517576037796180433 6153901888182028347135325)
              ·
                refine ⟨2307713208068260630175747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6153901888182028347135325 2307713208068260630175747)
                ·
                  refine ⟨3461569812102390945263621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307713208068260630175747 3461569812102390945263621)
                  ·
                    refine ⟨649044339769198302236929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3461569812102390945263621 649044339769198302236929)
                    ·
                      rfl

theorem cell23_3792028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_3792028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792028 prefixEnd_3792028 := by exact prefixLift 3792028
  have htrace : WordTrace (prefixWord ++ tailWord_3792028) baseStart_3792028 baseEnd_3792028 := by
    simpa [prefixWord, tailWord_3792028, baseEnd_3792028] using wordTrace_append hprefix tailTrace_3792028
  have hstable : (prefixWord ++ tailWord_3792028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792028).length < 2 ^ (prefixWord ++ tailWord_3792028).sum := by decide
  have hdescent : baseEnd_3792028 < baseStart_3792028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792067 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 1, 6]
def baseStart_3792067 : Nat := 118140960795 + 3792067 * 2 ^ 59
def prefixEnd_3792067 : Nat := 4983230072969 + 3 ^ 40 * 3792067 * 2
def baseEnd_3792067 : Nat := 649051015017706751374369

theorem tailTrace_3792067 : CollatzResearch.WordTrace tailWord_3792067 prefixEnd_3792067 649051015017706751374369 := by
  unfold tailWord_3792067
  simp only [CollatzResearch.WordTrace]
  refine ⟨138308045952996367327974455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92205363968664244885316303 138308045952996367327974455)
  ·
    refine ⟨207462068929494550991961683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138308045952996367327974455 207462068929494550991961683)
    ·
      refine ⟨311193103394241826487942525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207462068929494550991961683 311193103394241826487942525)
      ·
        refine ⟨116697413772840684932978447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311193103394241826487942525 116697413772840684932978447)
        ·
          refine ⟨175046120659261027399467671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116697413772840684932978447 175046120659261027399467671)
          ·
            refine ⟨262569180988891541099201507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175046120659261027399467671 262569180988891541099201507)
            ·
              refine ⟨393853771483337311648802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262569180988891541099201507 393853771483337311648802261)
              ·
                refine ⟨9230947769140718241768803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 393853771483337311648802261 9230947769140718241768803)
                ·
                  refine ⟨13846421653711077362653205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9230947769140718241768803 13846421653711077362653205)
                  ·
                    refine ⟨649051015017706751374369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13846421653711077362653205 649051015017706751374369)
                    ·
                      rfl

theorem cell23_3792067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 6].length) (baseStart_3792067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792067 prefixEnd_3792067 := by exact prefixLift 3792067
  have htrace : WordTrace (prefixWord ++ tailWord_3792067) baseStart_3792067 baseEnd_3792067 := by
    simpa [prefixWord, tailWord_3792067, baseEnd_3792067] using wordTrace_append hprefix tailTrace_3792067
  have hstable : (prefixWord ++ tailWord_3792067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792067).length < 2 ^ (prefixWord ++ tailWord_3792067).sum := by decide
  have hdescent : baseEnd_3792067 < baseStart_3792067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792085 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3792085 : Nat := 118140960795 + 3792085 * 2 ^ 59
def prefixEnd_3792085 : Nat := 4983230072969 + 3 ^ 40 * 3792085 * 2
def baseEnd_3792085 : Nat := 1947162287704901183698025

theorem tailTrace_3792085 : CollatzResearch.WordTrace tailWord_3792085 prefixEnd_3792085 1947162287704901183698025 := by
  unfold tailWord_3792085
  simp only [CollatzResearch.WordTrace]
  refine ⟨138308702466931156402129709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92205801644620770934753139 138308702466931156402129709)
  ·
    refine ⟨51865763425099183650798641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138308702466931156402129709 51865763425099183650798641)
    ·
      refine ⟨38899322568824387738098981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51865763425099183650798641 38899322568824387738098981)
      ·
        refine ⟨7293622981654572700893559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38899322568824387738098981 7293622981654572700893559)
        ·
          refine ⟨10940434472481859051340339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293622981654572700893559 10940434472481859051340339)
          ·
            refine ⟨16410651708722788577010509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940434472481859051340339 16410651708722788577010509)
            ·
              refine ⟨6153994390771045716378941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16410651708722788577010509 6153994390771045716378941)
              ·
                refine ⟨2307747896539142143642103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6153994390771045716378941 2307747896539142143642103)
                ·
                  refine ⟨3461621844808713215463155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307747896539142143642103 3461621844808713215463155)
                  ·
                    refine ⟨5192432767213069823194733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3461621844808713215463155 5192432767213069823194733)
                    ·
                      refine ⟨1947162287704901183698025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5192432767213069823194733 1947162287704901183698025)
                      ·
                        rfl

theorem cell23_3792085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3792085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792085 prefixEnd_3792085 := by exact prefixLift 3792085
  have htrace : WordTrace (prefixWord ++ tailWord_3792085) baseStart_3792085 baseEnd_3792085 := by
    simpa [prefixWord, tailWord_3792085, baseEnd_3792085] using wordTrace_append hprefix tailTrace_3792085
  have hstable : (prefixWord ++ tailWord_3792085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792085).length < 2 ^ (prefixWord ++ tailWord_3792085).sum := by decide
  have hdescent : baseEnd_3792085 < baseStart_3792085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792097 : List Nat := [1, 2, 3, 1, 3, 2, 11]
def baseStart_3792097 : Nat := 118140960795 + 3792097 * 2 ^ 59
def prefixEnd_3792097 : Nat := 4983230072969 + 3 ^ 40 * 3792097 * 2
def baseEnd_3792097 : Nat := 24039116660157470824049

theorem tailTrace_3792097 : CollatzResearch.WordTrace tailWord_3792097 prefixEnd_3792097 24039116660157470824049 := by
  unfold tailWord_3792097
  simp only [CollatzResearch.WordTrace]
  refine ⟨138309140142887682451566545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92206093428591788301044363 138309140142887682451566545)
  ·
    refine ⟨103731855107165761838674909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138309140142887682451566545 103731855107165761838674909)
    ·
      refine ⟨38899445665187160689503091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103731855107165761838674909 38899445665187160689503091)
      ·
        refine ⟨58349168497780741034254637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38899445665187160689503091 58349168497780741034254637)
        ·
          refine ⟨21880938186667777887845489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58349168497780741034254637 21880938186667777887845489)
          ·
            refine ⟨16410703640000833415884117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21880938186667777887845489 16410703640000833415884117)
            ·
              refine ⟨24039116660157470824049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16410703640000833415884117 24039116660157470824049)
              ·
                rfl

theorem cell23_3792097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 11].length) (baseStart_3792097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792097 prefixEnd_3792097 := by exact prefixLift 3792097
  have htrace : WordTrace (prefixWord ++ tailWord_3792097) baseStart_3792097 baseEnd_3792097 := by
    simpa [prefixWord, tailWord_3792097, baseEnd_3792097] using wordTrace_append hprefix tailTrace_3792097
  have hstable : (prefixWord ++ tailWord_3792097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792097).length < 2 ^ (prefixWord ++ tailWord_3792097).sum := by decide
  have hdescent : baseEnd_3792097 < baseStart_3792097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792108 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 3, 2, 2]
def baseStart_3792108 : Nat := 118140960795 + 3792108 * 2 ^ 59
def prefixEnd_3792108 : Nat := 4983230072969 + 3 ^ 40 * 3792108 * 2
def baseEnd_3792108 : Nat := 1947174097759954593710419

theorem tailTrace_3792108 : CollatzResearch.WordTrace tailWord_3792108 prefixEnd_3792108 1947174097759954593710419 := by
  unfold tailWord_3792108
  simp only [CollatzResearch.WordTrace]
  refine ⟨69154770672923915665108489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92206360897231887553477985 69154770672923915665108489)
  ·
    refine ⟨51866078004692936748831367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69154770672923915665108489 51866078004692936748831367)
    ·
      refine ⟨77799117007039405123247051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51866078004692936748831367 77799117007039405123247051)
      ·
        refine ⟨116698675510559107684870577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77799117007039405123247051 116698675510559107684870577)
        ·
          refine ⟨87524006632919330763652933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116698675510559107684870577 87524006632919330763652933)
          ·
            refine ⟨16410751243672374518184925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87524006632919330763652933 16410751243672374518184925)
            ·
              refine ⟨6154031716377140444319347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16410751243672374518184925 6154031716377140444319347)
              ·
                refine ⟨9231047574565710666479021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154031716377140444319347 9231047574565710666479021)
                ·
                  refine ⟨3461642840462141499929633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9231047574565710666479021 3461642840462141499929633)
                  ·
                    refine ⟨2596232130346606124947225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461642840462141499929633 2596232130346606124947225)
                    ·
                      refine ⟨1947174097759954593710419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596232130346606124947225 1947174097759954593710419)
                      ·
                        rfl

theorem cell23_3792108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_3792108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792108 prefixEnd_3792108 := by exact prefixLift 3792108
  have htrace : WordTrace (prefixWord ++ tailWord_3792108) baseStart_3792108 baseEnd_3792108 := by
    simpa [prefixWord, tailWord_3792108, baseEnd_3792108] using wordTrace_append hprefix tailTrace_3792108
  have hstable : (prefixWord ++ tailWord_3792108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792108).length < 2 ^ (prefixWord ++ tailWord_3792108).sum := by decide
  have hdescent : baseEnd_3792108 < baseStart_3792108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792159 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 1, 2, 2]
def baseStart_3792159 : Nat := 118140960795 + 3792159 * 2 ^ 59
def prefixEnd_3792159 : Nat := 4983230072969 + 3 ^ 40 * 3792159 * 2
def baseEnd_3792159 : Nat := 1947200285273333894172685

theorem tailTrace_3792159 : CollatzResearch.WordTrace tailWord_3792159 prefixEnd_3792159 1947200285273333894172685 := by
  unfold tailWord_3792159
  simp only [CollatzResearch.WordTrace]
  refine ⟨138311401468663067040323531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92207600979108711360215687 138311401468663067040323531)
  ·
    refine ⟨207467102202994600560485297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138311401468663067040323531 207467102202994600560485297)
    ·
      refine ⟨155600326652245950420363973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207467102202994600560485297 155600326652245950420363973)
      ·
        refine ⟨29175061247296115703818245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155600326652245950420363973 29175061247296115703818245)
        ·
          refine ⟨5470323983868021694465921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29175061247296115703818245 5470323983868021694465921)
          ·
            refine ⟨4102742987901016270849441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5470323983868021694465921 4102742987901016270849441)
            ·
              refine ⟨3077057240925762203137081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102742987901016270849441 3077057240925762203137081)
              ·
                refine ⟨2307792930694321652352811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077057240925762203137081 2307792930694321652352811)
                ·
                  refine ⟨3461689396041482478529217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307792930694321652352811 3461689396041482478529217)
                  ·
                    refine ⟨2596267047031111858896913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461689396041482478529217 2596267047031111858896913)
                    ·
                      refine ⟨1947200285273333894172685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596267047031111858896913 1947200285273333894172685)
                      ·
                        rfl

theorem cell23_3792159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_3792159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792159 prefixEnd_3792159 := by exact prefixLift 3792159
  have htrace : WordTrace (prefixWord ++ tailWord_3792159) baseStart_3792159 baseEnd_3792159 := by
    simpa [prefixWord, tailWord_3792159, baseEnd_3792159] using wordTrace_append hprefix tailTrace_3792159
  have hstable : (prefixWord ++ tailWord_3792159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792159).length < 2 ^ (prefixWord ++ tailWord_3792159).sum := by decide
  have hdescent : baseEnd_3792159 < baseStart_3792159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792164 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3792164 : Nat := 118140960795 + 3792164 * 2 ^ 59
def prefixEnd_3792164 : Nat := 4983230072969 + 3 ^ 40 * 3792164 * 2
def baseEnd_3792164 : Nat := 1947202852676606374610161

theorem tailTrace_3792164 : CollatzResearch.WordTrace tailWord_3792164 prefixEnd_3792164 1947202852676606374610161 := by
  unfold tailWord_3792164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69155791916822476447127773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92207722555763301929503697 69155791916822476447127773)
  ·
    refine ⟨25933421968808428667672915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69155791916822476447127773 25933421968808428667672915)
    ·
      refine ⟨38900132953212643001509373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25933421968808428667672915 38900132953212643001509373)
      ·
        refine ⟨14587549857454741125566015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38900132953212643001509373 14587549857454741125566015)
        ·
          refine ⟨21881324786182111688349023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14587549857454741125566015 21881324786182111688349023)
          ·
            refine ⟨32821987179273167532523535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21881324786182111688349023 32821987179273167532523535)
            ·
              refine ⟨49232980768909751298785303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32821987179273167532523535 49232980768909751298785303)
              ·
                refine ⟨73849471153364626948177955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49232980768909751298785303 73849471153364626948177955)
                ·
                  refine ⟨110774206730046940422266933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73849471153364626948177955 110774206730046940422266933)
                  ·
                    refine ⟨10385081880941900664587525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110774206730046940422266933 10385081880941900664587525)
                    ·
                      refine ⟨1947202852676606374610161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10385081880941900664587525 1947202852676606374610161)
                      ·
                        rfl

theorem cell23_3792164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3792164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792164 prefixEnd_3792164 := by exact prefixLift 3792164
  have htrace : WordTrace (prefixWord ++ tailWord_3792164) baseStart_3792164 baseEnd_3792164 := by
    simpa [prefixWord, tailWord_3792164, baseEnd_3792164] using wordTrace_append hprefix tailTrace_3792164
  have hstable : (prefixWord ++ tailWord_3792164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792164).length < 2 ^ (prefixWord ++ tailWord_3792164).sum := by decide
  have hdescent : baseEnd_3792164 < baseStart_3792164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792168 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3792168 : Nat := 118140960795 + 3792168 * 2 ^ 59
def prefixEnd_3792168 : Nat := 4983230072969 + 3 ^ 40 * 3792168 * 2
def baseEnd_3792168 : Nat := 1947204906599224358960143

theorem tailTrace_3792168 : CollatzResearch.WordTrace tailWord_3792168 prefixEnd_3792168 1947204906599224358960143 := by
  unfold tailWord_3792168
  simp only [CollatzResearch.WordTrace]
  refine ⟨69155864862815230788700579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92207819817086974384934105 69155864862815230788700579)
  ·
    refine ⟨103733797294222846183050869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69155864862815230788700579 103733797294222846183050869)
    ·
      refine ⟨9725043496333391829661019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103733797294222846183050869 9725043496333391829661019)
      ·
        refine ⟨14587565244500087744491529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725043496333391829661019 14587565244500087744491529)
        ·
          refine ⟨10940673933375065808368647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14587565244500087744491529 10940673933375065808368647)
          ·
            refine ⟨16411010900062598712552971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940673933375065808368647 16411010900062598712552971)
            ·
              refine ⟨24616516350093898068829457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16411010900062598712552971 24616516350093898068829457)
              ·
                refine ⟨18462387262570423551622093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24616516350093898068829457 18462387262570423551622093)
                ·
                  refine ⟨6923395223463908831858285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18462387262570423551622093 6923395223463908831858285)
                  ·
                    refine ⟨2596273208798965811946857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6923395223463908831858285 2596273208798965811946857)
                    ·
                      refine ⟨1947204906599224358960143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596273208798965811946857 1947204906599224358960143)
                      ·
                        rfl

theorem cell23_3792168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3792168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792168 prefixEnd_3792168 := by exact prefixLift 3792168
  have htrace : WordTrace (prefixWord ++ tailWord_3792168) baseStart_3792168 baseEnd_3792168 := by
    simpa [prefixWord, tailWord_3792168, baseEnd_3792168] using wordTrace_append hprefix tailTrace_3792168
  have hstable : (prefixWord ++ tailWord_3792168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792168).length < 2 ^ (prefixWord ++ tailWord_3792168).sum := by decide
  have hdescent : baseEnd_3792168 < baseStart_3792168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792184 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_3792184 : Nat := 118140960795 + 3792184 * 2 ^ 59
def prefixEnd_3792184 : Nat := 4983230072969 + 3 ^ 40 * 3792184 * 2
def baseEnd_3792184 : Nat := 1947213122289696296360069

theorem tailTrace_3792184 : CollatzResearch.WordTrace tailWord_3792184 prefixEnd_3792184 1947213122289696296360069 := by
  unfold tailWord_3792184
  simp only [CollatzResearch.WordTrace]
  refine ⟨69156156646786248154991803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92208208862381664206655737 69156156646786248154991803)
  ·
    refine ⟨103734234970179372232487705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69156156646786248154991803 103734234970179372232487705)
    ·
      refine ⟨77800676227634529174365779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103734234970179372232487705 77800676227634529174365779)
      ·
        refine ⟨116701014341451793761548669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77800676227634529174365779 116701014341451793761548669)
        ·
          refine ⟨43762880378044422660580751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116701014341451793761548669 43762880378044422660580751)
          ·
            refine ⟨65644320567066633990871127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43762880378044422660580751 65644320567066633990871127)
            ·
              refine ⟨98466480850599950986306691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65644320567066633990871127 98466480850599950986306691)
              ·
                refine ⟨147699721275899926479460037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98466480850599950986306691 147699721275899926479460037)
                ·
                  refine ⟨27693697739231236214898757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147699721275899926479460037 27693697739231236214898757)
                  ·
                    refine ⟨5192568326105856790293517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27693697739231236214898757 5192568326105856790293517)
                    ·
                      refine ⟨1947213122289696296360069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5192568326105856790293517 1947213122289696296360069)
                      ·
                        rfl

theorem cell23_3792184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_3792184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792184 prefixEnd_3792184 := by exact prefixLift 3792184
  have htrace : WordTrace (prefixWord ++ tailWord_3792184) baseStart_3792184 baseEnd_3792184 := by
    simpa [prefixWord, tailWord_3792184, baseEnd_3792184] using wordTrace_append hprefix tailTrace_3792184
  have hstable : (prefixWord ++ tailWord_3792184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792184).length < 2 ^ (prefixWord ++ tailWord_3792184).sum := by decide
  have hdescent : baseEnd_3792184 < baseStart_3792184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792215 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 2, 2, 2]
def baseStart_3792215 : Nat := 118140960795 + 3792215 * 2 ^ 59
def prefixEnd_3792215 : Nat := 4983230072969 + 3 ^ 40 * 3792215 * 2
def baseEnd_3792215 : Nat := 1947229040189985675072427

theorem tailTrace_3792215 : CollatzResearch.WordTrace tailWord_3792215 prefixEnd_3792215 1947229040189985675072427 := by
  unfold tailWord_3792215
  simp only [CollatzResearch.WordTrace]
  refine ⟨138313443956460188604362099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92208962637640125736241399 138313443956460188604362099)
  ·
    refine ⟨207470165934690282906543149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138313443956460188604362099 207470165934690282906543149)
    ·
      refine ⟨77801312225508856089953681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207470165934690282906543149 77801312225508856089953681)
      ·
        refine ⟨58350984169131642067465261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77801312225508856089953681 58350984169131642067465261)
        ·
          refine ⟨21881619063424365775299473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58350984169131642067465261 21881619063424365775299473)
          ·
            refine ⟨16411214297568274331474605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21881619063424365775299473 16411214297568274331474605)
            ·
              refine ⟨6154205361588102874302977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16411214297568274331474605 6154205361588102874302977)
              ·
                refine ⟨4615654021191077155727233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6154205361588102874302977 4615654021191077155727233)
                ·
                  refine ⟨3461740515893307866795425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4615654021191077155727233 3461740515893307866795425)
                  ·
                    refine ⟨2596305386919980900096569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461740515893307866795425 2596305386919980900096569)
                    ·
                      refine ⟨1947229040189985675072427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596305386919980900096569 1947229040189985675072427)
                      ·
                        rfl

theorem cell23_3792215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_3792215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792215 prefixEnd_3792215 := by exact prefixLift 3792215
  have htrace : WordTrace (prefixWord ++ tailWord_3792215) baseStart_3792215 baseEnd_3792215 := by
    simpa [prefixWord, tailWord_3792215, baseEnd_3792215] using wordTrace_append hprefix tailTrace_3792215
  have hstable : (prefixWord ++ tailWord_3792215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792215).length < 2 ^ (prefixWord ++ tailWord_3792215).sum := by decide
  have hdescent : baseEnd_3792215 < baseStart_3792215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792232 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3792232 : Nat := 118140960795 + 3792232 * 2 ^ 59
def prefixEnd_3792232 : Nat := 4983230072969 + 3 ^ 40 * 3792232 * 2
def baseEnd_3792232 : Nat := 1947237769361112108559849

theorem tailTrace_3792232 : CollatzResearch.WordTrace tailWord_3792232 prefixEnd_3792232 1947237769361112108559849 := by
  unfold tailWord_3792232
  simp only [CollatzResearch.WordTrace]
  refine ⟨69157031998699300253865475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92209375998265733671820633 69157031998699300253865475)
  ·
    refine ⟨103735547998048950380798213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69157031998699300253865475 103735547998048950380798213)
    ·
      refine ⟨19450415249634178196399665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103735547998048950380798213 19450415249634178196399665)
      ·
        refine ⟨14587811437225633647299749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19450415249634178196399665 14587811437225633647299749)
        ·
          refine ⟨2735214644479806308868703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14587811437225633647299749 2735214644479806308868703)
          ·
            refine ⟨4102821966719709463303055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735214644479806308868703 4102821966719709463303055)
            ·
              refine ⟨6154232950079564194954583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4102821966719709463303055 6154232950079564194954583)
              ·
                refine ⟨9231349425119346292431875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154232950079564194954583 9231349425119346292431875)
                ·
                  refine ⟨13847024137679019438647813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9231349425119346292431875 13847024137679019438647813)
                  ·
                    refine ⟨2596317025814816144746465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13847024137679019438647813 2596317025814816144746465)
                    ·
                      refine ⟨1947237769361112108559849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596317025814816144746465 1947237769361112108559849)
                      ·
                        rfl

theorem cell23_3792232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3792232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792232 prefixEnd_3792232 := by exact prefixLift 3792232
  have htrace : WordTrace (prefixWord ++ tailWord_3792232) baseStart_3792232 baseEnd_3792232 := by
    simpa [prefixWord, tailWord_3792232, baseEnd_3792232] using wordTrace_append hprefix tailTrace_3792232
  have hstable : (prefixWord ++ tailWord_3792232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792232).length < 2 ^ (prefixWord ++ tailWord_3792232).sum := by decide
  have hdescent : baseEnd_3792232 < baseStart_3792232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792241 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 2, 5, 2]
def baseStart_3792241 : Nat := 118140960795 + 3792241 * 2 ^ 59
def prefixEnd_3792241 : Nat := 4983230072969 + 3 ^ 40 * 3792241 * 2
def baseEnd_3792241 : Nat := 1947242390687002573347307

theorem tailTrace_3792241 : CollatzResearch.WordTrace tailWord_3792241 prefixEnd_3792241 1947242390687002573347307 := by
  unfold tailWord_3792241
  simp only [CollatzResearch.WordTrace]
  refine ⟨138314392254365995044808577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92209594836243996696539051 138314392254365995044808577)
  ·
    refine ⟨103735794190774496283606433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138314392254365995044808577 103735794190774496283606433)
    ·
      refine ⟨77801845643080872212704825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103735794190774496283606433 77801845643080872212704825)
      ·
        refine ⟨58351384232310654159528619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77801845643080872212704825 58351384232310654159528619)
        ·
          refine ⟨87527076348465981239292929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58351384232310654159528619 87527076348465981239292929)
          ·
            refine ⟨65645307261349485929469697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87527076348465981239292929 65645307261349485929469697)
            ·
              refine ⟨49233980446012114447102273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65645307261349485929469697 49233980446012114447102273)
              ·
                refine ⟨36925485334509085835326705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49233980446012114447102273 36925485334509085835326705)
                ·
                  refine ⟨27694114000881814376495029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36925485334509085835326705 27694114000881814376495029)
                  ·
                    refine ⟨2596323187582670097796409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27694114000881814376495029 2596323187582670097796409)
                    ·
                      refine ⟨1947242390687002573347307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596323187582670097796409 1947242390687002573347307)
                      ·
                        rfl

theorem cell23_3792241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_3792241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792241 prefixEnd_3792241 := by exact prefixLift 3792241
  have htrace : WordTrace (prefixWord ++ tailWord_3792241) baseStart_3792241 baseEnd_3792241 := by
    simpa [prefixWord, tailWord_3792241, baseEnd_3792241] using wordTrace_append hprefix tailTrace_3792241
  have hstable : (prefixWord ++ tailWord_3792241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792241).length < 2 ^ (prefixWord ++ tailWord_3792241).sum := by decide
  have hdescent : baseEnd_3792241 < baseStart_3792241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792291 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 3]
def baseStart_3792291 : Nat := 118140960795 + 3792291 * 2 ^ 59
def prefixEnd_3792291 : Nat := 4983230072969 + 3 ^ 40 * 3792291 * 2
def baseEnd_3792291 : Nat := 1947268064719727377722077

theorem tailTrace_3792291 : CollatzResearch.WordTrace tailWord_3792291 prefixEnd_3792291 1947268064719727377722077 := by
  unfold tailWord_3792291
  simp only [CollatzResearch.WordTrace]
  refine ⟨138316215904184853584128727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92210810602789902389419151 138316215904184853584128727)
  ·
    refine ⟨207474323856277280376193091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138316215904184853584128727 207474323856277280376193091)
    ·
      refine ⟨311211485784415920564289637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207474323856277280376193091 311211485784415920564289637)
      ·
        refine ⟨58352153584577985105804307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311211485784415920564289637 58352153584577985105804307)
        ·
          refine ⟨87528230376866977658706461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58352153584577985105804307 87528230376866977658706461)
          ·
            refine ⟨32823086391325116622014923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87528230376866977658706461 32823086391325116622014923)
            ·
              refine ⟨49234629586987674933022385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32823086391325116622014923 49234629586987674933022385)
              ·
                refine ⟨36925972190240756199766789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49234629586987674933022385 36925972190240756199766789)
                ·
                  refine ⟨6923619785670141787456273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36925972190240756199766789 6923619785670141787456273)
                  ·
                    refine ⟨5192714839252606340592205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6923619785670141787456273 5192714839252606340592205)
                    ·
                      refine ⟨1947268064719727377722077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5192714839252606340592205 1947268064719727377722077)
                      ·
                        rfl

theorem cell23_3792291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_3792291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792291 prefixEnd_3792291 := by exact prefixLift 3792291
  have htrace : WordTrace (prefixWord ++ tailWord_3792291) baseStart_3792291 baseEnd_3792291 := by
    simpa [prefixWord, tailWord_3792291, baseEnd_3792291] using wordTrace_append hprefix tailTrace_3792291
  have hstable : (prefixWord ++ tailWord_3792291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792291).length < 2 ^ (prefixWord ++ tailWord_3792291).sum := by decide
  have hdescent : baseEnd_3792291 < baseStart_3792291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792314 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_3792314 : Nat := 118140960795 + 3792314 * 2 ^ 59
def prefixEnd_3792314 : Nat := 4983230072969 + 3 ^ 40 * 3792314 * 2
def baseEnd_3792314 : Nat := 1947279874774780787734471

theorem tailTrace_3792314 : CollatzResearch.WordTrace tailWord_3792314 prefixEnd_3792314 1947279874774780787734471 := by
  unfold tailWord_3792314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34579263695775382128053999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92211369855401019008143997 34579263695775382128053999)
  ·
    refine ⟨51868895543663073192080999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34579263695775382128053999 51868895543663073192080999)
    ·
      refine ⟨77803343315494609788121499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51868895543663073192080999 77803343315494609788121499)
      ·
        refine ⟨116705014973241914682182249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77803343315494609788121499 116705014973241914682182249)
        ·
          refine ⟨87528761229931436011636687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116705014973241914682182249 87528761229931436011636687)
          ·
            refine ⟨131293141844897154017455031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87528761229931436011636687 131293141844897154017455031)
            ·
              refine ⟨196939712767345731026182547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131293141844897154017455031 196939712767345731026182547)
              ·
                refine ⟨295409569151018596539273821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196939712767345731026182547 295409569151018596539273821)
                ·
                  refine ⟨110778588431631973702227683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295409569151018596539273821 110778588431631973702227683)
                  ·
                    refine ⟨166167882647447960553341525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110778588431631973702227683 166167882647447960553341525)
                    ·
                      refine ⟨1947279874774780787734471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 166167882647447960553341525 1947279874774780787734471)
                      ·
                        rfl

theorem cell23_3792314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_3792314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792314 prefixEnd_3792314 := by exact prefixLift 3792314
  have htrace : WordTrace (prefixWord ++ tailWord_3792314) baseStart_3792314 baseEnd_3792314 := by
    simpa [prefixWord, tailWord_3792314, baseEnd_3792314] using wordTrace_append hprefix tailTrace_3792314
  have hstable : (prefixWord ++ tailWord_3792314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792314).length < 2 ^ (prefixWord ++ tailWord_3792314).sum := by decide
  have hdescent : baseEnd_3792314 < baseStart_3792314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792332 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_3792332 : Nat := 118140960795 + 3792332 * 2 ^ 59
def prefixEnd_3792332 : Nat := 4983230072969 + 3 ^ 40 * 3792332 * 2
def baseEnd_3792332 : Nat := 649096372475520572436463

theorem tailTrace_3792332 : CollatzResearch.WordTrace tailWord_3792332 prefixEnd_3792332 649096372475520572436463 := by
  unfold tailWord_3792332
  simp only [CollatzResearch.WordTrace]
  refine ⟨69158855648518158793185625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92211807531357545057580833 69158855648518158793185625)
  ·
    refine ⟨51869141736388619094889219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69158855648518158793185625 51869141736388619094889219)
    ·
      refine ⟨77803712604582928642333829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51869141736388619094889219 77803712604582928642333829)
      ·
        refine ⟨14588196113359299120437593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77803712604582928642333829 14588196113359299120437593)
        ·
          refine ⟨10941147085019474340328195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14588196113359299120437593 10941147085019474340328195)
          ·
            refine ⟨16411720627529211510492293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941147085019474340328195 16411720627529211510492293)
            ·
              refine ⟨3077197617661727158217305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16411720627529211510492293 3077197617661727158217305)
              ·
                refine ⟨2307898213246295368662979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077197617661727158217305 2307898213246295368662979)
                ·
                  refine ⟨3461847319869443052994469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307898213246295368662979 3461847319869443052994469)
                  ·
                    refine ⟨649096372475520572436463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3461847319869443052994469 649096372475520572436463)
                    ·
                      rfl

theorem cell23_3792332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_3792332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792332 prefixEnd_3792332 := by exact prefixLift 3792332
  have htrace : WordTrace (prefixWord ++ tailWord_3792332) baseStart_3792332 baseEnd_3792332 := by
    simpa [prefixWord, tailWord_3792332, baseEnd_3792332] using wordTrace_append hprefix tailTrace_3792332
  have hstable : (prefixWord ++ tailWord_3792332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792332).length < 2 ^ (prefixWord ++ tailWord_3792332).sum := by decide
  have hdescent : baseEnd_3792332 < baseStart_3792332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792341 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3792341 : Nat := 118140960795 + 3792341 * 2 ^ 59
def prefixEnd_3792341 : Nat := 4983230072969 + 3 ^ 40 * 3792341 * 2
def baseEnd_3792341 : Nat := 649097912917484060698949

theorem tailTrace_3792341 : CollatzResearch.WordTrace tailWord_3792341 prefixEnd_3792341 649097912917484060698949 := by
  unfold tailWord_3792341
  simp only [CollatzResearch.WordTrace]
  refine ⟨138318039554003712123448877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92212026369335808082299251 138318039554003712123448877)
  ·
    refine ⟨51869264832751392046293329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138318039554003712123448877 51869264832751392046293329)
    ·
      refine ⟨38901948624563544034719997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51869264832751392046293329 38901948624563544034719997)
      ·
        refine ⟨14588230734211329013019999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38901948624563544034719997 14588230734211329013019999)
        ·
          refine ⟨21882346101316993519529999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588230734211329013019999 21882346101316993519529999)
          ·
            refine ⟨32823519151975490279294999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21882346101316993519529999 32823519151975490279294999)
            ·
              refine ⟨49235278727963235418942499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32823519151975490279294999 49235278727963235418942499)
              ·
                refine ⟨73852918091944853128413749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49235278727963235418942499 73852918091944853128413749)
                ·
                  refine ⟨6923711071119829980788789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73852918091944853128413749 6923711071119829980788789)
                  ·
                    refine ⟨649097912917484060698949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6923711071119829980788789 649097912917484060698949)
                    ·
                      rfl

theorem cell23_3792341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3792341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792341 prefixEnd_3792341 := by exact prefixLift 3792341
  have htrace : WordTrace (prefixWord ++ tailWord_3792341) baseStart_3792341 baseEnd_3792341 := by
    simpa [prefixWord, tailWord_3792341, baseEnd_3792341] using wordTrace_append hprefix tailTrace_3792341
  have hstable : (prefixWord ++ tailWord_3792341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792341).length < 2 ^ (prefixWord ++ tailWord_3792341).sum := by decide
  have hdescent : baseEnd_3792341 < baseStart_3792341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792355 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3792355 : Nat := 118140960795 + 3792355 * 2 ^ 59
def prefixEnd_3792355 : Nat := 4983230072969 + 3 ^ 40 * 3792355 * 2
def baseEnd_3792355 : Nat := 1947300927481615127321783

theorem tailTrace_3792355 : CollatzResearch.WordTrace tailWord_3792355 prefixEnd_3792355 1947300927481615127321783 := by
  unfold tailWord_3792355
  simp only [CollatzResearch.WordTrace]
  refine ⟨138318550175952992514458519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92212366783968661676305679 138318550175952992514458519)
  ·
    refine ⟨207477825263929488771687779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138318550175952992514458519 207477825263929488771687779)
    ·
      refine ⟨311216737895894233157531669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207477825263929488771687779 311216737895894233157531669)
      ·
        refine ⟨14588284588870042179259297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 311216737895894233157531669 14588284588870042179259297)
        ·
          refine ⟨10941213441652531634444473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14588284588870042179259297 10941213441652531634444473)
          ·
            refine ⟨8205910081239398725833355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10941213441652531634444473 8205910081239398725833355)
            ·
              refine ⟨12308865121859098088750033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8205910081239398725833355 12308865121859098088750033)
              ·
                refine ⟨9231648841394323566562525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12308865121859098088750033 9231648841394323566562525)
                ·
                  refine ⟨3461868315522871337460947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9231648841394323566562525 3461868315522871337460947)
                  ·
                    refine ⟨5192802473284307006191421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3461868315522871337460947 5192802473284307006191421)
                    ·
                      refine ⟨1947300927481615127321783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5192802473284307006191421 1947300927481615127321783)
                      ·
                        rfl

theorem cell23_3792355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3792355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792355 prefixEnd_3792355 := by exact prefixLift 3792355
  have htrace : WordTrace (prefixWord ++ tailWord_3792355) baseStart_3792355 baseEnd_3792355 := by
    simpa [prefixWord, tailWord_3792355, baseEnd_3792355] using wordTrace_append hprefix tailTrace_3792355
  have hstable : (prefixWord ++ tailWord_3792355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792355).length < 2 ^ (prefixWord ++ tailWord_3792355).sum := by decide
  have hdescent : baseEnd_3792355 < baseStart_3792355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792378 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_3792378 : Nat := 118140960795 + 3792378 * 2 ^ 59
def prefixEnd_3792378 : Nat := 4983230072969 + 3 ^ 40 * 3792378 * 2
def baseEnd_3792378 : Nat := 1947312737536668537334177

theorem tailTrace_3792378 : CollatzResearch.WordTrace tailWord_3792378 prefixEnd_3792378 1947312737536668537334177 := by
  unfold tailWord_3792378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34579847263717416860636447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92212926036579778295030525 34579847263717416860636447)
  ·
    refine ⟨51869770895576125290954671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34579847263717416860636447 51869770895576125290954671)
    ·
      refine ⟨77804656343364187936432007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51869770895576125290954671 77804656343364187936432007)
      ·
        refine ⟨116706984515046281904648011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77804656343364187936432007 116706984515046281904648011)
        ·
          refine ⟨175060476772569422856972017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116706984515046281904648011 175060476772569422856972017)
          ·
            refine ⟨131295357579427067142729013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175060476772569422856972017 131295357579427067142729013)
            ·
              refine ⟨12308939773071287544630845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131295357579427067142729013 12308939773071287544630845)
              ·
                refine ⟨4615852414901732829236567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12308939773071287544630845 4615852414901732829236567)
                ·
                  refine ⟨6923778622352599243854851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615852414901732829236567 6923778622352599243854851)
                  ·
                    refine ⟨10385667933528898865782277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923778622352599243854851 10385667933528898865782277)
                    ·
                      refine ⟨1947312737536668537334177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10385667933528898865782277 1947312737536668537334177)
                      ·
                        rfl

theorem cell23_3792378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_3792378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792378 prefixEnd_3792378 := by exact prefixLift 3792378
  have htrace : WordTrace (prefixWord ++ tailWord_3792378) baseStart_3792378 baseEnd_3792378 := by
    simpa [prefixWord, tailWord_3792378, baseEnd_3792378] using wordTrace_append hprefix tailTrace_3792378
  have hstable : (prefixWord ++ tailWord_3792378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792378).length < 2 ^ (prefixWord ++ tailWord_3792378).sum := by decide
  have hdescent : baseEnd_3792378 < baseStart_3792378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792408 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3792408 : Nat := 118140960795 + 3792408 * 2 ^ 59
def prefixEnd_3792408 : Nat := 4983230072969 + 3 ^ 40 * 3792408 * 2
def baseEnd_3792408 : Nat := 1947328141956303419959039

theorem tailTrace_3792408 : CollatzResearch.WordTrace tailWord_3792408 prefixEnd_3792408 1947328141956303419959039 := by
  unfold tailWord_3792408
  simp only [CollatzResearch.WordTrace]
  refine ⟨69160241622380491283068939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92213655496507321710758585 69160241622380491283068939)
  ·
    refine ⟨103740362433570736924603409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69160241622380491283068939 103740362433570736924603409)
    ·
      refine ⟨77805271825178052693452557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103740362433570736924603409 77805271825178052693452557)
      ·
        refine ⟨29176976934441769760044709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77805271825178052693452557 29176976934441769760044709)
        ·
          refine ⟨5470683175207831830008383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29176976934441769760044709 5470683175207831830008383)
          ·
            refine ⟨8206024762811747745012575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470683175207831830008383 8206024762811747745012575)
            ·
              refine ⟨12309037144217621617518863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206024762811747745012575 12309037144217621617518863)
              ·
                refine ⟨18463555716326432426278295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12309037144217621617518863 18463555716326432426278295)
                ·
                  refine ⟨27695333574489648639417443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18463555716326432426278295 27695333574489648639417443)
                  ·
                    refine ⟨41543000361734472959126165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27695333574489648639417443 41543000361734472959126165)
                    ·
                      refine ⟨1947328141956303419959039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41543000361734472959126165 1947328141956303419959039)
                      ·
                        rfl

theorem cell23_3792408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3792408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792408 prefixEnd_3792408 := by exact prefixLift 3792408
  have htrace : WordTrace (prefixWord ++ tailWord_3792408) baseStart_3792408 baseEnd_3792408 := by
    simpa [prefixWord, tailWord_3792408, baseEnd_3792408] using wordTrace_append hprefix tailTrace_3792408
  have hstable : (prefixWord ++ tailWord_3792408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792408).length < 2 ^ (prefixWord ++ tailWord_3792408).sum := by decide
  have hdescent : baseEnd_3792408 < baseStart_3792408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792418 : List Nat := [3, 3, 1, 1, 1, 1, 6, 7]
def baseStart_3792418 : Nat := 118140960795 + 3792418 * 2 ^ 59
def prefixEnd_3792418 : Nat := 4983230072969 + 3 ^ 40 * 3792418 * 2
def baseEnd_3792418 : Nat := 72123454694920310401259

theorem tailTrace_3792418 : CollatzResearch.WordTrace tailWord_3792418 prefixEnd_3792418 72123454694920310401259 := by
  unfold tailWord_3792418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34580211993681188568500477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92213898649816502849334605 34580211993681188568500477)
  ·
    refine ⟨12967579497630445713187679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34580211993681188568500477 12967579497630445713187679)
    ·
      refine ⟨19451369246445668569781519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12967579497630445713187679 19451369246445668569781519)
      ·
        refine ⟨29177053869668502854672279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19451369246445668569781519 29177053869668502854672279)
        ·
          refine ⟨43765580804502754282008419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29177053869668502854672279 43765580804502754282008419)
          ·
            refine ⟨65648371206754131423012629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43765580804502754282008419 65648371206754131423012629)
            ·
              refine ⟨3077267400316599910453717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65648371206754131423012629 3077267400316599910453717)
              ·
                refine ⟨72123454694920310401259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3077267400316599910453717 72123454694920310401259)
                ·
                  rfl

theorem cell23_3792418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_3792418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792418 prefixEnd_3792418 := by exact prefixLift 3792418
  have htrace : WordTrace (prefixWord ++ tailWord_3792418) baseStart_3792418 baseEnd_3792418 := by
    simpa [prefixWord, tailWord_3792418, baseEnd_3792418] using wordTrace_append hprefix tailTrace_3792418
  have hstable : (prefixWord ++ tailWord_3792418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792418).length < 2 ^ (prefixWord ++ tailWord_3792418).sum := by decide
  have hdescent : baseEnd_3792418 < baseStart_3792418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792485 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 3, 4, 2]
def baseStart_3792485 : Nat := 118140960795 + 3792485 * 2 ^ 59
def prefixEnd_3792485 : Nat := 4983230072969 + 3 ^ 40 * 3792485 * 2
def baseEnd_3792485 : Nat := 1947367679966699618696185

theorem tailTrace_3792485 : CollatzResearch.WordTrace tailWord_3792485 prefixEnd_3792485 1947367679966699618696185 := by
  unfold tailWord_3792485
  simp only [CollatzResearch.WordTrace]
  refine ⟨138323291665482024716690909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92215527776988016477793939 138323291665482024716690909)
  ·
    refine ⟨51871234374555759268759091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138323291665482024716690909 51871234374555759268759091)
    ·
      refine ⟨77806851561833638903138637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51871234374555759268759091 77806851561833638903138637)
      ·
        refine ⟨29177569335687614588676989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77806851561833638903138637 29177569335687614588676989)
        ·
          refine ⟨10941588500882855470753871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29177569335687614588676989 10941588500882855470753871)
          ·
            refine ⟨16412382751324283206130807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941588500882855470753871 16412382751324283206130807)
            ·
              refine ⟨24618574126986424809196211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16412382751324283206130807 24618574126986424809196211)
              ·
                refine ⟨36927861190479637213794317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24618574126986424809196211 36927861190479637213794317)
                ·
                  refine ⟨13847947946429863955172869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36927861190479637213794317 13847947946429863955172869)
                  ·
                    refine ⟨2596490239955599491594913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13847947946429863955172869 2596490239955599491594913)
                    ·
                      refine ⟨1947367679966699618696185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596490239955599491594913 1947367679966699618696185)
                      ·
                        rfl

theorem cell23_3792485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_3792485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792485 prefixEnd_3792485 := by exact prefixLift 3792485
  have htrace : WordTrace (prefixWord ++ tailWord_3792485) baseStart_3792485 baseEnd_3792485 := by
    simpa [prefixWord, tailWord_3792485, baseEnd_3792485] using wordTrace_append hprefix tailTrace_3792485
  have hstable : (prefixWord ++ tailWord_3792485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792485).length < 2 ^ (prefixWord ++ tailWord_3792485).sum := by decide
  have hdescent : baseEnd_3792485 < baseStart_3792485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792542 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3792542 : Nat := 118140960795 + 3792542 * 2 ^ 59
def prefixEnd_3792542 : Nat := 4983230072969 + 3 ^ 40 * 3792542 * 2
def baseEnd_3792542 : Nat := 216377438707111766187047

theorem tailTrace_3792542 : CollatzResearch.WordTrace tailWord_3792542 prefixEnd_3792542 216377438707111766187047 := by
  unfold tailWord_3792542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290671328284440431439485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92216913750850348967677253 17290671328284440431439485)
  ·
    refine ⟨6484001748106665161789807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17290671328284440431439485 6484001748106665161789807)
    ·
      refine ⟨9726002622159997742684711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484001748106665161789807 9726002622159997742684711)
      ·
        refine ⟨14589003933239996614027067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726002622159997742684711 14589003933239996614027067)
        ·
          refine ⟨21883505899859994921040601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14589003933239996614027067 21883505899859994921040601)
          ·
            refine ⟨16412629424894996190780451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21883505899859994921040601 16412629424894996190780451)
            ·
              refine ⟨24618944137342494286170677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16412629424894996190780451 24618944137342494286170677)
              ·
                refine ⟨2308026012875858839328501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24618944137342494286170677 2308026012875858839328501)
                ·
                  refine ⟨216377438707111766187047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308026012875858839328501 216377438707111766187047)
                  ·
                    rfl

theorem cell23_3792542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3792542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792542 prefixEnd_3792542 := by exact prefixLift 3792542
  have htrace : WordTrace (prefixWord ++ tailWord_3792542) baseStart_3792542 baseEnd_3792542 := by
    simpa [prefixWord, tailWord_3792542, baseEnd_3792542] using wordTrace_append hprefix tailTrace_3792542
  have hstable : (prefixWord ++ tailWord_3792542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792542).length < 2 ^ (prefixWord ++ tailWord_3792542).sum := by decide
  have hdescent : baseEnd_3792542 < baseStart_3792542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792575 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 2, 4, 2]
def baseStart_3792575 : Nat := 118140960795 + 3792575 * 2 ^ 59
def prefixEnd_3792575 : Nat := 4983230072969 + 3 ^ 40 * 3792575 * 2
def baseEnd_3792575 : Nat := 1947413893225604266570771

theorem tailTrace_3792575 : CollatzResearch.WordTrace tailWord_3792575 prefixEnd_3792575 1947413893225604266570771 := by
  unfold tailWord_3792575
  simp only [CollatzResearch.WordTrace]
  refine ⟨138326574235155970087467179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92217716156770646724978119 138326574235155970087467179)
  ·
    refine ⟨207489861352733955131200769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138326574235155970087467179 207489861352733955131200769)
    ·
      refine ⟨155617396014550466348400577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207489861352733955131200769 155617396014550466348400577)
      ·
        refine ⟨116713047010912849761300433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155617396014550466348400577 116713047010912849761300433)
        ·
          refine ⟨87534785258184637320975325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116713047010912849761300433 87534785258184637320975325)
          ·
            refine ⟨32825544471819238995365747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87534785258184637320975325 32825544471819238995365747)
            ·
              refine ⟨49238316707728858493048621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32825544471819238995365747 49238316707728858493048621)
              ·
                refine ⟨18464368765398321934893233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49238316707728858493048621 18464368765398321934893233)
                ·
                  refine ⟨13848276574048741451169925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18464368765398321934893233 13848276574048741451169925)
                  ·
                    refine ⟨2596551857634139022094361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13848276574048741451169925 2596551857634139022094361)
                    ·
                      refine ⟨1947413893225604266570771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596551857634139022094361 1947413893225604266570771)
                      ·
                        rfl

theorem cell23_3792575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_3792575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792575 prefixEnd_3792575 := by exact prefixLift 3792575
  have htrace : WordTrace (prefixWord ++ tailWord_3792575) baseStart_3792575 baseEnd_3792575 := by
    simpa [prefixWord, tailWord_3792575, baseEnd_3792575] using wordTrace_append hprefix tailTrace_3792575
  have hstable : (prefixWord ++ tailWord_3792575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792575).length < 2 ^ (prefixWord ++ tailWord_3792575).sum := by decide
  have hdescent : baseEnd_3792575 < baseStart_3792575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792618 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3792618 : Nat := 118140960795 + 3792618 * 2 ^ 59
def prefixEnd_3792618 : Nat := 4983230072969 + 3 ^ 40 * 3792618 * 2
def baseEnd_3792618 : Nat := 1947435972893747598333073

theorem tailTrace_3792618 : CollatzResearch.WordTrace tailWord_3792618 prefixEnd_3792618 1947435972893747598333073 := by
  unfold tailWord_3792618
  simp only [CollatzResearch.WordTrace]
  refine ⟨34582035643500047107820627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92218761716000125620855005 34582035643500047107820627)
  ·
    refine ⟨51873053465250070661730941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34582035643500047107820627 51873053465250070661730941)
    ·
      refine ⟨19452395049468776498149103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51873053465250070661730941 19452395049468776498149103)
      ·
        refine ⟨29178592574203164747223655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19452395049468776498149103 29178592574203164747223655)
        ·
          refine ⟨43767888861304747120835483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29178592574203164747223655 43767888861304747120835483)
          ·
            refine ⟨65651833291957120681253225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43767888861304747120835483 65651833291957120681253225)
            ·
              refine ⟨49238874968967840510939919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65651833291957120681253225 49238874968967840510939919)
              ·
                refine ⟨73858312453451760766409879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49238874968967840510939919 73858312453451760766409879)
                ·
                  refine ⟨110787468680177641149614819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73858312453451760766409879 110787468680177641149614819)
                  ·
                    refine ⟨166181203020266461724422229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110787468680177641149614819 166181203020266461724422229)
                    ·
                      refine ⟨1947435972893747598333073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 166181203020266461724422229 1947435972893747598333073)
                      ·
                        rfl

theorem cell23_3792618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3792618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792618 prefixEnd_3792618 := by exact prefixLift 3792618
  have htrace : WordTrace (prefixWord ++ tailWord_3792618) baseStart_3792618 baseEnd_3792618 := by
    simpa [prefixWord, tailWord_3792618, baseEnd_3792618] using wordTrace_append hprefix tailTrace_3792618
  have hstable : (prefixWord ++ tailWord_3792618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792618).length < 2 ^ (prefixWord ++ tailWord_3792618).sum := by decide
  have hdescent : baseEnd_3792618 < baseStart_3792618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792635 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 1, 5, 2]
def baseStart_3792635 : Nat := 118140960795 + 3792635 * 2 ^ 59
def prefixEnd_3792635 : Nat := 4983230072969 + 3 ^ 40 * 3792635 * 2
def baseEnd_3792635 : Nat := 1947444702064874031820495

theorem tailTrace_3792635 : CollatzResearch.WordTrace tailWord_3792635 prefixEnd_3792635 1947444702064874031820495 := by
  unfold tailWord_3792635
  simp only [CollatzResearch.WordTrace]
  refine ⟨138328762614938600334651359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92219175076625733556434239 138328762614938600334651359)
  ·
    refine ⟨207493143922407900501977039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138328762614938600334651359 207493143922407900501977039)
    ·
      refine ⟨311239715883611850752965559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207493143922407900501977039 311239715883611850752965559)
      ·
        refine ⟨466859573825417776129448339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311239715883611850752965559 466859573825417776129448339)
        ·
          refine ⟨700289360738126664194172509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466859573825417776129448339 700289360738126664194172509)
          ·
            refine ⟨262608510276797499072814691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 700289360738126664194172509 262608510276797499072814691)
            ·
              refine ⟨393912765415196248609222037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262608510276797499072814691 393912765415196248609222037)
              ·
                refine ⟨18464660878837324153557283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 393912765415196248609222037 18464660878837324153557283)
                ·
                  refine ⟨27696991318255986230335925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18464660878837324153557283 27696991318255986230335925)
                  ·
                    refine ⟨2596592936086498709093993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27696991318255986230335925 2596592936086498709093993)
                    ·
                      refine ⟨1947444702064874031820495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596592936086498709093993 1947444702064874031820495)
                      ·
                        rfl

theorem cell23_3792635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5, 2].length) (baseStart_3792635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792635 prefixEnd_3792635 := by exact prefixLift 3792635
  have htrace : WordTrace (prefixWord ++ tailWord_3792635) baseStart_3792635 baseEnd_3792635 := by
    simpa [prefixWord, tailWord_3792635, baseEnd_3792635] using wordTrace_append hprefix tailTrace_3792635
  have hstable : (prefixWord ++ tailWord_3792635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792635).length < 2 ^ (prefixWord ++ tailWord_3792635).sum := by decide
  have hdescent : baseEnd_3792635 < baseStart_3792635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792652 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 2, 3, 2]
def baseStart_3792652 : Nat := 118140960795 + 3792652 * 2 ^ 59
def prefixEnd_3792652 : Nat := 4983230072969 + 3 ^ 40 * 3792652 * 2
def baseEnd_3792652 : Nat := 1947453431236000465307917

theorem tailTrace_3792652 : CollatzResearch.WordTrace tailWord_3792652 prefixEnd_3792652 1947453431236000465307917 := by
  unfold tailWord_3792652
  simp only [CollatzResearch.WordTrace]
  refine ⟨69164691327938506119010105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92219588437251341492013473 69164691327938506119010105)
  ·
    refine ⟨51873518495953879589257579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69164691327938506119010105 51873518495953879589257579)
    ·
      refine ⟨77810277743930819383886369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51873518495953879589257579 77810277743930819383886369)
      ·
        refine ⟨58357708307948114537914777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77810277743930819383886369 58357708307948114537914777)
        ·
          refine ⟨43768281230961085903436083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58357708307948114537914777 43768281230961085903436083)
          ·
            refine ⟨65652421846441628855154125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43768281230961085903436083 65652421846441628855154125)
            ·
              refine ⟨24619658192415610820682797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65652421846441628855154125 24619658192415610820682797)
              ·
                refine ⟨9232371822155854057756049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24619658192415610820682797 9232371822155854057756049)
                ·
                  refine ⟨6924278866616890543317037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9232371822155854057756049 6924278866616890543317037)
                  ·
                    refine ⟨2596604574981333953743889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6924278866616890543317037 2596604574981333953743889)
                    ·
                      refine ⟨1947453431236000465307917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596604574981333953743889 1947453431236000465307917)
                      ·
                        rfl

theorem cell23_3792652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_3792652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792652 prefixEnd_3792652 := by exact prefixLift 3792652
  have htrace : WordTrace (prefixWord ++ tailWord_3792652) baseStart_3792652 baseEnd_3792652 := by
    simpa [prefixWord, tailWord_3792652, baseEnd_3792652] using wordTrace_append hprefix tailTrace_3792652
  have hstable : (prefixWord ++ tailWord_3792652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792652).length < 2 ^ (prefixWord ++ tailWord_3792652).sum := by decide
  have hdescent : baseEnd_3792652 < baseStart_3792652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792665 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 6, 2]
def baseStart_3792665 : Nat := 118140960795 + 3792665 * 2 ^ 59
def prefixEnd_3792665 : Nat := 4983230072969 + 3 ^ 40 * 3792665 * 2
def baseEnd_3792665 : Nat := 1947460106484508914445357

theorem tailTrace_3792665 : CollatzResearch.WordTrace tailWord_3792665 prefixEnd_3792665 1947460106484508914445357 := by
  unfold tailWord_3792665
  simp only [CollatzResearch.WordTrace]
  refine ⟨138329856804829915458243449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92219904536553276972162299 138329856804829915458243449)
  ·
    refine ⟨103747392603622436593682587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138329856804829915458243449 103747392603622436593682587)
    ·
      refine ⟨155621088905433654890523881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103747392603622436593682587 155621088905433654890523881)
      ·
        refine ⟨116715816679075241167892911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155621088905433654890523881 116715816679075241167892911)
        ·
          refine ⟨175073725018612861751839367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116715816679075241167892911 175073725018612861751839367)
          ·
            refine ⟨262610587527919292627759051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175073725018612861751839367 262610587527919292627759051)
            ·
              refine ⟨393915881291878938941638577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262610587527919292627759051 393915881291878938941638577)
              ·
                refine ⟨295436910968909204206228933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393915881291878938941638577 295436910968909204206228933)
                ·
                  refine ⟨55394420806670475788667925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295436910968909204206228933 55394420806670475788667925)
                  ·
                    refine ⟨2596613475312678552593809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55394420806670475788667925 2596613475312678552593809)
                    ·
                      refine ⟨1947460106484508914445357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596613475312678552593809 1947460106484508914445357)
                      ·
                        rfl

theorem cell23_3792665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_3792665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792665 prefixEnd_3792665 := by exact prefixLift 3792665
  have htrace : WordTrace (prefixWord ++ tailWord_3792665) baseStart_3792665 baseEnd_3792665 := by
    simpa [prefixWord, tailWord_3792665, baseEnd_3792665] using wordTrace_append hprefix tailTrace_3792665
  have hstable : (prefixWord ++ tailWord_3792665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792665).length < 2 ^ (prefixWord ++ tailWord_3792665).sum := by decide
  have hdescent : baseEnd_3792665 < baseStart_3792665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792675 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 4, 4]
def baseStart_3792675 : Nat := 118140960795 + 3792675 * 2 ^ 59
def prefixEnd_3792675 : Nat := 4983230072969 + 3 ^ 40 * 3792675 * 2
def baseEnd_3792675 : Nat := 649155080430351291773437

theorem tailTrace_3792675 : CollatzResearch.WordTrace tailWord_3792675 prefixEnd_3792675 649155080430351291773437 := by
  unfold tailWord_3792675
  simp only [CollatzResearch.WordTrace]
  refine ⟨138330221534793687166107479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92220147689862458110738319 138330221534793687166107479)
  ·
    refine ⟨207495332302190530749161219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138330221534793687166107479 207495332302190530749161219)
    ·
      refine ⟨311242998453285796123741829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207495332302190530749161219 311242998453285796123741829)
      ·
        refine ⟨58358062209991086773201593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311242998453285796123741829 58358062209991086773201593)
        ·
          refine ⟨43768546657493315079901195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58358062209991086773201593 43768546657493315079901195)
          ·
            refine ⟨65652819986239972619851793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43768546657493315079901195 65652819986239972619851793)
            ·
              refine ⟨49239614989679979464888845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65652819986239972619851793 49239614989679979464888845)
              ·
                refine ⟨18464855621129992299333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49239614989679979464888845 18464855621129992299333317)
                ·
                  refine ⟨3462160428961873556124997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18464855621129992299333317 3462160428961873556124997)
                  ·
                    refine ⟨649155080430351291773437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3462160428961873556124997 649155080430351291773437)
                    ·
                      rfl

theorem cell23_3792675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 4].length) (baseStart_3792675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792675 prefixEnd_3792675 := by exact prefixLift 3792675
  have htrace : WordTrace (prefixWord ++ tailWord_3792675) baseStart_3792675 baseEnd_3792675 := by
    simpa [prefixWord, tailWord_3792675, baseEnd_3792675] using wordTrace_append hprefix tailTrace_3792675
  have hstable : (prefixWord ++ tailWord_3792675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792675).length < 2 ^ (prefixWord ++ tailWord_3792675).sum := by decide
  have hdescent : baseEnd_3792675 < baseStart_3792675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792676 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_3792676 : Nat := 118140960795 + 3792676 * 2 ^ 59
def prefixEnd_3792676 : Nat := 4983230072969 + 3 ^ 40 * 3792676 * 2
def baseEnd_3792676 : Nat := 1947465754771708371407807

theorem tailTrace_3792676 : CollatzResearch.WordTrace tailWord_3792676 prefixEnd_3792676 1947465754771708371407807 := by
  unfold tailWord_3792676
  simp only [CollatzResearch.WordTrace]
  refine ⟨69165129003895032168446941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92220172005193376224595921 69165129003895032168446941)
  ·
    refine ⟨25936923376460637063167603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69165129003895032168446941 25936923376460637063167603)
    ·
      refine ⟨38905385064690955594751405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25936923376460637063167603 38905385064690955594751405)
      ·
        refine ⟨14589519399259108348031777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38905385064690955594751405 14589519399259108348031777)
        ·
          refine ⟨10942139549444331261023833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14589519399259108348031777 10942139549444331261023833)
          ·
            refine ⟨8206604662083248445767875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10942139549444331261023833 8206604662083248445767875)
            ·
              refine ⟨12309906993124872668651813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206604662083248445767875 12309906993124872668651813)
              ·
                refine ⟨2308107561210913625372215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12309906993124872668651813 2308107561210913625372215)
                ·
                  refine ⟨3462161341816370438058323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308107561210913625372215 3462161341816370438058323)
                  ·
                    refine ⟨5193242012724555657087485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462161341816370438058323 5193242012724555657087485)
                    ·
                      refine ⟨1947465754771708371407807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5193242012724555657087485 1947465754771708371407807)
                      ·
                        rfl

theorem cell23_3792676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_3792676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792676 prefixEnd_3792676 := by exact prefixLift 3792676
  have htrace : WordTrace (prefixWord ++ tailWord_3792676) baseStart_3792676 baseEnd_3792676 := by
    simpa [prefixWord, tailWord_3792676, baseEnd_3792676] using wordTrace_append hprefix tailTrace_3792676
  have hstable : (prefixWord ++ tailWord_3792676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792676).length < 2 ^ (prefixWord ++ tailWord_3792676).sum := by decide
  have hdescent : baseEnd_3792676 < baseStart_3792676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792692 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3792692 : Nat := 118140960795 + 3792692 * 2 ^ 59
def prefixEnd_3792692 : Nat := 4983230072969 + 3 ^ 40 * 3792692 * 2
def baseEnd_3792692 : Nat := 649157990154060102935911

theorem tailTrace_3792692 : CollatzResearch.WordTrace tailWord_3792692 prefixEnd_3792692 649157990154060102935911 := by
  unfold tailWord_3792692
  simp only [CollatzResearch.WordTrace]
  refine ⟨69165420787866049534738165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92220561050488066046317553 69165420787866049534738165)
  ·
    refine ⟨6484258198862442143881703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69165420787866049534738165 6484258198862442143881703)
    ·
      refine ⟨9726387298293663215822555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484258198862442143881703 9726387298293663215822555)
      ·
        refine ⟨14589580947440494823733833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726387298293663215822555 14589580947440494823733833)
        ·
          refine ⟨10942185710580371117800375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14589580947440494823733833 10942185710580371117800375)
          ·
            refine ⟨16413278565870556676700563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10942185710580371117800375 16413278565870556676700563)
            ·
              refine ⟨24619917848805835015050845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16413278565870556676700563 24619917848805835015050845)
              ·
                refine ⟨9232469193302188130644067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24619917848805835015050845 9232469193302188130644067)
                ·
                  refine ⟨13848703789953282195966101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9232469193302188130644067 13848703789953282195966101)
                  ·
                    refine ⟨649157990154060102935911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13848703789953282195966101 649157990154060102935911)
                    ·
                      rfl

theorem cell23_3792692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3792692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792692 prefixEnd_3792692 := by exact prefixLift 3792692
  have htrace : WordTrace (prefixWord ++ tailWord_3792692) baseStart_3792692 baseEnd_3792692 := by
    simpa [prefixWord, tailWord_3792692, baseEnd_3792692] using wordTrace_append hprefix tailTrace_3792692
  have hstable : (prefixWord ++ tailWord_3792692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792692).length < 2 ^ (prefixWord ++ tailWord_3792692).sum := by decide
  have hdescent : baseEnd_3792692 < baseStart_3792692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792710 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3792710 : Nat := 118140960795 + 3792710 * 2 ^ 59
def prefixEnd_3792710 : Nat := 4983230072969 + 3 ^ 40 * 3792710 * 2
def baseEnd_3792710 : Nat := 1947483213113961238382651

theorem tailTrace_3792710 : CollatzResearch.WordTrace tailWord_3792710 prefixEnd_3792710 1947483213113961238382651 := by
  unfold tailWord_3792710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322859315302090254488487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92220998726444592095754389 4322859315302090254488487)
  ·
    refine ⟨6484288972953135381732731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322859315302090254488487 6484288972953135381732731)
    ·
      refine ⟨9726433459429703072599097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484288972953135381732731 9726433459429703072599097)
      ·
        refine ⟨7294825094572277304449323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9726433459429703072599097 7294825094572277304449323)
        ·
          refine ⟨10942237641858415956673985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7294825094572277304449323 10942237641858415956673985)
          ·
            refine ⟨8206678231393811967505489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10942237641858415956673985 8206678231393811967505489)
            ·
              refine ⟨6155008673545358975629117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8206678231393811967505489 6155008673545358975629117)
              ·
                refine ⟨2308128252579509615860919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6155008673545358975629117 2308128252579509615860919)
                ·
                  refine ⟨3462192378869264423791379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308128252579509615860919 3462192378869264423791379)
                  ·
                    refine ⟨5193288568303896635687069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462192378869264423791379 5193288568303896635687069)
                    ·
                      refine ⟨1947483213113961238382651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5193288568303896635687069 1947483213113961238382651)
                      ·
                        rfl

theorem cell23_3792710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3792710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792710 prefixEnd_3792710 := by exact prefixLift 3792710
  have htrace : WordTrace (prefixWord ++ tailWord_3792710) baseStart_3792710 baseEnd_3792710 := by
    simpa [prefixWord, tailWord_3792710, baseEnd_3792710] using wordTrace_append hprefix tailTrace_3792710
  have hstable : (prefixWord ++ tailWord_3792710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792710).length < 2 ^ (prefixWord ++ tailWord_3792710).sum := by decide
  have hdescent : baseEnd_3792710 < baseStart_3792710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792716 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 1, 1, 4]
def baseStart_3792716 : Nat := 118140960795 + 3792716 * 2 ^ 59
def prefixEnd_3792716 : Nat := 4983230072969 + 3 ^ 40 * 3792716 * 2
def baseEnd_3792716 : Nat := 1947486293997888214907623

theorem tailTrace_3792716 : CollatzResearch.WordTrace tailWord_3792716 prefixEnd_3792716 1947486293997888214907623 := by
  unfold tailWord_3792716
  simp only [CollatzResearch.WordTrace]
  refine ⟨69165858463822575584175001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92221144618430100778900001 69165858463822575584175001)
  ·
    refine ⟨51874393847866931688131251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69165858463822575584175001 51874393847866931688131251)
    ·
      refine ⟨77811590771800397532196877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51874393847866931688131251 77811590771800397532196877)
      ·
        refine ⟨29179346539425149074573829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77811590771800397532196877 29179346539425149074573829)
        ·
          refine ⟨5471127476142215451482593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29179346539425149074573829 5471127476142215451482593)
          ·
            refine ⟨4103345607106661588611945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5471127476142215451482593 4103345607106661588611945)
            ·
              refine ⟨3077509205329996191458959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4103345607106661588611945 3077509205329996191458959)
              ·
                refine ⟨4616263807994994287188439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077509205329996191458959 4616263807994994287188439)
                ·
                  refine ⟨6924395711992491430782659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616263807994994287188439 6924395711992491430782659)
                  ·
                    refine ⟨10386593567988737146173989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6924395711992491430782659 10386593567988737146173989)
                    ·
                      refine ⟨1947486293997888214907623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10386593567988737146173989 1947486293997888214907623)
                      ·
                        rfl

theorem cell23_3792716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_3792716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792716 prefixEnd_3792716 := by exact prefixLift 3792716
  have htrace : WordTrace (prefixWord ++ tailWord_3792716) baseStart_3792716 baseEnd_3792716 := by
    simpa [prefixWord, tailWord_3792716, baseEnd_3792716] using wordTrace_append hprefix tailTrace_3792716
  have hstable : (prefixWord ++ tailWord_3792716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792716).length < 2 ^ (prefixWord ++ tailWord_3792716).sum := by decide
  have hdescent : baseEnd_3792716 < baseStart_3792716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792746 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3792746 : Nat := 118140960795 + 3792746 * 2 ^ 59
def prefixEnd_3792746 : Nat := 4983230072969 + 3 ^ 40 * 3792746 * 2
def baseEnd_3792746 : Nat := 1947501698417523097532485

theorem tailTrace_3792746 : CollatzResearch.WordTrace tailWord_3792746 prefixEnd_3792746 1947501698417523097532485 := by
  unfold tailWord_3792746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34583202779384116572985523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92221874078357644194628061 34583202779384116572985523)
  ·
    refine ⟨51874804169076174859478285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34583202779384116572985523 51874804169076174859478285)
    ·
      refine ⟨19453051563403565572304357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51874804169076174859478285 19453051563403565572304357)
      ·
        refine ⟨3647447168138168544807067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19453051563403565572304357 3647447168138168544807067)
        ·
          refine ⟨5471170752207252817210601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647447168138168544807067 5471170752207252817210601)
          ·
            refine ⟨4103378064155439612907951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5471170752207252817210601 4103378064155439612907951)
            ·
              refine ⟨6155067096233159419361927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103378064155439612907951 6155067096233159419361927)
              ·
                refine ⟨9232600644349739129042891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155067096233159419361927 9232600644349739129042891)
                ·
                  refine ⟨13848900966524608693564337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9232600644349739129042891 13848900966524608693564337)
                  ·
                    refine ⟨10386675724893456520173253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13848900966524608693564337 10386675724893456520173253)
                    ·
                      refine ⟨1947501698417523097532485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10386675724893456520173253 1947501698417523097532485)
                      ·
                        rfl

theorem cell23_3792746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3792746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792746 prefixEnd_3792746 := by exact prefixLift 3792746
  have htrace : WordTrace (prefixWord ++ tailWord_3792746) baseStart_3792746 baseEnd_3792746 := by
    simpa [prefixWord, tailWord_3792746, baseEnd_3792746] using wordTrace_append hprefix tailTrace_3792746
  have hstable : (prefixWord ++ tailWord_3792746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792746).length < 2 ^ (prefixWord ++ tailWord_3792746).sum := by decide
  have hdescent : baseEnd_3792746 < baseStart_3792746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792749 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3792749 : Nat := 118140960795 + 3792749 * 2 ^ 59
def prefixEnd_3792749 : Nat := 4983230072969 + 3 ^ 40 * 3792749 * 2
def baseEnd_3792749 : Nat := 1947503238859486585794971

theorem tailTrace_3792749 : CollatzResearch.WordTrace tailWord_3792749 prefixEnd_3792749 1947503238859486585794971 := by
  unfold tailWord_3792749
  simp only [CollatzResearch.WordTrace]
  refine ⟨138332920536525597804301301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92221947024350398536200867 138332920536525597804301301)
  ·
    refine ⟨12968711300299274794153247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138332920536525597804301301 12968711300299274794153247)
    ·
      refine ⟨19453066950448912191229871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12968711300299274794153247 19453066950448912191229871)
      ·
        refine ⟨29179600425673368286844807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19453066950448912191229871 29179600425673368286844807)
        ·
          refine ⟨43769400638510052430267211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29179600425673368286844807 43769400638510052430267211)
          ·
            refine ⟨65654100957765078645400817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43769400638510052430267211 65654100957765078645400817)
            ·
              refine ⟨49240575718323808984050613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65654100957765078645400817 49240575718323808984050613)
              ·
                refine ⟨4616303973592857092254745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49240575718323808984050613 4616303973592857092254745)
                ·
                  refine ⟨3462227980194642819191059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4616303973592857092254745 3462227980194642819191059)
                  ·
                    refine ⟨5193341970291964228786589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462227980194642819191059 5193341970291964228786589)
                    ·
                      refine ⟨1947503238859486585794971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5193341970291964228786589 1947503238859486585794971)
                      ·
                        rfl

theorem cell23_3792749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3792749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792749 prefixEnd_3792749 := by exact prefixLift 3792749
  have htrace : WordTrace (prefixWord ++ tailWord_3792749) baseStart_3792749 baseEnd_3792749 := by
    simpa [prefixWord, tailWord_3792749, baseEnd_3792749] using wordTrace_append hprefix tailTrace_3792749
  have hstable : (prefixWord ++ tailWord_3792749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792749).length < 2 ^ (prefixWord ++ tailWord_3792749).sum := by decide
  have hdescent : baseEnd_3792749 < baseStart_3792749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792766 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3792766 : Nat := 118140960795 + 3792766 * 2 ^ 59
def prefixEnd_3792766 : Nat := 4983230072969 + 3 ^ 40 * 3792766 * 2
def baseEnd_3792766 : Nat := 1947511968030613019282393

theorem tailTrace_3792766 : CollatzResearch.WordTrace tailWord_3792766 prefixEnd_3792766 1947511968030613019282393 := by
  unfold tailWord_3792766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291692572183001213458769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92222360384976006471780101 17291692572183001213458769)
  ·
    refine ⟨12968769429137250910094077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17291692572183001213458769 12968769429137250910094077)
    ·
      refine ⟨4863288535926469091285279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12968769429137250910094077 4863288535926469091285279)
      ·
        refine ⟨7294932803889703636927919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863288535926469091285279 7294932803889703636927919)
        ·
          refine ⟨10942399205834555455391879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7294932803889703636927919 10942399205834555455391879)
          ·
            refine ⟨16413598808751833183087819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10942399205834555455391879 16413598808751833183087819)
            ·
              refine ⟨24620398213127749774631729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16413598808751833183087819 24620398213127749774631729)
              ·
                refine ⟨18465298659845812330973797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24620398213127749774631729 18465298659845812330973797)
                ·
                  refine ⟨3462243498721089812057587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18465298659845812330973797 3462243498721089812057587)
                  ·
                    refine ⟨5193365248081634718086381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462243498721089812057587 5193365248081634718086381)
                    ·
                      refine ⟨1947511968030613019282393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5193365248081634718086381 1947511968030613019282393)
                      ·
                        rfl

theorem cell23_3792766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3792766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792766 prefixEnd_3792766 := by exact prefixLift 3792766
  have htrace : WordTrace (prefixWord ++ tailWord_3792766) baseStart_3792766 baseEnd_3792766 := by
    simpa [prefixWord, tailWord_3792766, baseEnd_3792766] using wordTrace_append hprefix tailTrace_3792766
  have hstable : (prefixWord ++ tailWord_3792766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792766).length < 2 ^ (prefixWord ++ tailWord_3792766).sum := by decide
  have hdescent : baseEnd_3792766 < baseStart_3792766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792785 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_3792785 : Nat := 118140960795 + 3792785 * 2 ^ 59
def prefixEnd_3792785 : Nat := 4983230072969 + 3 ^ 40 * 3792785 * 2
def baseEnd_3792785 : Nat := 1947521724163048444944805

theorem tailTrace_3792785 : CollatzResearch.WordTrace tailWord_3792785 prefixEnd_3792785 1947521724163048444944805 := by
  unfold tailWord_3792785
  simp only [CollatzResearch.WordTrace]
  refine ⟨138334233564395175952611809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92222822376263450635074539 138334233564395175952611809)
  ·
    refine ⟨103750675173296381964458857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138334233564395175952611809 103750675173296381964458857)
    ·
      refine ⟨77813006379972286473344143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103750675173296381964458857 77813006379972286473344143)
      ·
        refine ⟨116719509569958429710016215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77813006379972286473344143 116719509569958429710016215)
        ·
          refine ⟨175079264354937644565024323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116719509569958429710016215 175079264354937644565024323)
          ·
            refine ⟨262618896532406466847536485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175079264354937644565024323 262618896532406466847536485)
            ·
              refine ⟨49241043099826212533913091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262618896532406466847536485 49241043099826212533913091)
              ·
                refine ⟨73861564649739318800869637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49241043099826212533913091 73861564649739318800869637)
                ·
                  refine ⟨13849043371826122275163057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73861564649739318800869637 13849043371826122275163057)
                  ·
                    refine ⟨10386782528869591706372293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13849043371826122275163057 10386782528869591706372293)
                    ·
                      refine ⟨1947521724163048444944805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10386782528869591706372293 1947521724163048444944805)
                      ·
                        rfl

theorem cell23_3792785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_3792785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792785 prefixEnd_3792785 := by exact prefixLift 3792785
  have htrace : WordTrace (prefixWord ++ tailWord_3792785) baseStart_3792785 baseEnd_3792785 := by
    simpa [prefixWord, tailWord_3792785, baseEnd_3792785] using wordTrace_append hprefix tailTrace_3792785
  have hstable : (prefixWord ++ tailWord_3792785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792785).length < 2 ^ (prefixWord ++ tailWord_3792785).sum := by decide
  have hdescent : baseEnd_3792785 < baseStart_3792785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792789 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_3792789 : Nat := 118140960795 + 3792789 * 2 ^ 59
def prefixEnd_3792789 : Nat := 4983230072969 + 3 ^ 40 * 3792789 * 2
def baseEnd_3792789 : Nat := 1947523778085666429294787

theorem tailTrace_3792789 : CollatzResearch.WordTrace tailWord_3792789 prefixEnd_3792789 1947523778085666429294787 := by
  unfold tailWord_3792789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138334379456380684635757421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92222919637587123090504947 138334379456380684635757421)
  ·
    refine ⟨51875392296142756738409033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138334379456380684635757421 51875392296142756738409033)
    ·
      refine ⟨38906544222107067553806775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51875392296142756738409033 38906544222107067553806775)
      ·
        refine ⟨58359816333160601330710163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38906544222107067553806775 58359816333160601330710163)
        ·
          refine ⟨87539724499740901996065245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58359816333160601330710163 87539724499740901996065245)
          ·
            refine ⟨32827396687402838248524467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87539724499740901996065245 32827396687402838248524467)
            ·
              refine ⟨49241095031104257372786701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32827396687402838248524467 49241095031104257372786701)
              ·
                refine ⟨18465410636664096514795013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49241095031104257372786701 18465410636664096514795013)
                ·
                  refine ⟨3462264494374518096524065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18465410636664096514795013 3462264494374518096524065)
                  ·
                    refine ⟨2596698370780888572393049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462264494374518096524065 2596698370780888572393049)
                    ·
                      refine ⟨1947523778085666429294787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596698370780888572393049 1947523778085666429294787)
                      ·
                        rfl

theorem cell23_3792789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_3792789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792789 prefixEnd_3792789 := by exact prefixLift 3792789
  have htrace : WordTrace (prefixWord ++ tailWord_3792789) baseStart_3792789 baseEnd_3792789 := by
    simpa [prefixWord, tailWord_3792789, baseEnd_3792789] using wordTrace_append hprefix tailTrace_3792789
  have hstable : (prefixWord ++ tailWord_3792789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792789).length < 2 ^ (prefixWord ++ tailWord_3792789).sum := by decide
  have hdescent : baseEnd_3792789 < baseStart_3792789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792842 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_3792842 : Nat := 118140960795 + 3792842 * 2 ^ 59
def prefixEnd_3792842 : Nat := 4983230072969 + 3 ^ 40 * 3792842 * 2
def baseEnd_3792842 : Nat := 649183664186784907310681

theorem tailTrace_3792842 : CollatzResearch.WordTrace tailWord_3792842 prefixEnd_3792842 649183664186784907310681 := by
  unfold tailWord_3792842
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584078131297168671859195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92224208350125783124957853 34584078131297168671859195)
  ·
    refine ⟨51876117196945753007788793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34584078131297168671859195 51876117196945753007788793)
    ·
      refine ⟨38907087897709314755841595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51876117196945753007788793 38907087897709314755841595)
      ·
        refine ⟨58360631846563972133762393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38907087897709314755841595 58360631846563972133762393)
        ·
          refine ⟨43770473884922979100321795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58360631846563972133762393 43770473884922979100321795)
          ·
            refine ⟨65655710827384468650482693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43770473884922979100321795 65655710827384468650482693)
            ·
              refine ⟨12310445780134587871965505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65655710827384468650482693 12310445780134587871965505)
              ·
                refine ⟨9232834335100940903974129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310445780134587871965505 9232834335100940903974129)
                ·
                  refine ⟨6924625751325705677980597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9232834335100940903974129 6924625751325705677980597)
                  ·
                    refine ⟨649183664186784907310681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6924625751325705677980597 649183664186784907310681)
                    ·
                      rfl

theorem cell23_3792842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_3792842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792842 prefixEnd_3792842 := by exact prefixLift 3792842
  have htrace : WordTrace (prefixWord ++ tailWord_3792842) baseStart_3792842 baseEnd_3792842 := by
    simpa [prefixWord, tailWord_3792842, baseEnd_3792842] using wordTrace_append hprefix tailTrace_3792842
  have hstable : (prefixWord ++ tailWord_3792842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792842).length < 2 ^ (prefixWord ++ tailWord_3792842).sum := by decide
  have hdescent : baseEnd_3792842 < baseStart_3792842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792852 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3792852 : Nat := 118140960795 + 3792852 * 2 ^ 59
def prefixEnd_3792852 : Nat := 4983230072969 + 3 ^ 40 * 3792852 * 2
def baseEnd_3792852 : Nat := 1947556127366899682806997

theorem tailTrace_3792852 : CollatzResearch.WordTrace tailWord_3792852 prefixEnd_3792852 1947556127366899682806997 := by
  unfold tailWord_3792852
  simp only [CollatzResearch.WordTrace]
  refine ⟨69168338627576223197650405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92224451503434964263533873 69168338627576223197650405)
  ·
    refine ⟨12969063492670541849559451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69168338627576223197650405 12969063492670541849559451)
    ·
      refine ⟨19453595239005812774339177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12969063492670541849559451 19453595239005812774339177)
      ·
        refine ⟨14590196429254359580754383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19453595239005812774339177 14590196429254359580754383)
        ·
          refine ⟨21885294643881539371131575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14590196429254359580754383 21885294643881539371131575)
          ·
            refine ⟨32827941965822309056697363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21885294643881539371131575 32827941965822309056697363)
            ·
              refine ⟨49241912948733463585046045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32827941965822309056697363 49241912948733463585046045)
              ·
                refine ⟨18465717355775048844392267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49241912948733463585046045 18465717355775048844392267)
                ·
                  refine ⟨27698576033662573266588401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18465717355775048844392267 27698576033662573266588401)
                  ·
                    refine ⟨20773932025246929949941301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27698576033662573266588401 20773932025246929949941301)
                    ·
                      refine ⟨1947556127366899682806997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20773932025246929949941301 1947556127366899682806997)
                      ·
                        rfl

theorem cell23_3792852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3792852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792852 prefixEnd_3792852 := by exact prefixLift 3792852
  have htrace : WordTrace (prefixWord ++ tailWord_3792852) baseStart_3792852 baseEnd_3792852 := by
    simpa [prefixWord, tailWord_3792852, baseEnd_3792852] using wordTrace_append hprefix tailTrace_3792852
  have hstable : (prefixWord ++ tailWord_3792852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792852).length < 2 ^ (prefixWord ++ tailWord_3792852).sum := by decide
  have hdescent : baseEnd_3792852 < baseStart_3792852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792875 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_3792875 : Nat := 118140960795 + 3792875 * 2 ^ 59
def prefixEnd_3792875 : Nat := 4983230072969 + 3 ^ 40 * 3792875 * 2
def baseEnd_3792875 : Nat := 1947567937421953092819391

theorem tailTrace_3792875 : CollatzResearch.WordTrace tailWord_3792875 prefixEnd_3792875 1947567937421953092819391 := by
  unfold tailWord_3792875
  simp only [CollatzResearch.WordTrace]
  refine ⟨138337516134069121323388079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92225010756046080882258719 138337516134069121323388079)
  ·
    refine ⟨207506274201103681985082119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138337516134069121323388079 207506274201103681985082119)
    ·
      refine ⟨311259411301655522977623179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207506274201103681985082119 311259411301655522977623179)
      ·
        refine ⟨466889116952483284466434769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311259411301655522977623179 466889116952483284466434769)
        ·
          refine ⟨350166837714362463349826077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466889116952483284466434769 350166837714362463349826077)
          ·
            refine ⟨131312564142885923756184779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350166837714362463349826077 131312564142885923756184779)
            ·
              refine ⟨196968846214328885634277169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131312564142885923756184779 196968846214328885634277169)
              ·
                refine ⟨147726634660746664225707877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196968846214328885634277169 147726634660746664225707877)
                ·
                  refine ⟨27698743998889999542320227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147726634660746664225707877 27698743998889999542320227)
                  ·
                    refine ⟨41548115998334999313480341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27698743998889999542320227 41548115998334999313480341)
                    ·
                      refine ⟨1947567937421953092819391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41548115998334999313480341 1947567937421953092819391)
                      ·
                        rfl

theorem cell23_3792875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_3792875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792875 prefixEnd_3792875 := by exact prefixLift 3792875
  have htrace : WordTrace (prefixWord ++ tailWord_3792875) baseStart_3792875 baseEnd_3792875 := by
    simpa [prefixWord, tailWord_3792875, baseEnd_3792875] using wordTrace_append hprefix tailTrace_3792875
  have hstable : (prefixWord ++ tailWord_3792875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792875).length < 2 ^ (prefixWord ++ tailWord_3792875).sum := by decide
  have hdescent : baseEnd_3792875 < baseStart_3792875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792906 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_3792906 : Nat := 118140960795 + 3792906 * 2 ^ 59
def prefixEnd_3792906 : Nat := 4983230072969 + 3 ^ 40 * 3792906 * 2
def baseEnd_3792906 : Nat := 649194618440747490510583

theorem tailTrace_3792906 : CollatzResearch.WordTrace tailWord_3792906 prefixEnd_3792906 649194618440747490510583 := by
  unfold tailWord_3792906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584661699239203404441643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92225764531304542411844381 34584661699239203404441643)
  ·
    refine ⟨51876992548858805106662465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34584661699239203404441643 51876992548858805106662465)
    ·
      refine ⟨38907744411644103829996849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51876992548858805106662465 38907744411644103829996849)
      ·
        refine ⟨29180808308733077872497637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38907744411644103829996849 29180808308733077872497637)
        ·
          refine ⟨5471401557887452101093307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29180808308733077872497637 5471401557887452101093307)
          ·
            refine ⟨8207102336831178151639961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471401557887452101093307 8207102336831178151639961)
            ·
              refine ⟨6155326752623383613729971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8207102336831178151639961 6155326752623383613729971)
              ·
                refine ⟨9232990128935075420594957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155326752623383613729971 9232990128935075420594957)
                ·
                  refine ⟨3462371298350653282723109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9232990128935075420594957 3462371298350653282723109)
                  ·
                    refine ⟨649194618440747490510583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3462371298350653282723109 649194618440747490510583)
                    ·
                      rfl

theorem cell23_3792906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_3792906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792906 prefixEnd_3792906 := by exact prefixLift 3792906
  have htrace : WordTrace (prefixWord ++ tailWord_3792906) baseStart_3792906 baseEnd_3792906 := by
    simpa [prefixWord, tailWord_3792906, baseEnd_3792906] using wordTrace_append hprefix tailTrace_3792906
  have hstable : (prefixWord ++ tailWord_3792906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792906).length < 2 ^ (prefixWord ++ tailWord_3792906).sum := by decide
  have hdescent : baseEnd_3792906 < baseStart_3792906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792949 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3792949 : Nat := 118140960795 + 3792949 * 2 ^ 59
def prefixEnd_3792949 : Nat := 4983230072969 + 3 ^ 40 * 3792949 * 2
def baseEnd_3792949 : Nat := 649201978330128601098017

theorem tailTrace_3792949 : CollatzResearch.WordTrace tailWord_3792949 prefixEnd_3792949 649201978330128601098017 := by
  unfold tailWord_3792949
  simp only [CollatzResearch.WordTrace]
  refine ⟨138340215135801031961581901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92226810090534021307721267 138340215135801031961581901)
  ·
    refine ⟨51877580675925386985593213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138340215135801031961581901 51877580675925386985593213)
    ·
      refine ⟨19454092753472020119597455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51877580675925386985593213 19454092753472020119597455)
      ·
        refine ⟨29181139130208030179396183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19454092753472020119597455 29181139130208030179396183)
        ·
          refine ⟨43771708695312045269094275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29181139130208030179396183 43771708695312045269094275)
          ·
            refine ⟨65657563042968067903641413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43771708695312045269094275 65657563042968067903641413)
            ·
              refine ⟨12310793070556512731932765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65657563042968067903641413 12310793070556512731932765)
              ·
                refine ⟨4616547401458692274474787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12310793070556512731932765 4616547401458692274474787)
                ·
                  refine ⟨6924821102188038411712181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616547401458692274474787 6924821102188038411712181)
                  ·
                    refine ⟨649201978330128601098017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6924821102188038411712181 649201978330128601098017)
                    ·
                      rfl

theorem cell23_3792949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3792949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792949 prefixEnd_3792949 := by exact prefixLift 3792949
  have htrace : WordTrace (prefixWord ++ tailWord_3792949) baseStart_3792949 baseEnd_3792949 := by
    simpa [prefixWord, tailWord_3792949, baseEnd_3792949] using wordTrace_append hprefix tailTrace_3792949
  have hstable : (prefixWord ++ tailWord_3792949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792949).length < 2 ^ (prefixWord ++ tailWord_3792949).sum := by decide
  have hdescent : baseEnd_3792949 < baseStart_3792949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792956 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_3792956 : Nat := 118140960795 + 3792956 * 2 ^ 59
def prefixEnd_3792956 : Nat := 4983230072969 + 3 ^ 40 * 3792956 * 2
def baseEnd_3792956 : Nat := 1947609529354967275906519

theorem tailTrace_3792956 : CollatzResearch.WordTrace tailWord_3792956 prefixEnd_3792956 1947609529354967275906519 := by
  unfold tailWord_3792956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69170235223387836078543361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92226980297850448104724481 69170235223387836078543361)
  ·
    refine ⟨51877676417540877058907521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69170235223387836078543361 51877676417540877058907521)
    ·
      refine ⟨38908257313155657794180641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51877676417540877058907521 38908257313155657794180641)
      ·
        refine ⟨29181192984866743345635481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38908257313155657794180641 29181192984866743345635481)
        ·
          refine ⟨21885894738650057509226611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29181192984866743345635481 21885894738650057509226611)
          ·
            refine ⟨32828842107975086263839917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21885894738650057509226611 32828842107975086263839917)
            ·
              refine ⟨12310815790490657348939969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32828842107975086263839917 12310815790490657348939969)
              ·
                refine ⟨9233111842867993011704977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310815790490657348939969 9233111842867993011704977)
                ·
                  refine ⟨6924833882150994758778733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9233111842867993011704977 6924833882150994758778733)
                  ·
                    refine ⟨2596812705806623034542025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6924833882150994758778733 2596812705806623034542025)
                    ·
                      refine ⟨1947609529354967275906519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596812705806623034542025 1947609529354967275906519)
                      ·
                        rfl

theorem cell23_3792956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_3792956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792956 prefixEnd_3792956 := by exact prefixLift 3792956
  have htrace : WordTrace (prefixWord ++ tailWord_3792956) baseStart_3792956 baseEnd_3792956 := by
    simpa [prefixWord, tailWord_3792956, baseEnd_3792956] using wordTrace_append hprefix tailTrace_3792956
  have hstable : (prefixWord ++ tailWord_3792956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792956).length < 2 ^ (prefixWord ++ tailWord_3792956).sum := by decide
  have hdescent : baseEnd_3792956 < baseStart_3792956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792966 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3792966 : Nat := 118140960795 + 3792966 * 2 ^ 59
def prefixEnd_3792966 : Nat := 4983230072969 + 3 ^ 40 * 3792966 * 2
def baseEnd_3792966 : Nat := 649204888053837412260491

theorem tailTrace_3792966 : CollatzResearch.WordTrace tailWord_3792966 prefixEnd_3792966 649204888053837412260491 := by
  unfold tailWord_3792966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323151099273107620779711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92227223451159629243300501 4323151099273107620779711)
  ·
    refine ⟨6484726648909661431169567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4323151099273107620779711 6484726648909661431169567)
    ·
      refine ⟨9727089973364492146754351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484726648909661431169567 9727089973364492146754351)
      ·
        refine ⟨14590634960046738220131527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727089973364492146754351 14590634960046738220131527)
        ·
          refine ⟨21885952440070107330197291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14590634960046738220131527 21885952440070107330197291)
          ·
            refine ⟨32828928660105160995295937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21885952440070107330197291 32828928660105160995295937)
            ·
              refine ⟨24621696495078870746471953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32828928660105160995295937 24621696495078870746471953)
              ·
                refine ⟨18466272371309153059853965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24621696495078870746471953 18466272371309153059853965)
                ·
                  refine ⟨6924852139240932397445237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18466272371309153059853965 6924852139240932397445237)
                  ·
                    refine ⟨649204888053837412260491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6924852139240932397445237 649204888053837412260491)
                    ·
                      rfl

theorem cell23_3792966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3792966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792966 prefixEnd_3792966 := by exact prefixLift 3792966
  have htrace : WordTrace (prefixWord ++ tailWord_3792966) baseStart_3792966 baseEnd_3792966 := by
    simpa [prefixWord, tailWord_3792966, baseEnd_3792966] using wordTrace_append hprefix tailTrace_3792966
  have hstable : (prefixWord ++ tailWord_3792966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792966).length < 2 ^ (prefixWord ++ tailWord_3792966).sum := by decide
  have hdescent : baseEnd_3792966 < baseStart_3792966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792986 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2]
def baseStart_3792986 : Nat := 118140960795 + 3792986 * 2 ^ 59
def prefixEnd_3792986 : Nat := 4983230072969 + 3 ^ 40 * 3792986 * 2
def baseEnd_3792986 : Nat := 1947624933774602158531381

theorem tailTrace_3792986 : CollatzResearch.WordTrace tailWord_3792986 prefixEnd_3792986 1947624933774602158531381 := by
  unfold tailWord_3792986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34585391159166746820169703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92227709757777991520452541 34585391159166746820169703)
  ·
    refine ⟨51878086738750120230254555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34585391159166746820169703 51878086738750120230254555)
    ·
      refine ⟨77817130108125180345381833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51878086738750120230254555 77817130108125180345381833)
      ·
        refine ⟨58362847581093885259036375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77817130108125180345381833 58362847581093885259036375)
        ·
          refine ⟨87544271371640827888554563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58362847581093885259036375 87544271371640827888554563)
          ·
            refine ⟨131316407057461241832831845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87544271371640827888554563 131316407057461241832831845)
            ·
              refine ⟨24621826323273982843655971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131316407057461241832831845 24621826323273982843655971)
              ·
                refine ⟨36932739484910974265483957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24621826323273982843655971 36932739484910974265483957)
                ·
                  refine ⟨3462444326710403837389121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36932739484910974265483957 3462444326710403837389121)
                  ·
                    refine ⟨2596833245032802878041841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462444326710403837389121 2596833245032802878041841)
                    ·
                      refine ⟨1947624933774602158531381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596833245032802878041841 1947624933774602158531381)
                      ·
                        rfl

theorem cell23_3792986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_3792986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792986 prefixEnd_3792986 := by exact prefixLift 3792986
  have htrace : WordTrace (prefixWord ++ tailWord_3792986) baseStart_3792986 baseEnd_3792986 := by
    simpa [prefixWord, tailWord_3792986, baseEnd_3792986] using wordTrace_append hprefix tailTrace_3792986
  have hstable : (prefixWord ++ tailWord_3792986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792986).length < 2 ^ (prefixWord ++ tailWord_3792986).sum := by decide
  have hdescent : baseEnd_3792986 < baseStart_3792986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792992 : List Nat := [2, 1, 1, 3, 2, 3, 2, 9]
def baseStart_3792992 : Nat := 118140960795 + 3792992 * 2 ^ 59
def prefixEnd_3792992 : Nat := 4983230072969 + 3 ^ 40 * 3792992 * 2
def baseEnd_3792992 : Nat := 72134370913278856853939

theorem tailTrace_3792992 : CollatzResearch.WordTrace tailWord_3792992 prefixEnd_3792992 72134370913278856853939 := by
  unfold tailWord_3792992
  simp only [CollatzResearch.WordTrace]
  refine ⟨69170891737322625152698615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92227855649763500203598153 69170891737322625152698615)
  ·
    refine ⟨103756337605983937729047923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69170891737322625152698615 103756337605983937729047923)
    ·
      refine ⟨155634506408975906593571885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103756337605983937729047923 155634506408975906593571885)
      ·
        refine ⟨58362939903365964972589457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155634506408975906593571885 58362939903365964972589457)
        ·
          refine ⟨43772204927524473729442093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58362939903365964972589457 43772204927524473729442093)
          ·
            refine ⟨16414576847821677648540785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43772204927524473729442093 16414576847821677648540785)
            ·
              refine ⟨12310932635866258236405589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16414576847821677648540785 12310932635866258236405589)
              ·
                refine ⟨72134370913278856853939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12310932635866258236405589 72134370913278856853939)
                ·
                  rfl

theorem cell23_3792992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 9].length) (baseStart_3792992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792992 prefixEnd_3792992 := by exact prefixLift 3792992
  have htrace : WordTrace (prefixWord ++ tailWord_3792992) baseStart_3792992 baseEnd_3792992 := by
    simpa [prefixWord, tailWord_3792992, baseEnd_3792992] using wordTrace_append hprefix tailTrace_3792992
  have hstable : (prefixWord ++ tailWord_3792992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792992).length < 2 ^ (prefixWord ++ tailWord_3792992).sum := by decide
  have hdescent : baseEnd_3792992 < baseStart_3792992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792999 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3792999 : Nat := 118140960795 + 3792999 * 2 ^ 59
def prefixEnd_3792999 : Nat := 4983230072969 + 3 ^ 40 * 3792999 * 2
def baseEnd_3792999 : Nat := 1947631609023110607668821

theorem tailTrace_3792999 : CollatzResearch.WordTrace tailWord_3792999 prefixEnd_3792999 1947631609023110607668821 := by
  unfold tailWord_3792999
  simp only [CollatzResearch.WordTrace]
  refine ⟨138342038785619890500902051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92228025857079927000601367 138342038785619890500902051)
  ·
    refine ⟨207513058178429835751353077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138342038785619890500902051 207513058178429835751353077)
    ·
      refine ⟨19454349204227797101689351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207513058178429835751353077 19454349204227797101689351)
      ·
        refine ⟨29181523806341695652534027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19454349204227797101689351 29181523806341695652534027)
        ·
          refine ⟨43772285709512543478801041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29181523806341695652534027 43772285709512543478801041)
          ·
            refine ⟨32829214282134407609100781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43772285709512543478801041 32829214282134407609100781)
            ·
              refine ⟨12310955355800402853412793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32829214282134407609100781 12310955355800402853412793)
              ·
                refine ⟨9233216516850302140059595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310955355800402853412793 9233216516850302140059595)
                ·
                  refine ⟨13849824775275453210089393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233216516850302140059595 13849824775275453210089393)
                  ·
                    refine ⟨10387368581456589907567045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13849824775275453210089393 10387368581456589907567045)
                    ·
                      refine ⟨1947631609023110607668821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10387368581456589907567045 1947631609023110607668821)
                      ·
                        rfl

theorem cell23_3792999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3792999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3792999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3792999 prefixEnd_3792999 := by exact prefixLift 3792999
  have htrace : WordTrace (prefixWord ++ tailWord_3792999) baseStart_3792999 baseEnd_3792999 := by
    simpa [prefixWord, tailWord_3792999, baseEnd_3792999] using wordTrace_append hprefix tailTrace_3792999
  have hstable : (prefixWord ++ tailWord_3792999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792999).length < 2 ^ (prefixWord ++ tailWord_3792999).sum := by decide
  have hdescent : baseEnd_3792999 < baseStart_3792999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793020 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_3793020 : Nat := 118140960795 + 3793020 * 2 ^ 59
def prefixEnd_3793020 : Nat := 4983230072969 + 3 ^ 40 * 3793020 * 2
def baseEnd_3793020 : Nat := 1947642392116855025506225

theorem tailTrace_3793020 : CollatzResearch.WordTrace tailWord_3793020 prefixEnd_3793020 1947642392116855025506225 := by
  unfold tailWord_3793020
  simp only [CollatzResearch.WordTrace]
  refine ⟨69171402359271905543708257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92228536479029207391611009 69171402359271905543708257)
  ·
    refine ⟨51878551769453929157781193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69171402359271905543708257 51878551769453929157781193)
    ·
      refine ⟨38908913827090446868335895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51878551769453929157781193 38908913827090446868335895)
      ·
        refine ⟨58363370740635670302503843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38908913827090446868335895 58363370740635670302503843)
        ·
          refine ⟨87545056110953505453755765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58363370740635670302503843 87545056110953505453755765)
          ·
            refine ⟨8207349010401891136289603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87545056110953505453755765 8207349010401891136289603)
            ·
              refine ⟨12311023515602836704434405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207349010401891136289603 12311023515602836704434405)
              ·
                refine ⟨2308316909175531882081451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12311023515602836704434405 2308316909175531882081451)
                ·
                  refine ⟨3462475363763297823122177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308316909175531882081451 3462475363763297823122177)
                  ·
                    refine ⟨2596856522822473367341633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462475363763297823122177 2596856522822473367341633)
                    ·
                      refine ⟨1947642392116855025506225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596856522822473367341633 1947642392116855025506225)
                      ·
                        rfl

theorem cell23_3793020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_3793020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793020 prefixEnd_3793020 := by exact prefixLift 3793020
  have htrace : WordTrace (prefixWord ++ tailWord_3793020) baseStart_3793020 baseEnd_3793020 := by
    simpa [prefixWord, tailWord_3793020, baseEnd_3793020] using wordTrace_append hprefix tailTrace_3793020
  have hstable : (prefixWord ++ tailWord_3793020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793020).length < 2 ^ (prefixWord ++ tailWord_3793020).sum := by decide
  have hdescent : baseEnd_3793020 < baseStart_3793020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793054 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3793054 : Nat := 118140960795 + 3793054 * 2 ^ 59
def prefixEnd_3793054 : Nat := 4983230072969 + 3 ^ 40 * 3793054 * 2
def baseEnd_3793054 : Nat := 1947659850459107892481069

theorem tailTrace_3793054 : CollatzResearch.WordTrace tailWord_3793054 prefixEnd_3793054 1947659850459107892481069 := by
  unfold tailWord_3793054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293005600052579361769277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92229363200280423262769477 17293005600052579361769277)
  ·
    refine ⟨6484877100019717260663479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17293005600052579361769277 6484877100019717260663479)
    ·
      refine ⟨9727315650029575890995219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484877100019717260663479 9727315650029575890995219)
      ·
        refine ⟨14590973475044363836492829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727315650029575890995219 14590973475044363836492829)
        ·
          refine ⟨5471615053141636438684811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14590973475044363836492829 5471615053141636438684811)
          ·
            refine ⟨8207422579712454658027217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471615053141636438684811 8207422579712454658027217)
            ·
              refine ⟨6155566934784340993520413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8207422579712454658027217 6155566934784340993520413)
              ·
                refine ⟨2308337600544127872570155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6155566934784340993520413 2308337600544127872570155)
                ·
                  refine ⟨3462506400816191808855233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308337600544127872570155 3462506400816191808855233)
                  ·
                    refine ⟨2596879800612143856641425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462506400816191808855233 2596879800612143856641425)
                    ·
                      refine ⟨1947659850459107892481069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596879800612143856641425 1947659850459107892481069)
                      ·
                        rfl

theorem cell23_3793054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3793054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793054 prefixEnd_3793054 := by exact prefixLift 3793054
  have htrace : WordTrace (prefixWord ++ tailWord_3793054) baseStart_3793054 baseEnd_3793054 := by
    simpa [prefixWord, tailWord_3793054, baseEnd_3793054] using wordTrace_append hprefix tailTrace_3793054
  have hstable : (prefixWord ++ tailWord_3793054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793054).length < 2 ^ (prefixWord ++ tailWord_3793054).sum := by decide
  have hdescent : baseEnd_3793054 < baseStart_3793054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793072 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_3793072 : Nat := 118140960795 + 3793072 * 2 ^ 59
def prefixEnd_3793072 : Nat := 4983230072969 + 3 ^ 40 * 3793072 * 2
def baseEnd_3793072 : Nat := 1947669093110888822055985

theorem tailTrace_3793072 : CollatzResearch.WordTrace tailWord_3793072 prefixEnd_3793072 1947669093110888822055985 := by
  unfold tailWord_3793072
  simp only [CollatzResearch.WordTrace]
  refine ⟨69172350657177711984154735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92229800876236949312206313 69172350657177711984154735)
  ·
    refine ⟨103758525985766567976232103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69172350657177711984154735 103758525985766567976232103)
    ·
      refine ⟨155637788978649851964348155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103758525985766567976232103 155637788978649851964348155)
      ·
        refine ⟨233456683467974777946522233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155637788978649851964348155 233456683467974777946522233)
        ·
          refine ⟨175092512600981083459891675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233456683467974777946522233 175092512600981083459891675)
          ·
            refine ⟨262638768901471625189837513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175092512600981083459891675 262638768901471625189837513)
            ·
              refine ⟨196979076676103718892378135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262638768901471625189837513 196979076676103718892378135)
              ·
                refine ⟨295468615014155578338567203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196979076676103718892378135 295468615014155578338567203)
                ·
                  refine ⟨443202922521233367507850805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295468615014155578338567203 443202922521233367507850805)
                  ·
                    refine ⟨41550273986365628203861013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 443202922521233367507850805 41550273986365628203861013)
                    ·
                      refine ⟨1947669093110888822055985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41550273986365628203861013 1947669093110888822055985)
                      ·
                        rfl

theorem cell23_3793072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_3793072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793072 prefixEnd_3793072 := by exact prefixLift 3793072
  have htrace : WordTrace (prefixWord ++ tailWord_3793072) baseStart_3793072 baseEnd_3793072 := by
    simpa [prefixWord, tailWord_3793072, baseEnd_3793072] using wordTrace_append hprefix tailTrace_3793072
  have hstable : (prefixWord ++ tailWord_3793072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793072).length < 2 ^ (prefixWord ++ tailWord_3793072).sum := by decide
  have hdescent : baseEnd_3793072 < baseStart_3793072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793093 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 2, 2, 2]
def baseStart_3793093 : Nat := 118140960795 + 3793093 * 2 ^ 59
def prefixEnd_3793093 : Nat := 4983230072969 + 3 ^ 40 * 3793093 * 2
def baseEnd_3793093 : Nat := 1947679876204633239893389

theorem tailTrace_3793093 : CollatzResearch.WordTrace tailWord_3793093 prefixEnd_3793093 1947679876204633239893389 := by
  unfold tailWord_3793093
  simp only [CollatzResearch.WordTrace]
  refine ⟨138345467247279344554823933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92230311498186229703215955 138345467247279344554823933)
  ·
    refine ⟨51879550217729754208058975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138345467247279344554823933 51879550217729754208058975)
    ·
      refine ⟨77819325326594631312088463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51879550217729754208058975 77819325326594631312088463)
      ·
        refine ⟨116728987989891946968132695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77819325326594631312088463 116728987989891946968132695)
        ·
          refine ⟨175093481984837920452199043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116728987989891946968132695 175093481984837920452199043)
          ·
            refine ⟨262640222977256880678298565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175093481984837920452199043 262640222977256880678298565)
            ·
              refine ⟨49245041808235665127180981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262640222977256880678298565 49245041808235665127180981)
              ·
                refine ⟨4616722669522093605673217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49245041808235665127180981 4616722669522093605673217)
                ·
                  refine ⟨3462542002141570204254913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4616722669522093605673217 3462542002141570204254913)
                  ·
                    refine ⟨2596906501606177653191185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462542002141570204254913 2596906501606177653191185)
                    ·
                      refine ⟨1947679876204633239893389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2596906501606177653191185 1947679876204633239893389)
                      ·
                        rfl

theorem cell23_3793093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_3793093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793093 prefixEnd_3793093 := by exact prefixLift 3793093
  have htrace : WordTrace (prefixWord ++ tailWord_3793093) baseStart_3793093 baseEnd_3793093 := by
    simpa [prefixWord, tailWord_3793093, baseEnd_3793093] using wordTrace_append hprefix tailTrace_3793093
  have hstable : (prefixWord ++ tailWord_3793093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793093).length < 2 ^ (prefixWord ++ tailWord_3793093).sum := by decide
  have hdescent : baseEnd_3793093 < baseStart_3793093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793129 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_3793129 : Nat := 118140960795 + 3793129 * 2 ^ 59
def prefixEnd_3793129 : Nat := 4983230072969 + 3 ^ 40 * 3793129 * 2
def baseEnd_3793129 : Nat := 649232787169398366347741

theorem tailTrace_3793129 : CollatzResearch.WordTrace tailWord_3793129 prefixEnd_3793129 649232787169398366347741 := by
  unfold tailWord_3793129
  simp only [CollatzResearch.WordTrace]
  refine ⟨138346780275148922703134441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92231186850099281802089627 138346780275148922703134441)
  ·
    refine ⟨103760085206361692027350831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138346780275148922703134441 103760085206361692027350831)
    ·
      refine ⟨155640127809542538041026247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103760085206361692027350831 155640127809542538041026247)
      ·
        refine ⟨233460191714313807061539371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155640127809542538041026247 233460191714313807061539371)
        ·
          refine ⟨350190287571470710592309057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233460191714313807061539371 350190287571470710592309057)
          ·
            refine ⟨262642715678603032944231793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350190287571470710592309057 262642715678603032944231793)
            ·
              refine ⟨196982036758952274708173845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262642715678603032944231793 196982036758952274708173845)
              ·
                refine ⟨9233532973075887876945649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196982036758952274708173845 9233532973075887876945649)
                ·
                  refine ⟨6925149729806915907709237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9233532973075887876945649 6925149729806915907709237)
                  ·
                    refine ⟨649232787169398366347741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6925149729806915907709237 649232787169398366347741)
                    ·
                      rfl

theorem cell23_3793129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_3793129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793129 prefixEnd_3793129 := by exact prefixLift 3793129
  have htrace : WordTrace (prefixWord ++ tailWord_3793129) baseStart_3793129 baseEnd_3793129 := by
    simpa [prefixWord, tailWord_3793129, baseEnd_3793129] using wordTrace_append hprefix tailTrace_3793129
  have hstable : (prefixWord ++ tailWord_3793129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793129).length < 2 ^ (prefixWord ++ tailWord_3793129).sum := by decide
  have hdescent : baseEnd_3793129 < baseStart_3793129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793133 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 7]
def baseStart_3793133 : Nat := 118140960795 + 3793133 * 2 ^ 59
def prefixEnd_3793133 : Nat := 4983230072969 + 3 ^ 40 * 3793133 * 2
def baseEnd_3793133 : Nat := 216411157270090342599245

theorem tailTrace_3793133 : CollatzResearch.WordTrace tailWord_3793133 prefixEnd_3793133 216411157270090342599245 := by
  unfold tailWord_3793133
  simp only [CollatzResearch.WordTrace]
  refine ⟨138346926167134431386280053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92231284111422954257520035 138346926167134431386280053)
  ·
    refine ⟨12970024328168852942463755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138346926167134431386280053 12970024328168852942463755)
    ·
      refine ⟨19455036492253279413695633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970024328168852942463755 19455036492253279413695633)
      ·
        refine ⟨14591277369189959560271725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19455036492253279413695633 14591277369189959560271725)
        ·
          refine ⟨5471729013446234835101897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14591277369189959560271725 5471729013446234835101897)
          ·
            refine ⟨4103796760084676126326423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5471729013446234835101897 4103796760084676126326423)
            ·
              refine ⟨6155695140127014189489635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103796760084676126326423 6155695140127014189489635)
              ·
                refine ⟨9233542710190521284234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155695140127014189489635 9233542710190521284234453)
                ·
                  refine ⟨216411157270090342599245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9233542710190521284234453 216411157270090342599245)
                  ·
                    rfl

theorem cell23_3793133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_3793133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793133 prefixEnd_3793133 := by exact prefixLift 3793133
  have htrace : WordTrace (prefixWord ++ tailWord_3793133) baseStart_3793133 baseEnd_3793133 := by
    simpa [prefixWord, tailWord_3793133, baseEnd_3793133] using wordTrace_append hprefix tailTrace_3793133
  have hstable : (prefixWord ++ tailWord_3793133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793133).length < 2 ^ (prefixWord ++ tailWord_3793133).sum := by decide
  have hdescent : baseEnd_3793133 < baseStart_3793133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793139 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5]
def baseStart_3793139 : Nat := 118140960795 + 3793139 * 2 ^ 59
def prefixEnd_3793139 : Nat := 4983230072969 + 3 ^ 40 * 3793139 * 2
def baseEnd_3793139 : Nat := 1947703496314740059918177

theorem tailTrace_3793139 : CollatzResearch.WordTrace tailWord_3793139 prefixEnd_3793139 1947703496314740059918177 := by
  unfold tailWord_3793139
  simp only [CollatzResearch.WordTrace]
  refine ⟨138347145005112694410998471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92231430003408462940665647 138347145005112694410998471)
  ·
    refine ⟨207520717507669041616497707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138347145005112694410998471 207520717507669041616497707)
    ·
      refine ⟨311281076261503562424746561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207520717507669041616497707 311281076261503562424746561)
      ·
        refine ⟨233460807196127671818559921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311281076261503562424746561 233460807196127671818559921)
        ·
          refine ⟨175095605397095753863919941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233460807196127671818559921 175095605397095753863919941)
          ·
            refine ⟨32830426011955453849484989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175095605397095753863919941 32830426011955453849484989)
            ·
              refine ⟨12311409754483295193556871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32830426011955453849484989 12311409754483295193556871)
              ·
                refine ⟨18467114631724942790335307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12311409754483295193556871 18467114631724942790335307)
                ·
                  refine ⟨27700671947587414185502961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18467114631724942790335307 27700671947587414185502961)
                  ·
                    refine ⟨20775503960690560639127221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27700671947587414185502961 20775503960690560639127221)
                    ·
                      refine ⟨1947703496314740059918177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20775503960690560639127221 1947703496314740059918177)
                      ·
                        rfl

theorem cell23_3793139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_3793139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793139 prefixEnd_3793139 := by exact prefixLift 3793139
  have htrace : WordTrace (prefixWord ++ tailWord_3793139) baseStart_3793139 baseEnd_3793139 := by
    simpa [prefixWord, tailWord_3793139, baseEnd_3793139] using wordTrace_append hprefix tailTrace_3793139
  have hstable : (prefixWord ++ tailWord_3793139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793139).length < 2 ^ (prefixWord ++ tailWord_3793139).sum := by decide
  have hdescent : baseEnd_3793139 < baseStart_3793139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793149 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3793149 : Nat := 118140960795 + 3793149 * 2 ^ 59
def prefixEnd_3793149 : Nat := 4983230072969 + 3 ^ 40 * 3793149 * 2
def baseEnd_3793149 : Nat := 1947708631121285020793131

theorem tailTrace_3793149 : CollatzResearch.WordTrace tailWord_3793149 prefixEnd_3793149 1947708631121285020793131 := by
  unfold tailWord_3793149
  simp only [CollatzResearch.WordTrace]
  refine ⟨138347509735076466118862501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92231673156717644079241667 138347509735076466118862501)
  ·
    refine ⟨25940158075326837397286719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138347509735076466118862501 25940158075326837397286719)
    ·
      refine ⟨38910237112990256095930079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25940158075326837397286719 38910237112990256095930079)
      ·
        refine ⟨58365355669485384143895119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38910237112990256095930079 58365355669485384143895119)
        ·
          refine ⟨87548033504228076215842679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58365355669485384143895119 87548033504228076215842679)
          ·
            refine ⟨131322050256342114323764019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87548033504228076215842679 131322050256342114323764019)
            ·
              refine ⟨196983075384513171485646029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131322050256342114323764019 196983075384513171485646029)
              ·
                refine ⟨73868653269192439307117261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196983075384513171485646029 73868653269192439307117261)
                ·
                  refine ⟨27700744975947164740168973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73868653269192439307117261 27700744975947164740168973)
                  ·
                    refine ⟨10387779365980186777563365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27700744975947164740168973 10387779365980186777563365)
                    ·
                      refine ⟨1947708631121285020793131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10387779365980186777563365 1947708631121285020793131)
                      ·
                        rfl

theorem cell23_3793149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3793149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793149 prefixEnd_3793149 := by exact prefixLift 3793149
  have htrace : WordTrace (prefixWord ++ tailWord_3793149) baseStart_3793149 baseEnd_3793149 := by
    simpa [prefixWord, tailWord_3793149, baseEnd_3793149] using wordTrace_append hprefix tailTrace_3793149
  have hstable : (prefixWord ++ tailWord_3793149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793149).length < 2 ^ (prefixWord ++ tailWord_3793149).sum := by decide
  have hdescent : baseEnd_3793149 < baseStart_3793149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793217 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3793217 : Nat := 118140960795 + 3793217 * 2 ^ 59
def prefixEnd_3793217 : Nat := 4983230072969 + 3 ^ 40 * 3793217 * 2
def baseEnd_3793217 : Nat := 1947743547805790754742819

theorem tailTrace_3793217 : CollatzResearch.WordTrace tailWord_3793217 prefixEnd_3793217 1947743547805790754742819 := by
  unfold tailWord_3793217
  simp only [CollatzResearch.WordTrace]
  refine ⟨138349989898830113732337905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92233326599220075821558603 138349989898830113732337905)
  ·
    refine ⟨103762492424122585299253429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138349989898830113732337905 103762492424122585299253429)
    ·
      refine ⟨9727733664761492371805009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103762492424122585299253429 9727733664761492371805009)
      ·
        refine ⟨7295800248571119278853757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9727733664761492371805009 7295800248571119278853757)
        ·
          refine ⟨2735925093214169729570159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7295800248571119278853757 2735925093214169729570159)
          ·
            refine ⟨4103887639821254594355239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735925093214169729570159 4103887639821254594355239)
            ·
              refine ⟨6155831459731881891532859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103887639821254594355239 6155831459731881891532859)
              ·
                refine ⟨9233747189597822837299289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155831459731881891532859 9233747189597822837299289)
                ·
                  refine ⟨6925310392198367127974467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9233747189597822837299289 6925310392198367127974467)
                  ·
                    refine ⟨10387965588297550691961701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6925310392198367127974467 10387965588297550691961701)
                    ·
                      refine ⟨1947743547805790754742819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10387965588297550691961701 1947743547805790754742819)
                      ·
                        rfl

theorem cell23_3793217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3793217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793217 prefixEnd_3793217 := by exact prefixLift 3793217
  have htrace : WordTrace (prefixWord ++ tailWord_3793217) baseStart_3793217 baseEnd_3793217 := by
    simpa [prefixWord, tailWord_3793217, baseEnd_3793217] using wordTrace_append hprefix tailTrace_3793217
  have hstable : (prefixWord ++ tailWord_3793217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793217).length < 2 ^ (prefixWord ++ tailWord_3793217).sum := by decide
  have hdescent : baseEnd_3793217 < baseStart_3793217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793220 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3793220 : Nat := 118140960795 + 3793220 * 2 ^ 59
def prefixEnd_3793220 : Nat := 4983230072969 + 3 ^ 40 * 3793220 * 2
def baseEnd_3793220 : Nat := 1947745088247754243005305

theorem tailTrace_3793220 : CollatzResearch.WordTrace tailWord_3793220 prefixEnd_3793220 1947745088247754243005305 := by
  unfold tailWord_3793220
  simp only [CollatzResearch.WordTrace]
  refine ⟨69175049658909622622348557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92233399545212830163131409 69175049658909622622348557)
  ·
    refine ⟨25940643622091108483380709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69175049658909622622348557 25940643622091108483380709)
    ·
      refine ⟨4863870679142082840633883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25940643622091108483380709 4863870679142082840633883)
      ·
        refine ⟨7295806018713124260950825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863870679142082840633883 7295806018713124260950825)
        ·
          refine ⟨5471854514034843195713119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7295806018713124260950825 5471854514034843195713119)
          ·
            refine ⟨8207781771052264793569679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471854514034843195713119 8207781771052264793569679)
            ·
              refine ⟨12311672656578397190354519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207781771052264793569679 12311672656578397190354519)
              ·
                refine ⟨18467508984867595785531779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12311672656578397190354519 18467508984867595785531779)
                ·
                  refine ⟨27701263477301393678297669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18467508984867595785531779 27701263477301393678297669)
                  ·
                    refine ⟨5193986901994011314680813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27701263477301393678297669 5193986901994011314680813)
                    ·
                      refine ⟨1947745088247754243005305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5193986901994011314680813 1947745088247754243005305)
                      ·
                        rfl

theorem cell23_3793220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3793220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793220 prefixEnd_3793220 := by exact prefixLift 3793220
  have htrace : WordTrace (prefixWord ++ tailWord_3793220) baseStart_3793220 baseEnd_3793220 := by
    simpa [prefixWord, tailWord_3793220, baseEnd_3793220] using wordTrace_append hprefix tailTrace_3793220
  have hstable : (prefixWord ++ tailWord_3793220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793220).length < 2 ^ (prefixWord ++ tailWord_3793220).sum := by decide
  have hdescent : baseEnd_3793220 < baseStart_3793220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793249 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_3793249 : Nat := 118140960795 + 3793249 * 2 ^ 59
def prefixEnd_3793249 : Nat := 4983230072969 + 3 ^ 40 * 3793249 * 2
def baseEnd_3793249 : Nat := 649253326395578209847557

theorem tailTrace_3793249 : CollatzResearch.WordTrace tailWord_3793249 prefixEnd_3793249 649253326395578209847557 := by
  unfold tailWord_3793249
  simp only [CollatzResearch.WordTrace]
  refine ⟨138351157034714183197502801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92234104689809455465001867 138351157034714183197502801)
  ·
    refine ⟨103763367776035637398127101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138351157034714183197502801 103763367776035637398127101)
    ·
      refine ⟨38911262916013364024297663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103763367776035637398127101 38911262916013364024297663)
      ·
        refine ⟨58366894374020046036446495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38911262916013364024297663 58366894374020046036446495)
        ·
          refine ⟨87550341561030069054669743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58366894374020046036446495 87550341561030069054669743)
          ·
            refine ⟨131325512341545103582004615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87550341561030069054669743 131325512341545103582004615)
            ·
              refine ⟨196988268512317655373006923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131325512341545103582004615 196988268512317655373006923)
              ·
                refine ⟨295482402768476483059510385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196988268512317655373006923 295482402768476483059510385)
                ·
                  refine ⟨221611802076357362294632789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295482402768476483059510385 221611802076357362294632789)
                  ·
                    refine ⟨649253326395578209847557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 221611802076357362294632789 649253326395578209847557)
                    ·
                      rfl

theorem cell23_3793249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_3793249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793249 prefixEnd_3793249 := by exact prefixLift 3793249
  have htrace : WordTrace (prefixWord ++ tailWord_3793249) baseStart_3793249 baseEnd_3793249 := by
    simpa [prefixWord, tailWord_3793249, baseEnd_3793249] using wordTrace_append hprefix tailTrace_3793249
  have hstable : (prefixWord ++ tailWord_3793249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793249).length < 2 ^ (prefixWord ++ tailWord_3793249).sum := by decide
  have hdescent : baseEnd_3793249 < baseStart_3793249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793250 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3793250 : Nat := 118140960795 + 3793250 * 2 ^ 59
def prefixEnd_3793250 : Nat := 4983230072969 + 3 ^ 40 * 3793250 * 2
def baseEnd_3793250 : Nat := 1947760492667389125630167

theorem tailTrace_3793250 : CollatzResearch.WordTrace tailWord_3793250 prefixEnd_3793250 1947760492667389125630167 := by
  unfold tailWord_3793250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34587798376927640092072301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92234129005140373578859469 34587798376927640092072301)
  ·
    refine ⟨12970424391347865034527113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34587798376927640092072301 12970424391347865034527113)
    ·
      refine ⟨9727818293510898775895335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12970424391347865034527113 9727818293510898775895335)
      ·
        refine ⟨14591727440266348163843003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727818293510898775895335 14591727440266348163843003)
        ·
          refine ⟨21887591160399522245764505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14591727440266348163843003 21887591160399522245764505)
          ·
            refine ⟨16415693370299641684323379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21887591160399522245764505 16415693370299641684323379)
            ·
              refine ⟨24623540055449462526485069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16415693370299641684323379 24623540055449462526485069)
              ·
                refine ⟨9233827520793548447431901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24623540055449462526485069 9233827520793548447431901)
                ·
                  refine ⟨3462685320297580667786963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9233827520793548447431901 3462685320297580667786963)
                  ·
                    refine ⟨5194027980446371001680445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462685320297580667786963 5194027980446371001680445)
                    ·
                      refine ⟨1947760492667389125630167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194027980446371001680445 1947760492667389125630167)
                      ·
                        rfl

theorem cell23_3793250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3793250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793250 prefixEnd_3793250 := by exact prefixLift 3793250
  have htrace : WordTrace (prefixWord ++ tailWord_3793250) baseStart_3793250 baseEnd_3793250 := by
    simpa [prefixWord, tailWord_3793250, baseEnd_3793250] using wordTrace_append hprefix tailTrace_3793250
  have hstable : (prefixWord ++ tailWord_3793250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793250).length < 2 ^ (prefixWord ++ tailWord_3793250).sum := by decide
  have hdescent : baseEnd_3793250 < baseStart_3793250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793279 : List Nat := [1, 1, 2, 2, 1, 1, 2, 13]
def baseStart_3793279 : Nat := 118140960795 + 3793279 * 2 ^ 59
def prefixEnd_3793279 : Nat := 4983230072969 + 3 ^ 40 * 3793279 * 2
def baseEnd_3793279 : Nat := 72139829022458130080279

theorem tailTrace_3793279 : CollatzResearch.WordTrace tailWord_3793279 prefixEnd_3793279 72139829022458130080279 := by
  unfold tailWord_3793279
  simp only [CollatzResearch.WordTrace]
  refine ⟨138352251224605498321094891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92234834149736998880729927 138352251224605498321094891)
  ·
    refine ⟨207528376836908247481642337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138352251224605498321094891 207528376836908247481642337)
    ·
      refine ⟨155646282627681185611231753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207528376836908247481642337 155646282627681185611231753)
      ·
        refine ⟨116734711970760889208423815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155646282627681185611231753 116734711970760889208423815)
        ·
          refine ⟨175102067956141333812635723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116734711970760889208423815 175102067956141333812635723)
          ·
            refine ⟨262653101934212000718953585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175102067956141333812635723 262653101934212000718953585)
            ·
              refine ⟨196989826450659000539215189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262653101934212000718953585 196989826450659000539215189)
              ·
                refine ⟨72139829022458130080279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 196989826450659000539215189 72139829022458130080279)
                ·
                  rfl

theorem cell23_3793279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 13].length) (baseStart_3793279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793279 prefixEnd_3793279 := by exact prefixLift 3793279
  have htrace : WordTrace (prefixWord ++ tailWord_3793279) baseStart_3793279 baseEnd_3793279 := by
    simpa [prefixWord, tailWord_3793279, baseEnd_3793279] using wordTrace_append hprefix tailTrace_3793279
  have hstable : (prefixWord ++ tailWord_3793279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793279).length < 2 ^ (prefixWord ++ tailWord_3793279).sum := by decide
  have hdescent : baseEnd_3793279 < baseStart_3793279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793310 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3793310 : Nat := 118140960795 + 3793310 * 2 ^ 59
def prefixEnd_3793310 : Nat := 4983230072969 + 3 ^ 40 * 3793310 * 2
def baseEnd_3793310 : Nat := 1947791301506658890879891

theorem tailTrace_3793310 : CollatzResearch.WordTrace tailWord_3793310 prefixEnd_3793310 1947791301506658890879891 := by
  unfold tailWord_3793310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294172735936648826934173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92235587924995460410315589 17294172735936648826934173)
  ·
    refine ⟨6485314775976243310100315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17294172735936648826934173 6485314775976243310100315)
    ·
      refine ⟨9727972163964364965150473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6485314775976243310100315 9727972163964364965150473)
      ·
        refine ⟨7295979122973273723862855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9727972163964364965150473 7295979122973273723862855)
        ·
          refine ⟨10943968684459910585794283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7295979122973273723862855 10943968684459910585794283)
          ·
            refine ⟨16415953026689865878691425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10943968684459910585794283 16415953026689865878691425)
            ·
              refine ⟨12311964770017399409018569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16415953026689865878691425 12311964770017399409018569)
              ·
                refine ⟨9233973577513049556763927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12311964770017399409018569 9233973577513049556763927)
                ·
                  refine ⟨13850960366269574335145891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233973577513049556763927 13850960366269574335145891)
                  ·
                    refine ⟨20776440549404361502718837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13850960366269574335145891 20776440549404361502718837)
                    ·
                      refine ⟨1947791301506658890879891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20776440549404361502718837 1947791301506658890879891)
                      ·
                        rfl

theorem cell23_3793310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3793310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793310 prefixEnd_3793310 := by exact prefixLift 3793310
  have htrace : WordTrace (prefixWord ++ tailWord_3793310) baseStart_3793310 baseEnd_3793310 := by
    simpa [prefixWord, tailWord_3793310, baseEnd_3793310] using wordTrace_append hprefix tailTrace_3793310
  have hstable : (prefixWord ++ tailWord_3793310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793310).length < 2 ^ (prefixWord ++ tailWord_3793310).sum := by decide
  have hdescent : baseEnd_3793310 < baseStart_3793310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793340 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3793340 : Nat := 118140960795 + 3793340 * 2 ^ 59
def prefixEnd_3793340 : Nat := 4983230072969 + 3 ^ 40 * 3793340 * 2
def baseEnd_3793340 : Nat := 1947806705926293773504753

theorem tailTrace_3793340 : CollatzResearch.WordTrace tailWord_3793340 prefixEnd_3793340 1947806705926293773504753 := by
  unfold tailWord_3793340
  simp only [CollatzResearch.WordTrace]
  refine ⟨69177238038692252869532737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92236317384923003826043649 69177238038692252869532737)
  ·
    refine ⟨51882928529019189652149553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69177238038692252869532737 51882928529019189652149553)
    ·
      refine ⟨38912196396764392239112165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51882928529019189652149553 38912196396764392239112165)
      ·
        refine ⟨7296036824393323544833531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38912196396764392239112165 7296036824393323544833531)
        ·
          refine ⟨10944055236589985317250297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296036824393323544833531 10944055236589985317250297)
          ·
            refine ⟨8208041427442488987937723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10944055236589985317250297 8208041427442488987937723)
            ·
              refine ⟨12312062141163733481906585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208041427442488987937723 12312062141163733481906585)
              ·
                refine ⟨9234046605872800111429939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12312062141163733481906585 9234046605872800111429939)
                ·
                  refine ⟨13851069908809200167144909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9234046605872800111429939 13851069908809200167144909)
                  ·
                    refine ⟨5194151215803450062679341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13851069908809200167144909 5194151215803450062679341)
                    ·
                      refine ⟨1947806705926293773504753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194151215803450062679341 1947806705926293773504753)
                      ·
                        rfl

theorem cell23_3793340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3793340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793340 prefixEnd_3793340 := by exact prefixLift 3793340
  have htrace : WordTrace (prefixWord ++ tailWord_3793340) baseStart_3793340 baseEnd_3793340 := by
    simpa [prefixWord, tailWord_3793340, baseEnd_3793340] using wordTrace_append hprefix tailTrace_3793340
  have hstable : (prefixWord ++ tailWord_3793340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793340).length < 2 ^ (prefixWord ++ tailWord_3793340).sum := by decide
  have hdescent : baseEnd_3793340 < baseStart_3793340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793373 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3793373 : Nat := 118140960795 + 3793373 * 2 ^ 59
def prefixEnd_3793373 : Nat := 4983230072969 + 3 ^ 40 * 3793373 * 2
def baseEnd_3793373 : Nat := 649274550262630714797367

theorem tailTrace_3793373 : CollatzResearch.WordTrace tailWord_3793373 prefixEnd_3793373 649274550262630714797367 := by
  unfold tailWord_3793373
  simp only [CollatzResearch.WordTrace]
  refine ⟨138355679686264952375016773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92237119790843301583344515 138355679686264952375016773)
  ·
    refine ⟨25941689941174678570315645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138355679686264952375016773 25941689941174678570315645)
    ·
      refine ⟨9728133727940504463868367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25941689941174678570315645 9728133727940504463868367)
      ·
        refine ⟨14592200591910756695802551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728133727940504463868367 14592200591910756695802551)
        ·
          refine ⟨21888300887866135043703827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592200591910756695802551 21888300887866135043703827)
          ·
            refine ⟨32832451331799202565555741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21888300887866135043703827 32832451331799202565555741)
            ·
              refine ⟨12312169249424700962083403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32832451331799202565555741 12312169249424700962083403)
              ·
                refine ⟨18468253874137051443125105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12312169249424700962083403 18468253874137051443125105)
                ·
                  refine ⟨13851190405602788582343829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18468253874137051443125105 13851190405602788582343829)
                  ·
                    refine ⟨649274550262630714797367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13851190405602788582343829 649274550262630714797367)
                    ·
                      rfl

theorem cell23_3793373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3793373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793373 prefixEnd_3793373 := by exact prefixLift 3793373
  have htrace : WordTrace (prefixWord ++ tailWord_3793373) baseStart_3793373 baseEnd_3793373 := by
    simpa [prefixWord, tailWord_3793373, baseEnd_3793373] using wordTrace_append hprefix tailTrace_3793373
  have hstable : (prefixWord ++ tailWord_3793373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793373).length < 2 ^ (prefixWord ++ tailWord_3793373).sum := by decide
  have hdescent : baseEnd_3793373 < baseStart_3793373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793380 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_3793380 : Nat := 118140960795 + 3793380 * 2 ^ 59
def prefixEnd_3793380 : Nat := 4983230072969 + 3 ^ 40 * 3793380 * 2
def baseEnd_3793380 : Nat := 1947827245152473617004569

theorem tailTrace_3793380 : CollatzResearch.WordTrace tailWord_3793380 prefixEnd_3793380 1947827245152473617004569 := by
  unfold tailWord_3793380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69177967498619796285260797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92237289998159728380347729 69177967498619796285260797)
  ·
    refine ⟨25941737811982423606972799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69177967498619796285260797 25941737811982423606972799)
    ·
      refine ⟨38912606717973635410459199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25941737811982423606972799 38912606717973635410459199)
      ·
        refine ⟨58368910076960453115688799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38912606717973635410459199 58368910076960453115688799)
        ·
          refine ⟨87553365115440679673533199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58368910076960453115688799 87553365115440679673533199)
          ·
            refine ⟨131330047673161019510299799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87553365115440679673533199 131330047673161019510299799)
            ·
              refine ⟨196995071509741529265449699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131330047673161019510299799 196995071509741529265449699)
              ·
                refine ⟨295492607264612293898174549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196995071509741529265449699 295492607264612293898174549)
                ·
                  refine ⟨3462803991382175319119233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 295492607264612293898174549 3462803991382175319119233)
                  ·
                    refine ⟨2597102993536631489339425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462803991382175319119233 2597102993536631489339425)
                    ·
                      refine ⟨1947827245152473617004569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597102993536631489339425 1947827245152473617004569)
                      ·
                        rfl

theorem cell23_3793380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_3793380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793380 prefixEnd_3793380 := by exact prefixLift 3793380
  have htrace : WordTrace (prefixWord ++ tailWord_3793380) baseStart_3793380 baseEnd_3793380 := by
    simpa [prefixWord, tailWord_3793380, baseEnd_3793380] using wordTrace_append hprefix tailTrace_3793380
  have hstable : (prefixWord ++ tailWord_3793380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793380).length < 2 ^ (prefixWord ++ tailWord_3793380).sum := by decide
  have hdescent : baseEnd_3793380 < baseStart_3793380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793383 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3793383 : Nat := 118140960795 + 3793383 * 2 ^ 59
def prefixEnd_3793383 : Nat := 4983230072969 + 3 ^ 40 * 3793383 * 2
def baseEnd_3793383 : Nat := 1947828785594437105267055

theorem tailTrace_3793383 : CollatzResearch.WordTrace tailWord_3793383 prefixEnd_3793383 1947828785594437105267055 := by
  unfold tailWord_3793383
  simp only [CollatzResearch.WordTrace]
  refine ⟨138356044416228724082880803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92237362944152482721920535 138356044416228724082880803)
  ·
    refine ⟨207534066624343086124321205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138356044416228724082880803 207534066624343086124321205)
    ·
      refine ⟨19456318746032164324155113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207534066624343086124321205 19456318746032164324155113)
      ·
        refine ⟨14592239059524123243116335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19456318746032164324155113 14592239059524123243116335)
        ·
          refine ⟨21888358589286184864674503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592239059524123243116335 21888358589286184864674503)
          ·
            refine ⟨32832537883929277297011755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21888358589286184864674503 32832537883929277297011755)
            ·
              refine ⟨49248806825893915945517633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32832537883929277297011755 49248806825893915945517633)
              ·
                refine ⟨36936605119420436959138225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49248806825893915945517633 36936605119420436959138225)
                ·
                  refine ⟨27702453839565327719353669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36936605119420436959138225 27702453839565327719353669)
                  ·
                    refine ⟨5194210094918498947378813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27702453839565327719353669 5194210094918498947378813)
                    ·
                      refine ⟨1947828785594437105267055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194210094918498947378813 1947828785594437105267055)
                      ·
                        rfl

theorem cell23_3793383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3793383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793383 prefixEnd_3793383 := by exact prefixLift 3793383
  have htrace : WordTrace (prefixWord ++ tailWord_3793383) baseStart_3793383 baseEnd_3793383 := by
    simpa [prefixWord, tailWord_3793383, baseEnd_3793383] using wordTrace_append hprefix tailTrace_3793383
  have hstable : (prefixWord ++ tailWord_3793383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793383).length < 2 ^ (prefixWord ++ tailWord_3793383).sum := by decide
  have hdescent : baseEnd_3793383 < baseStart_3793383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793413 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_3793413 : Nat := 118140960795 + 3793413 * 2 ^ 59
def prefixEnd_3793413 : Nat := 4983230072969 + 3 ^ 40 * 3793413 * 2
def baseEnd_3793413 : Nat := 1947844190014071987891917

theorem tailTrace_3793413 : CollatzResearch.WordTrace tailWord_3793413 prefixEnd_3793413 1947844190014071987891917 := by
  unfold tailWord_3793413
  simp only [CollatzResearch.WordTrace]
  refine ⟨138357138606120039206472893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92238092404080026137648595 138357138606120039206472893)
  ·
    refine ⟨51883926977295014702427335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138357138606120039206472893 51883926977295014702427335)
    ·
      refine ⟨77825890465942522053641003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51883926977295014702427335 77825890465942522053641003)
      ·
        refine ⟨116738835698913783080461505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77825890465942522053641003 116738835698913783080461505)
        ·
          refine ⟨87554126774185337310346129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116738835698913783080461505 87554126774185337310346129)
          ·
            refine ⟨65665595080639002982759597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87554126774185337310346129 65665595080639002982759597)
            ·
              refine ⟨24624598155239626118534849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65665595080639002982759597 24624598155239626118534849)
              ·
                refine ⟨18468448616429719588901137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24624598155239626118534849 18468448616429719588901137)
                ·
                  refine ⟨13851336462322289691675853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18468448616429719588901137 13851336462322289691675853)
                  ·
                    refine ⟨5194251173370858634378445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13851336462322289691675853 5194251173370858634378445)
                    ·
                      refine ⟨1947844190014071987891917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194251173370858634378445 1947844190014071987891917)
                      ·
                        rfl

theorem cell23_3793413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_3793413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793413 prefixEnd_3793413 := by exact prefixLift 3793413
  have htrace : WordTrace (prefixWord ++ tailWord_3793413) baseStart_3793413 baseEnd_3793413 := by
    simpa [prefixWord, tailWord_3793413, baseEnd_3793413] using wordTrace_append hprefix tailTrace_3793413
  have hstable : (prefixWord ++ tailWord_3793413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793413).length < 2 ^ (prefixWord ++ tailWord_3793413).sum := by decide
  have hdescent : baseEnd_3793413 < baseStart_3793413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793420 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 5]
def baseStart_3793420 : Nat := 118140960795 + 3793420 * 2 ^ 59
def prefixEnd_3793420 : Nat := 4983230072969 + 3 ^ 40 * 3793420 * 2
def baseEnd_3793420 : Nat := 216427531597628162278265

theorem tailTrace_3793420 : CollatzResearch.WordTrace tailWord_3793420 prefixEnd_3793420 216427531597628162278265 := by
  unfold tailWord_3793420
  simp only [CollatzResearch.WordTrace]
  refine ⟨69178696958547339700988857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92238262611396452934651809 69178696958547339700988857)
  ·
    refine ⟨51884022718910504775741643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69178696958547339700988857 51884022718910504775741643)
    ·
      refine ⟨77826034078365757163612465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51884022718910504775741643 77826034078365757163612465)
      ·
        refine ⟨58369525558774317872709349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77826034078365757163612465 58369525558774317872709349)
        ·
          refine ⟨10944286042270184601133003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58369525558774317872709349 10944286042270184601133003)
          ·
            refine ⟨16416429063405276901699505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944286042270184601133003 16416429063405276901699505)
            ·
              refine ⟨12312321797553957676274629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16416429063405276901699505 12312321797553957676274629)
              ·
                refine ⟨2308560337041367064301493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12312321797553957676274629 2308560337041367064301493)
                ·
                  refine ⟨216427531597628162278265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308560337041367064301493 216427531597628162278265)
                  ·
                    rfl

theorem cell23_3793420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_3793420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793420 prefixEnd_3793420 := by exact prefixLift 3793420
  have htrace : WordTrace (prefixWord ++ tailWord_3793420) baseStart_3793420 baseEnd_3793420 := by
    simpa [prefixWord, tailWord_3793420, baseEnd_3793420] using wordTrace_append hprefix tailTrace_3793420
  have hstable : (prefixWord ++ tailWord_3793420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793420).length < 2 ^ (prefixWord ++ tailWord_3793420).sum := by decide
  have hdescent : baseEnd_3793420 < baseStart_3793420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793431 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3793431 : Nat := 118140960795 + 3793431 * 2 ^ 59
def prefixEnd_3793431 : Nat := 4983230072969 + 3 ^ 40 * 3793431 * 2
def baseEnd_3793431 : Nat := 1947853432665852917466835

theorem tailTrace_3793431 : CollatzResearch.WordTrace tailWord_3793431 prefixEnd_3793431 1947853432665852917466835 := by
  unfold tailWord_3793431
  simp only [CollatzResearch.WordTrace]
  refine ⟨138357795120054828280628147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92238530080036552187085431 138357795120054828280628147)
  ·
    refine ⟨207536692680082242420942221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138357795120054828280628147 207536692680082242420942221)
    ·
      refine ⟨77826259755030840907853333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207536692680082242420942221 77826259755030840907853333)
      ·
        refine ⟨3648105926017070667555625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77826259755030840907853333 3648105926017070667555625)
        ·
          refine ⟨2736079444512803000666719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3648105926017070667555625 2736079444512803000666719)
          ·
            refine ⟨4104119166769204501000079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736079444512803000666719 4104119166769204501000079)
            ·
              refine ⟨6156178750153806751500119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104119166769204501000079 6156178750153806751500119)
              ·
                refine ⟨9234268125230710127250179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156178750153806751500119 9234268125230710127250179)
                ·
                  refine ⟨13851402187846065190875269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9234268125230710127250179 13851402187846065190875269)
                  ·
                    refine ⟨2597137910221137223289113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13851402187846065190875269 2597137910221137223289113)
                    ·
                      refine ⟨1947853432665852917466835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597137910221137223289113 1947853432665852917466835)
                      ·
                        rfl

theorem cell23_3793431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3793431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793431 prefixEnd_3793431 := by exact prefixLift 3793431
  have htrace : WordTrace (prefixWord ++ tailWord_3793431) baseStart_3793431 baseEnd_3793431 := by
    simpa [prefixWord, tailWord_3793431, baseEnd_3793431] using wordTrace_append hprefix tailTrace_3793431
  have hstable : (prefixWord ++ tailWord_3793431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793431).length < 2 ^ (prefixWord ++ tailWord_3793431).sum := by decide
  have hdescent : baseEnd_3793431 < baseStart_3793431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793454 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_3793454 : Nat := 118140960795 + 3793454 * 2 ^ 59
def prefixEnd_3793454 : Nat := 4983230072969 + 3 ^ 40 * 3793454 * 2
def baseEnd_3793454 : Nat := 216429471413434036386581

theorem tailTrace_3793454 : CollatzResearch.WordTrace tailWord_3793454 prefixEnd_3793454 216429471413434036386581 := by
  unfold tailWord_3793454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294829249871437901089427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92239089332647668805810277 17294829249871437901089427)
  ·
    refine ⟨25942243874807156851634141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17294829249871437901089427 25942243874807156851634141)
    ·
      refine ⟨9728341453052683819362803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25942243874807156851634141 9728341453052683819362803)
      ·
        refine ⟨14592512179579025729044205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728341453052683819362803 14592512179579025729044205)
        ·
          refine ⟨5472192067342134648391577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14592512179579025729044205 5472192067342134648391577)
          ·
            refine ⟨4104144050506600986293683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472192067342134648391577 4104144050506600986293683)
            ·
              refine ⟨6156216075759901479440525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104144050506600986293683 6156216075759901479440525)
              ·
                refine ⟨2308581028409963054790197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6156216075759901479440525 2308581028409963054790197)
                ·
                  refine ⟨216429471413434036386581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308581028409963054790197 216429471413434036386581)
                  ·
                    rfl

theorem cell23_3793454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_3793454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793454 prefixEnd_3793454 := by exact prefixLift 3793454
  have htrace : WordTrace (prefixWord ++ tailWord_3793454) baseStart_3793454 baseEnd_3793454 := by
    simpa [prefixWord, tailWord_3793454, baseEnd_3793454] using wordTrace_append hprefix tailTrace_3793454
  have hstable : (prefixWord ++ tailWord_3793454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793454).length < 2 ^ (prefixWord ++ tailWord_3793454).sum := by decide
  have hdescent : baseEnd_3793454 < baseStart_3793454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793490 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3793490 : Nat := 118140960795 + 3793490 * 2 ^ 59
def prefixEnd_3793490 : Nat := 4983230072969 + 3 ^ 40 * 3793490 * 2
def baseEnd_3793490 : Nat := 1947883728024468186629063

theorem tailTrace_3793490 : CollatzResearch.WordTrace tailWord_3793490 prefixEnd_3793490 1947883728024468186629063 := by
  unfold tailWord_3793490
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589986756710270339256481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92239964684560720904683949 34589986756710270339256481)
  ·
    refine ⟨25942490067532702754442361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34589986756710270339256481 25942490067532702754442361)
    ·
      refine ⟨19456867550649527065831771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25942490067532702754442361 19456867550649527065831771)
      ·
        refine ⟨29185301325974290598747657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19456867550649527065831771 29185301325974290598747657)
        ·
          refine ⟨21888975994480717949060743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29185301325974290598747657 21888975994480717949060743)
          ·
            refine ⟨32833463991721076923591115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21888975994480717949060743 32833463991721076923591115)
            ·
              refine ⟨49250195987581615385386673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32833463991721076923591115 49250195987581615385386673)
              ·
                refine ⟨36937646990686211539040005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49250195987581615385386673 36937646990686211539040005)
                ·
                  refine ⟨6925808810753664663570001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36937646990686211539040005 6925808810753664663570001)
                  ·
                    refine ⟨5194356608065248497677501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6925808810753664663570001 5194356608065248497677501)
                    ·
                      refine ⟨1947883728024468186629063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194356608065248497677501 1947883728024468186629063)
                      ·
                        rfl

theorem cell23_3793490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3793490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793490 prefixEnd_3793490 := by exact prefixLift 3793490
  have htrace : WordTrace (prefixWord ++ tailWord_3793490) baseStart_3793490 baseEnd_3793490 := by
    simpa [prefixWord, tailWord_3793490, baseEnd_3793490] using wordTrace_append hprefix tailTrace_3793490
  have hstable : (prefixWord ++ tailWord_3793490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793490).length < 2 ^ (prefixWord ++ tailWord_3793490).sum := by decide
  have hdescent : baseEnd_3793490 < baseStart_3793490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793503 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_3793503 : Nat := 118140960795 + 3793503 * 2 ^ 59
def prefixEnd_3793503 : Nat := 4983230072969 + 3 ^ 40 * 3793503 * 2
def baseEnd_3793503 : Nat := 1947890403272976635766503

theorem tailTrace_3793503 : CollatzResearch.WordTrace tailWord_3793503 prefixEnd_3793503 1947890403272976635766503 := by
  unfold tailWord_3793503
  simp only [CollatzResearch.WordTrace]
  refine ⟨138360421175793984577249163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92240280783862656384832775 138360421175793984577249163)
  ·
    refine ⟨207540631763690976865873745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138360421175793984577249163 207540631763690976865873745)
    ·
      refine ⟨155655473822768232649405309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207540631763690976865873745 155655473822768232649405309)
      ·
        refine ⟨58370802683538087243526991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155655473822768232649405309 58370802683538087243526991)
        ·
          refine ⟨87556204025307130865290487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58370802683538087243526991 87556204025307130865290487)
          ·
            refine ⟨131334306037960696297935731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87556204025307130865290487 131334306037960696297935731)
            ·
              refine ⟨197001459056941044446903597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131334306037960696297935731 197001459056941044446903597)
              ·
                refine ⟨73875547146352891667588849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197001459056941044446903597 73875547146352891667588849)
                ·
                  refine ⟨55406660359764668750691637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73875547146352891667588849 55406660359764668750691637)
                  ·
                    refine ⟨5194374408727937695377341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55406660359764668750691637 5194374408727937695377341)
                    ·
                      refine ⟨1947890403272976635766503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194374408727937695377341 1947890403272976635766503)
                      ·
                        rfl

theorem cell23_3793503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_3793503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793503 prefixEnd_3793503 := by exact prefixLift 3793503
  have htrace : WordTrace (prefixWord ++ tailWord_3793503) baseStart_3793503 baseEnd_3793503 := by
    simpa [prefixWord, tailWord_3793503, baseEnd_3793503] using wordTrace_append hprefix tailTrace_3793503
  have hstable : (prefixWord ++ tailWord_3793503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793503).length < 2 ^ (prefixWord ++ tailWord_3793503).sum := by decide
  have hdescent : baseEnd_3793503 < baseStart_3793503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793537 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3793537 : Nat := 118140960795 + 3793537 * 2 ^ 59
def prefixEnd_3793537 : Nat := 4983230072969 + 3 ^ 40 * 3793537 * 2
def baseEnd_3793537 : Nat := 1947907861615229502741347

theorem tailTrace_3793537 : CollatzResearch.WordTrace tailWord_3793537 prefixEnd_3793537 1947907861615229502741347 := by
  unfold tailWord_3793537
  simp only [CollatzResearch.WordTrace]
  refine ⟨138361661257670808383986865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92241107505113872255991243 138361661257670808383986865)
  ·
    refine ⟨103771245943253106287990149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138361661257670808383986865 103771245943253106287990149)
    ·
      refine ⟨19457108614359957428998153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103771245943253106287990149 19457108614359957428998153)
      ·
        refine ⟨14592831460769968071748615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19457108614359957428998153 14592831460769968071748615)
        ·
          refine ⟨21889247191154952107622923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592831460769968071748615 21889247191154952107622923)
          ·
            refine ⟨32833870786732428161434385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21889247191154952107622923 32833870786732428161434385)
            ·
              refine ⟨24625403090049321121075789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32833870786732428161434385 24625403090049321121075789)
              ·
                refine ⟨9234526158768495420403421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24625403090049321121075789 9234526158768495420403421)
                ·
                  refine ⟨3462947309538185782651283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9234526158768495420403421 3462947309538185782651283)
                  ·
                    refine ⟨5194420964307278673976925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462947309538185782651283 5194420964307278673976925)
                    ·
                      refine ⟨1947907861615229502741347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194420964307278673976925 1947907861615229502741347)
                      ·
                        rfl

theorem cell23_3793537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3793537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793537 prefixEnd_3793537 := by exact prefixLift 3793537
  have htrace : WordTrace (prefixWord ++ tailWord_3793537) baseStart_3793537 baseEnd_3793537 := by
    simpa [prefixWord, tailWord_3793537, baseEnd_3793537] using wordTrace_append hprefix tailTrace_3793537
  have hstable : (prefixWord ++ tailWord_3793537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793537).length < 2 ^ (prefixWord ++ tailWord_3793537).sum := by decide
  have hdescent : baseEnd_3793537 < baseStart_3793537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793538 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3793538 : Nat := 118140960795 + 3793538 * 2 ^ 59
def prefixEnd_3793538 : Nat := 4983230072969 + 3 ^ 40 * 3793538 * 2
def baseEnd_3793538 : Nat := 1947908375095883998828843

theorem tailTrace_3793538 : CollatzResearch.WordTrace tailWord_3793538 prefixEnd_3793538 1947908375095883998828843 := by
  unfold tailWord_3793538
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590424432666796388693317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92241131820444790369848845 34590424432666796388693317)
  ·
    refine ⟨6485704581125024322879997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34590424432666796388693317 6485704581125024322879997)
    ·
      refine ⟨2432139217921884121079999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6485704581125024322879997 2432139217921884121079999)
      ·
        refine ⟨3648208826882826181619999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432139217921884121079999 3648208826882826181619999)
        ·
          refine ⟨5472313240324239272429999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648208826882826181619999 5472313240324239272429999)
          ·
            refine ⟨8208469860486358908644999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472313240324239272429999 8208469860486358908644999)
            ·
              refine ⟨12312704790729538362967499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208469860486358908644999 12312704790729538362967499)
              ·
                refine ⟨18469057186094307544451249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12312704790729538362967499 18469057186094307544451249)
                ·
                  refine ⟨13851792889570730658338437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18469057186094307544451249 13851792889570730658338437)
                  ·
                    refine ⟨2597211166794511998438457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13851792889570730658338437 2597211166794511998438457)
                    ·
                      refine ⟨1947908375095883998828843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597211166794511998438457 1947908375095883998828843)
                      ·
                        rfl

theorem cell23_3793538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3793538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793538 prefixEnd_3793538 := by exact prefixLift 3793538
  have htrace : WordTrace (prefixWord ++ tailWord_3793538) baseStart_3793538 baseEnd_3793538 := by
    simpa [prefixWord, tailWord_3793538, baseEnd_3793538] using wordTrace_append hprefix tailTrace_3793538
  have hstable : (prefixWord ++ tailWord_3793538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793538).length < 2 ^ (prefixWord ++ tailWord_3793538).sum := by decide
  have hdescent : baseEnd_3793538 < baseStart_3793538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793540 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3793540 : Nat := 118140960795 + 3793540 * 2 ^ 59
def prefixEnd_3793540 : Nat := 4983230072969 + 3 ^ 40 * 3793540 * 2
def baseEnd_3793540 : Nat := 649303134019064330334611

theorem tailTrace_3793540 : CollatzResearch.WordTrace tailWord_3793540 prefixEnd_3793540 649303134019064330334611 := by
  unfold tailWord_3793540
  simp only [CollatzResearch.WordTrace]
  refine ⟨69180885338329969948173037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92241180451106626597564049 69180885338329969948173037)
  ·
    refine ⟨25942832001873738730564889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69180885338329969948173037 25942832001873738730564889)
    ·
      refine ⟨19457124001405304047923667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25942832001873738730564889 19457124001405304047923667)
      ·
        refine ⟨29185686002107956071885501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19457124001405304047923667 29185686002107956071885501)
        ·
          refine ⟨10944632250790483526957063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29185686002107956071885501 10944632250790483526957063)
          ·
            refine ⟨16416948376185725290435595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944632250790483526957063 16416948376185725290435595)
            ·
              refine ⟨24625422564278587935653393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16416948376185725290435595 24625422564278587935653393)
              ·
                refine ⟨18469066923208940951740045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24625422564278587935653393 18469066923208940951740045)
                ·
                  refine ⟨6925900096203352856902517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18469066923208940951740045 6925900096203352856902517)
                  ·
                    refine ⟨649303134019064330334611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6925900096203352856902517 649303134019064330334611)
                    ·
                      rfl

theorem cell23_3793540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3793540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793540 prefixEnd_3793540 := by exact prefixLift 3793540
  have htrace : WordTrace (prefixWord ++ tailWord_3793540) baseStart_3793540 baseEnd_3793540 := by
    simpa [prefixWord, tailWord_3793540, baseEnd_3793540] using wordTrace_append hprefix tailTrace_3793540
  have hstable : (prefixWord ++ tailWord_3793540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793540).length < 2 ^ (prefixWord ++ tailWord_3793540).sum := by decide
  have hdescent : baseEnd_3793540 < baseStart_3793540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793554 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3793554 : Nat := 118140960795 + 3793554 * 2 ^ 59
def prefixEnd_3793554 : Nat := 4983230072969 + 3 ^ 40 * 3793554 * 2
def baseEnd_3793554 : Nat := 1947916590786355936228769

theorem tailTrace_3793554 : CollatzResearch.WordTrace tailWord_3793554 prefixEnd_3793554 1947916590786355936228769 := by
  unfold tailWord_3793554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590570324652305071838929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92241520865739480191570477 34590570324652305071838929)
  ·
    refine ⟨25942927743489228803879197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34590570324652305071838929 25942927743489228803879197)
    ·
      refine ⟨9728597903808460801454699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25942927743489228803879197 9728597903808460801454699)
      ·
        refine ⟨14592896855712691202182049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728597903808460801454699 14592896855712691202182049)
        ·
          refine ⟨10944672641784518401636537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14592896855712691202182049 10944672641784518401636537)
          ·
            refine ⟨8208504481338388801227403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10944672641784518401636537 8208504481338388801227403)
            ·
              refine ⟨12312756722007583201841105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208504481338388801227403 12312756722007583201841105)
              ·
                refine ⟨9234567541505687401380829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12312756722007583201841105 9234567541505687401380829)
                ·
                  refine ⟨3462962828064632775517811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9234567541505687401380829 3462962828064632775517811)
                  ·
                    refine ⟨5194444242096949163276717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462962828064632775517811 5194444242096949163276717)
                    ·
                      refine ⟨1947916590786355936228769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194444242096949163276717 1947916590786355936228769)
                      ·
                        rfl

theorem cell23_3793554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3793554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793554 prefixEnd_3793554 := by exact prefixLift 3793554
  have htrace : WordTrace (prefixWord ++ tailWord_3793554) baseStart_3793554 baseEnd_3793554 := by
    simpa [prefixWord, tailWord_3793554, baseEnd_3793554] using wordTrace_append hprefix tailTrace_3793554
  have hstable : (prefixWord ++ tailWord_3793554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793554).length < 2 ^ (prefixWord ++ tailWord_3793554).sum := by decide
  have hdescent : baseEnd_3793554 < baseStart_3793554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793560 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3793560 : Nat := 118140960795 + 3793560 * 2 ^ 59
def prefixEnd_3793560 : Nat := 4983230072969 + 3 ^ 40 * 3793560 * 2
def baseEnd_3793560 : Nat := 1947919671670282912753741

theorem tailTrace_3793560 : CollatzResearch.WordTrace tailWord_3793560 prefixEnd_3793560 1947919671670282912753741 := by
  unfold tailWord_3793560
  simp only [CollatzResearch.WordTrace]
  refine ⟨69181250068293741656037067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92241666757724988874716089 69181250068293741656037067)
  ·
    refine ⟨103771875102440612484055601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69181250068293741656037067 103771875102440612484055601)
    ·
      refine ⟨77828906326830459363041701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103771875102440612484055601 77828906326830459363041701)
      ·
        refine ⟨14592919936280711130570319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77828906326830459363041701 14592919936280711130570319)
        ·
          refine ⟨21889379904421066695855479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592919936280711130570319 21889379904421066695855479)
          ·
            refine ⟨32834069856631600043783219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21889379904421066695855479 32834069856631600043783219)
            ·
              refine ⟨49251104784947400065674829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32834069856631600043783219 49251104784947400065674829)
              ·
                refine ⟨18469164294355275024628061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49251104784947400065674829 18469164294355275024628061)
                ·
                  refine ⟨6925936610383228134235523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18469164294355275024628061 6925936610383228134235523)
                  ·
                    refine ⟨10388904915574842201353285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6925936610383228134235523 10388904915574842201353285)
                    ·
                      refine ⟨1947919671670282912753741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10388904915574842201353285 1947919671670282912753741)
                      ·
                        rfl

theorem cell23_3793560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3793560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793560 prefixEnd_3793560 := by exact prefixLift 3793560
  have htrace : WordTrace (prefixWord ++ tailWord_3793560) baseStart_3793560 baseEnd_3793560 := by
    simpa [prefixWord, tailWord_3793560, baseEnd_3793560] using wordTrace_append hprefix tailTrace_3793560
  have hstable : (prefixWord ++ tailWord_3793560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793560).length < 2 ^ (prefixWord ++ tailWord_3793560).sum := by decide
  have hdescent : baseEnd_3793560 < baseStart_3793560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793564 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3793564 : Nat := 118140960795 + 3793564 * 2 ^ 59
def prefixEnd_3793564 : Nat := 4983230072969 + 3 ^ 40 * 3793564 * 2
def baseEnd_3793564 : Nat := 1947921725592900897103723

theorem tailTrace_3793564 : CollatzResearch.WordTrace tailWord_3793564 prefixEnd_3793564 1947921725592900897103723 := by
  unfold tailWord_3793564
  simp only [CollatzResearch.WordTrace]
  refine ⟨69181323014286495997609873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92241764019048661330146497 69181323014286495997609873)
  ·
    refine ⟨51885992260714871998207405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69181323014286495997609873 51885992260714871998207405)
    ·
      refine ⟨19457247097768076999327777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51885992260714871998207405 19457247097768076999327777)
      ·
        refine ⟨14592935323326057749495833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19457247097768076999327777 14592935323326057749495833)
        ·
          refine ⟨10944701492494543312121875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14592935323326057749495833 10944701492494543312121875)
          ·
            refine ⟨16417052238741814968182813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944701492494543312121875 16417052238741814968182813)
            ·
              refine ⟨6156394589528180613068555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16417052238741814968182813 6156394589528180613068555)
              ·
                refine ⟨9234591884292270919602833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156394589528180613068555 9234591884292270919602833)
                ·
                  refine ⟨6925943913219203189702125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9234591884292270919602833 6925943913219203189702125)
                  ·
                    refine ⟨2597228967457201196138297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6925943913219203189702125 2597228967457201196138297)
                    ·
                      refine ⟨1947921725592900897103723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597228967457201196138297 1947921725592900897103723)
                      ·
                        rfl

theorem cell23_3793564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3793564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793564 prefixEnd_3793564 := by exact prefixLift 3793564
  have htrace : WordTrace (prefixWord ++ tailWord_3793564) baseStart_3793564 baseEnd_3793564 := by
    simpa [prefixWord, tailWord_3793564, baseEnd_3793564] using wordTrace_append hprefix tailTrace_3793564
  have hstable : (prefixWord ++ tailWord_3793564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793564).length < 2 ^ (prefixWord ++ tailWord_3793564).sum := by decide
  have hdescent : baseEnd_3793564 < baseStart_3793564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793573 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3793573 : Nat := 118140960795 + 3793573 * 2 ^ 59
def prefixEnd_3793573 : Nat := 4983230072969 + 3 ^ 40 * 3793573 * 2
def baseEnd_3793573 : Nat := 1947926346918791361891181

theorem tailTrace_3793573 : CollatzResearch.WordTrace tailWord_3793573 prefixEnd_3793573 1947926346918791361891181 := by
  unfold tailWord_3793573
  simp only [CollatzResearch.WordTrace]
  refine ⟨138362974285540386532297373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92241982857026924354864915 138362974285540386532297373)
  ·
    refine ⟨51886115357077644949611515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138362974285540386532297373 51886115357077644949611515)
    ·
      refine ⟨77829173035616467424417273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51886115357077644949611515 77829173035616467424417273)
      ·
        refine ⟨58371879776712350568312955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77829173035616467424417273 58371879776712350568312955)
        ·
          refine ⟨87557819665068525852469433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58371879776712350568312955 87557819665068525852469433)
          ·
            refine ⟨65668364748801394389352075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87557819665068525852469433 65668364748801394389352075)
            ·
              refine ⟨98502547123202091584028113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65668364748801394389352075 98502547123202091584028113)
              ·
                refine ⟨73876910342401568688021085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98502547123202091584028113 73876910342401568688021085)
                ·
                  refine ⟨27703841378400588258007907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73876910342401568688021085 27703841378400588258007907)
                  ·
                    refine ⟨41555762067600882387011861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27703841378400588258007907 41555762067600882387011861)
                    ·
                      refine ⟨1947926346918791361891181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41555762067600882387011861 1947926346918791361891181)
                      ·
                        rfl

theorem cell23_3793573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3793573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793573 prefixEnd_3793573 := by exact prefixLift 3793573
  have htrace : WordTrace (prefixWord ++ tailWord_3793573) baseStart_3793573 baseEnd_3793573 := by
    simpa [prefixWord, tailWord_3793573, baseEnd_3793573] using wordTrace_append hprefix tailTrace_3793573
  have hstable : (prefixWord ++ tailWord_3793573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793573).length < 2 ^ (prefixWord ++ tailWord_3793573).sum := by decide
  have hdescent : baseEnd_3793573 < baseStart_3793573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793583 : List Nat := [1, 1, 2, 1, 2, 6, 10]
def baseStart_3793583 : Nat := 118140960795 + 3793583 * 2 ^ 59
def prefixEnd_3793583 : Nat := 4983230072969 + 3 ^ 40 * 3793583 * 2
def baseEnd_3793583 : Nat := 24048536811423905219335

theorem tailTrace_3793583 : CollatzResearch.WordTrace tailWord_3793583 prefixEnd_3793583 24048536811423905219335 := by
  unfold tailWord_3793583
  simp only [CollatzResearch.WordTrace]
  refine ⟨138363339015504158240161403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92242226010336105493440935 138363339015504158240161403)
  ·
    refine ⟨207545008523256237360242105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138363339015504158240161403 207545008523256237360242105)
    ·
      refine ⟨155658756392442178020181579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207545008523256237360242105 155658756392442178020181579)
      ·
        refine ⟨233488134588663267030272369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155658756392442178020181579 233488134588663267030272369)
        ·
          refine ⟨175116100941497450272704277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233488134588663267030272369 175116100941497450272704277)
          ·
            refine ⟨8208567231632692981533013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175116100941497450272704277 8208567231632692981533013)
            ·
              refine ⟨24048536811423905219335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8208567231632692981533013 24048536811423905219335)
              ·
                rfl

theorem cell23_3793583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 10].length) (baseStart_3793583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793583 prefixEnd_3793583 := by exact prefixLift 3793583
  have htrace : WordTrace (prefixWord ++ tailWord_3793583) baseStart_3793583 baseEnd_3793583 := by
    simpa [prefixWord, tailWord_3793583, baseEnd_3793583] using wordTrace_append hprefix tailTrace_3793583
  have hstable : (prefixWord ++ tailWord_3793583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793583).length < 2 ^ (prefixWord ++ tailWord_3793583).sum := by decide
  have hdescent : baseEnd_3793583 < baseStart_3793583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793587 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 2, 4]
def baseStart_3793587 : Nat := 118140960795 + 3793587 * 2 ^ 59
def prefixEnd_3793587 : Nat := 4983230072969 + 3 ^ 40 * 3793587 * 2
def baseEnd_3793587 : Nat := 649311178549318102372039

theorem tailTrace_3793587 : CollatzResearch.WordTrace tailWord_3793587 prefixEnd_3793587 649311178549318102372039 := by
  unfold tailWord_3793587
  simp only [CollatzResearch.WordTrace]
  refine ⟨138363484907489666923307015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92242323271659777948871343 138363484907489666923307015)
  ·
    refine ⟨207545227361234500384960523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138363484907489666923307015 207545227361234500384960523)
    ·
      refine ⟨311317841041851750577440785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207545227361234500384960523 311317841041851750577440785)
      ·
        refine ⟨233488380781388812933080589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311317841041851750577440785 233488380781388812933080589)
        ·
          refine ⟨87558142793020804849905221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233488380781388812933080589 87558142793020804849905221)
          ·
            refine ⟨16417151773691400909357229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87558142793020804849905221 16417151773691400909357229)
            ·
              refine ⟨6156431915134275341008961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16417151773691400909357229 6156431915134275341008961)
              ·
                refine ⟨4617323936350706505756721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156431915134275341008961 4617323936350706505756721)
                ·
                  refine ⟨3462992952263029879317541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4617323936350706505756721 3462992952263029879317541)
                  ·
                    refine ⟨649311178549318102372039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3462992952263029879317541 649311178549318102372039)
                    ·
                      rfl

theorem cell23_3793587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 4].length) (baseStart_3793587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793587 prefixEnd_3793587 := by exact prefixLift 3793587
  have htrace : WordTrace (prefixWord ++ tailWord_3793587) baseStart_3793587 baseEnd_3793587 := by
    simpa [prefixWord, tailWord_3793587, baseEnd_3793587] using wordTrace_append hprefix tailTrace_3793587
  have hstable : (prefixWord ++ tailWord_3793587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793587).length < 2 ^ (prefixWord ++ tailWord_3793587).sum := by decide
  have hdescent : baseEnd_3793587 < baseStart_3793587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793593 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3793593 : Nat := 118140960795 + 3793593 * 2 ^ 59
def prefixEnd_3793593 : Nat := 4983230072969 + 3 ^ 40 * 3793593 * 2
def baseEnd_3793593 : Nat := 1947936616531881283641089

theorem tailTrace_3793593 : CollatzResearch.WordTrace tailWord_3793593 prefixEnd_3793593 1947936616531881283641089 := by
  unfold tailWord_3793593
  simp only [CollatzResearch.WordTrace]
  refine ⟨138363703745467929948025433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92242469163645286632016955 138363703745467929948025433)
  ·
    refine ⟨103772777809100947461019075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138363703745467929948025433 103772777809100947461019075)
    ·
      refine ⟨155659166713651421191528613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103772777809100947461019075 155659166713651421191528613)
      ·
        refine ⟨29186093758809641473411615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155659166713651421191528613 29186093758809641473411615)
        ·
          refine ⟨43779140638214462210117423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29186093758809641473411615 43779140638214462210117423)
          ·
            refine ⟨65668710957321693315176135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43779140638214462210117423 65668710957321693315176135)
            ·
              refine ⟨98503066435982539972764203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65668710957321693315176135 98503066435982539972764203)
              ·
                refine ⟨147754599653973809959146305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98503066435982539972764203 147754599653973809959146305)
                ·
                  refine ⟨110815949740480357469359729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147754599653973809959146305 110815949740480357469359729)
                  ·
                    refine ⟨83111962305360268102019797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110815949740480357469359729 83111962305360268102019797)
                    ·
                      refine ⟨1947936616531881283641089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83111962305360268102019797 1947936616531881283641089)
                      ·
                        rfl

theorem cell23_3793593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3793593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793593 prefixEnd_3793593 := by exact prefixLift 3793593
  have htrace : WordTrace (prefixWord ++ tailWord_3793593) baseStart_3793593 baseEnd_3793593 := by
    simpa [prefixWord, tailWord_3793593, baseEnd_3793593] using wordTrace_append hprefix tailTrace_3793593
  have hstable : (prefixWord ++ tailWord_3793593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793593).length < 2 ^ (prefixWord ++ tailWord_3793593).sum := by decide
  have hdescent : baseEnd_3793593 < baseStart_3793593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793594 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2]
def baseStart_3793594 : Nat := 118140960795 + 3793594 * 2 ^ 59
def prefixEnd_3793594 : Nat := 4983230072969 + 3 ^ 40 * 3793594 * 2
def baseEnd_3793594 : Nat := 1947937130012535779728585

theorem tailTrace_3793594 : CollatzResearch.WordTrace tailWord_3793594 prefixEnd_3793594 1947937130012535779728585 := by
  unfold tailWord_3793594
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590935054616076779702959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92242493478976204745874557 34590935054616076779702959)
  ·
    refine ⟨51886402581924115169554439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34590935054616076779702959 51886402581924115169554439)
    ·
      refine ⟨77829603872886172754331659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51886402581924115169554439 77829603872886172754331659)
      ·
        refine ⟨116744405809329259131497489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77829603872886172754331659 116744405809329259131497489)
        ·
          refine ⟨87558304356996944348623117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116744405809329259131497489 87558304356996944348623117)
          ·
            refine ⟨32834364133873854130733669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87558304356996944348623117 32834364133873854130733669)
            ·
              refine ⟨6156443275101347649512563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32834364133873854130733669 6156443275101347649512563)
              ·
                refine ⟨9234664912652021474268845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156443275101347649512563 9234664912652021474268845)
                ·
                  refine ⟨3462999342244508052850817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9234664912652021474268845 3462999342244508052850817)
                  ·
                    refine ⟨2597249506683381039638113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462999342244508052850817 2597249506683381039638113)
                    ·
                      refine ⟨1947937130012535779728585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597249506683381039638113 1947937130012535779728585)
                      ·
                        rfl

theorem cell23_3793594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_3793594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793594 prefixEnd_3793594 := by exact prefixLift 3793594
  have htrace : WordTrace (prefixWord ++ tailWord_3793594) baseStart_3793594 baseEnd_3793594 := by
    simpa [prefixWord, tailWord_3793594, baseEnd_3793594] using wordTrace_append hprefix tailTrace_3793594
  have hstable : (prefixWord ++ tailWord_3793594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793594).length < 2 ^ (prefixWord ++ tailWord_3793594).sum := by decide
  have hdescent : baseEnd_3793594 < baseStart_3793594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793614 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3793614 : Nat := 118140960795 + 3793614 * 2 ^ 59
def prefixEnd_3793614 : Nat := 4983230072969 + 3 ^ 40 * 3793614 * 2
def baseEnd_3793614 : Nat := 1947947399625625701478493

theorem tailTrace_3793614 : CollatzResearch.WordTrace tailWord_3793614 prefixEnd_3793614 1947947399625625701478493 := by
  unfold tailWord_3793614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295558709798981316817487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92242979785594567023026597 17295558709798981316817487)
  ·
    refine ⟨25943338064698471975226231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17295558709798981316817487 25943338064698471975226231)
    ·
      refine ⟨38915007097047707962839347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25943338064698471975226231 38915007097047707962839347)
      ·
        refine ⟨58372510645571561944259021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38915007097047707962839347 58372510645571561944259021)
        ·
          refine ⟨21889691492089335729097133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58372510645571561944259021 21889691492089335729097133)
          ·
            refine ⟨8208634309533500898411425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21889691492089335729097133 8208634309533500898411425)
            ·
              refine ⟨6156475732150125673808569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8208634309533500898411425 6156475732150125673808569)
              ·
                refine ⟨4617356799112594255356427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156475732150125673808569 4617356799112594255356427)
                ·
                  refine ⟨6926035198668891383034641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617356799112594255356427 6926035198668891383034641)
                  ·
                    refine ⟨5194526399001668537275981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6926035198668891383034641 5194526399001668537275981)
                    ·
                      refine ⟨1947947399625625701478493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194526399001668537275981 1947947399625625701478493)
                      ·
                        rfl

theorem cell23_3793614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3793614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793614 prefixEnd_3793614 := by exact prefixLift 3793614
  have htrace : WordTrace (prefixWord ++ tailWord_3793614) baseStart_3793614 baseEnd_3793614 := by
    simpa [prefixWord, tailWord_3793614, baseEnd_3793614] using wordTrace_append hprefix tailTrace_3793614
  have hstable : (prefixWord ++ tailWord_3793614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793614).length < 2 ^ (prefixWord ++ tailWord_3793614).sum := by decide
  have hdescent : baseEnd_3793614 < baseStart_3793614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793654 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_3793654 : Nat := 118140960795 + 3793654 * 2 ^ 59
def prefixEnd_3793654 : Nat := 4983230072969 + 3 ^ 40 * 3793654 * 2
def baseEnd_3793654 : Nat := 1947967938851805544978309

theorem tailTrace_3793654 : CollatzResearch.WordTrace tailWord_3793654 prefixEnd_3793654 1947967938851805544978309 := by
  unfold tailWord_3793654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8647870537390433585374751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92243952398831291577330677 8647870537390433585374751)
  ·
    refine ⟨12971805806085650378062127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8647870537390433585374751 12971805806085650378062127)
    ·
      refine ⟨19457708709128475567093191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12971805806085650378062127 19457708709128475567093191)
      ·
        refine ⟨29186563063692713350639787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19457708709128475567093191 29186563063692713350639787)
        ·
          refine ⟨43779844595539070025959681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29186563063692713350639787 43779844595539070025959681)
          ·
            refine ⟨32834883446654302519469761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43779844595539070025959681 32834883446654302519469761)
            ·
              refine ⟨24626162584990726889602321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32834883446654302519469761 24626162584990726889602321)
              ·
                refine ⟨18469621938743045167201741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24626162584990726889602321 18469621938743045167201741)
                ·
                  refine ⟨6926108227028641937700653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18469621938743045167201741 6926108227028641937700653)
                  ·
                    refine ⟨2597290585135740726637745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6926108227028641937700653 2597290585135740726637745)
                    ·
                      refine ⟨1947967938851805544978309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597290585135740726637745 1947967938851805544978309)
                      ·
                        rfl

theorem cell23_3793654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_3793654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793654 prefixEnd_3793654 := by exact prefixLift 3793654
  have htrace : WordTrace (prefixWord ++ tailWord_3793654) baseStart_3793654 baseEnd_3793654 := by
    simpa [prefixWord, tailWord_3793654, baseEnd_3793654] using wordTrace_append hprefix tailTrace_3793654
  have hstable : (prefixWord ++ tailWord_3793654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793654).length < 2 ^ (prefixWord ++ tailWord_3793654).sum := by decide
  have hdescent : baseEnd_3793654 < baseStart_3793654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793667 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 1, 4, 2]
def baseStart_3793667 : Nat := 118140960795 + 3793667 * 2 ^ 59
def prefixEnd_3793667 : Nat := 4983230072969 + 3 ^ 40 * 3793667 * 2
def baseEnd_3793667 : Nat := 1947974614100313994115749

theorem tailTrace_3793667 : CollatzResearch.WordTrace tailWord_3793667 prefixEnd_3793667 1947974614100313994115749 := by
  unfold tailWord_3793667
  simp only [CollatzResearch.WordTrace]
  refine ⟨138366402747199840586219255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92244268498133227057479503 138366402747199840586219255)
  ·
    refine ⟨207549604120799760879328883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138366402747199840586219255 207549604120799760879328883)
    ·
      refine ⟨311324406181199641318993325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207549604120799760879328883 311324406181199641318993325)
      ·
        refine ⟨116746652317949865494622497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311324406181199641318993325 116746652317949865494622497)
        ·
          refine ⟨87559989238462399120966873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116746652317949865494622497 87559989238462399120966873)
          ·
            refine ⟨65669991928846799340725155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87559989238462399120966873 65669991928846799340725155)
            ·
              refine ⟨98504987893270199011087733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65669991928846799340725155 98504987893270199011087733)
              ·
                refine ⟨9234842614994081157289475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98504987893270199011087733 9234842614994081157289475)
                ·
                  refine ⟨13852263922491121735934213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9234842614994081157289475 13852263922491121735934213)
                  ·
                    refine ⟨2597299485467085325487665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13852263922491121735934213 2597299485467085325487665)
                    ·
                      refine ⟨1947974614100313994115749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597299485467085325487665 1947974614100313994115749)
                      ·
                        rfl

theorem cell23_3793667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_3793667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793667 prefixEnd_3793667 := by exact prefixLift 3793667
  have htrace : WordTrace (prefixWord ++ tailWord_3793667) baseStart_3793667 baseEnd_3793667 := by
    simpa [prefixWord, tailWord_3793667, baseEnd_3793667] using wordTrace_append hprefix tailTrace_3793667
  have hstable : (prefixWord ++ tailWord_3793667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793667).length < 2 ^ (prefixWord ++ tailWord_3793667).sum := by decide
  have hdescent : baseEnd_3793667 < baseStart_3793667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793671 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3793671 : Nat := 118140960795 + 3793671 * 2 ^ 59
def prefixEnd_3793671 : Nat := 4983230072969 + 3 ^ 40 * 3793671 * 2
def baseEnd_3793671 : Nat := 1947976668022931978465731

theorem tailTrace_3793671 : CollatzResearch.WordTrace tailWord_3793671 prefixEnd_3793671 1947976668022931978465731 := by
  unfold tailWord_3793671
  simp only [CollatzResearch.WordTrace]
  refine ⟨138366548639185349269364867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92244365759456899512909911 138366548639185349269364867)
  ·
    refine ⟨207549822958778023904047301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138366548639185349269364867 207549822958778023904047301)
    ·
      refine ⟨38915591804770879482008869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207549822958778023904047301 38915591804770879482008869)
      ·
        refine ⟨7296673463394539902876663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38915591804770879482008869 7296673463394539902876663)
        ·
          refine ⟨10945010195091809854314995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296673463394539902876663 10945010195091809854314995)
          ·
            refine ⟨16417515292637714781472493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10945010195091809854314995 16417515292637714781472493)
            ·
              refine ⟨6156568234739143043052185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16417515292637714781472493 6156568234739143043052185)
              ·
                refine ⟨4617426176054357282289139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156568234739143043052185 4617426176054357282289139)
                ·
                  refine ⟨6926139264081535923433709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617426176054357282289139 6926139264081535923433709)
                  ·
                    refine ⟨2597302224030575971287641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6926139264081535923433709 2597302224030575971287641)
                    ·
                      refine ⟨1947976668022931978465731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597302224030575971287641 1947976668022931978465731)
                      ·
                        rfl

theorem cell23_3793671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3793671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793671 prefixEnd_3793671 := by exact prefixLift 3793671
  have htrace : WordTrace (prefixWord ++ tailWord_3793671) baseStart_3793671 baseEnd_3793671 := by
    simpa [prefixWord, tailWord_3793671, baseEnd_3793671] using wordTrace_append hprefix tailTrace_3793671
  have hstable : (prefixWord ++ tailWord_3793671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793671).length < 2 ^ (prefixWord ++ tailWord_3793671).sum := by decide
  have hdescent : baseEnd_3793671 < baseStart_3793671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793701 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 2, 2, 2]
def baseStart_3793701 : Nat := 118140960795 + 3793701 * 2 ^ 59
def prefixEnd_3793701 : Nat := 4983230072969 + 3 ^ 40 * 3793701 * 2
def baseEnd_3793701 : Nat := 1947992072442566861090593

theorem tailTrace_3793701 : CollatzResearch.WordTrace tailWord_3793701 prefixEnd_3793701 1947992072442566861090593 := by
  unfold tailWord_3793701
  simp only [CollatzResearch.WordTrace]
  refine ⟨138367642829076664392956957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92245095219384442928637971 138367642829076664392956957)
  ·
    refine ⟨51887866060903749147358859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138367642829076664392956957 51887866060903749147358859)
    ·
      refine ⟨77831799091355623721038289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51887866060903749147358859 77831799091355623721038289)
      ·
        refine ⟨58373849318516717790778717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77831799091355623721038289 58373849318516717790778717)
        ·
          refine ⟨21890193494443769171542019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58373849318516717790778717 21890193494443769171542019)
          ·
            refine ⟨32835290241665653757313029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21890193494443769171542019 32835290241665653757313029)
            ·
              refine ⟨6156616920312310079496193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32835290241665653757313029 6156616920312310079496193)
              ·
                refine ⟨4617462690234232559622145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156616920312310079496193 4617462690234232559622145)
                ·
                  refine ⟨3463097017675674419716609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4617462690234232559622145 3463097017675674419716609)
                  ·
                    refine ⟨2597322763256755814787457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3463097017675674419716609 2597322763256755814787457)
                    ·
                      refine ⟨1947992072442566861090593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597322763256755814787457 1947992072442566861090593)
                      ·
                        rfl

theorem cell23_3793701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_3793701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793701 prefixEnd_3793701 := by exact prefixLift 3793701
  have htrace : WordTrace (prefixWord ++ tailWord_3793701) baseStart_3793701 baseEnd_3793701 := by
    simpa [prefixWord, tailWord_3793701, baseEnd_3793701] using wordTrace_append hprefix tailTrace_3793701
  have hstable : (prefixWord ++ tailWord_3793701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793701).length < 2 ^ (prefixWord ++ tailWord_3793701).sum := by decide
  have hdescent : baseEnd_3793701 < baseStart_3793701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793717 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_3793717 : Nat := 118140960795 + 3793717 * 2 ^ 59
def prefixEnd_3793717 : Nat := 4983230072969 + 3 ^ 40 * 3793717 * 2
def baseEnd_3793717 : Nat := 1948000288133038798490519

theorem tailTrace_3793717 : CollatzResearch.WordTrace tailWord_3793717 prefixEnd_3793717 1948000288133038798490519 := by
  unfold tailWord_3793717
  simp only [CollatzResearch.WordTrace]
  refine ⟨138368226397018699125539405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92245484264679132750359603 138368226397018699125539405)
  ·
    refine ⟨51888084898882012172077277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138368226397018699125539405 51888084898882012172077277)
    ·
      refine ⟨19458031837080754564528979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51888084898882012172077277 19458031837080754564528979)
      ·
        refine ⟨29187047755621131846793469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19458031837080754564528979 29187047755621131846793469)
        ·
          refine ⟨10945142908357924442547551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29187047755621131846793469 10945142908357924442547551)
          ·
            refine ⟨16417714362536886663821327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10945142908357924442547551 16417714362536886663821327)
            ·
              refine ⟨24626571543805329995731991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16417714362536886663821327 24626571543805329995731991)
              ·
                refine ⟨36939857315707994993597987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24626571543805329995731991 36939857315707994993597987)
                ·
                  refine ⟨55409785973561992490396981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36939857315707994993597987 55409785973561992490396981)
                  ·
                    refine ⟨5194667435021436795974717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55409785973561992490396981 5194667435021436795974717)
                    ·
                      refine ⟨1948000288133038798490519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194667435021436795974717 1948000288133038798490519)
                      ·
                        rfl

theorem cell23_3793717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_3793717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793717 prefixEnd_3793717 := by exact prefixLift 3793717
  have htrace : WordTrace (prefixWord ++ tailWord_3793717) baseStart_3793717 baseEnd_3793717 := by
    simpa [prefixWord, tailWord_3793717, baseEnd_3793717] using wordTrace_append hprefix tailTrace_3793717
  have hstable : (prefixWord ++ tailWord_3793717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793717).length < 2 ^ (prefixWord ++ tailWord_3793717).sum := by decide
  have hdescent : baseEnd_3793717 < baseStart_3793717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793718 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3793718 : Nat := 118140960795 + 3793718 * 2 ^ 59
def prefixEnd_3793718 : Nat := 4983230072969 + 3 ^ 40 * 3793718 * 2
def baseEnd_3793718 : Nat := 1948000801613693294578015

theorem tailTrace_3793718 : CollatzResearch.WordTrace tailWord_3793718 prefixEnd_3793718 1948000801613693294578015 := by
  unfold tailWord_3793718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8648016429375942268520363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92245508580010050864217205 8648016429375942268520363)
  ·
    refine ⟨12972024644063913402780545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8648016429375942268520363 12972024644063913402780545)
    ·
      refine ⟨9729018483047935052085409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12972024644063913402780545 9729018483047935052085409)
      ·
        refine ⟨7296763862285951289064057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9729018483047935052085409 7296763862285951289064057)
        ·
          refine ⟨5472572896714463466798043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7296763862285951289064057 5472572896714463466798043)
          ·
            refine ⟨8208859345071695200197065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472572896714463466798043 8208859345071695200197065)
            ·
              refine ⟨6156644508803771400147799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8208859345071695200197065 6156644508803771400147799)
              ·
                refine ⟨9234966763205657100221699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156644508803771400147799 9234966763205657100221699)
                ·
                  refine ⟨13852450144808485650332549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9234966763205657100221699 13852450144808485650332549)
                  ·
                    refine ⟨2597334402151591059437353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13852450144808485650332549 2597334402151591059437353)
                    ·
                      refine ⟨1948000801613693294578015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597334402151591059437353 1948000801613693294578015)
                      ·
                        rfl

theorem cell23_3793718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3793718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793718 prefixEnd_3793718 := by exact prefixLift 3793718
  have htrace : WordTrace (prefixWord ++ tailWord_3793718) baseStart_3793718 baseEnd_3793718 := by
    simpa [prefixWord, tailWord_3793718, baseEnd_3793718] using wordTrace_append hprefix tailTrace_3793718
  have hstable : (prefixWord ++ tailWord_3793718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793718).length < 2 ^ (prefixWord ++ tailWord_3793718).sum := by decide
  have hdescent : baseEnd_3793718 < baseStart_3793718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793720 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_3793720 : Nat := 118140960795 + 3793720 * 2 ^ 59
def prefixEnd_3793720 : Nat := 4983230072969 + 3 ^ 40 * 3793720 * 2
def baseEnd_3793720 : Nat := 649333942858334095584335

theorem tailTrace_3793720 : CollatzResearch.WordTrace tailWord_3793720 prefixEnd_3793720 649333942858334095584335 := by
  unfold tailWord_3793720
  simp only [CollatzResearch.WordTrace]
  refine ⟨69184167908003915318949307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92245557210671887091932409 69184167908003915318949307)
  ·
    refine ⟨103776251862005872978423961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69184167908003915318949307 103776251862005872978423961)
    ·
      refine ⟨77832188896504404733817971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103776251862005872978423961 77832188896504404733817971)
      ·
        refine ⟨116748283344756607100726957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77832188896504404733817971 116748283344756607100726957)
        ·
          refine ⟨43780606254283727662772609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116748283344756607100726957 43780606254283727662772609)
          ·
            refine ⟨32835454690712795747079457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43780606254283727662772609 32835454690712795747079457)
            ·
              refine ⟨24626591018034596810309593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32835454690712795747079457 24626591018034596810309593)
              ·
                refine ⟨18469943263525947607732195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24626591018034596810309593 18469943263525947607732195)
                ·
                  refine ⟨27704914895288921411598293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18469943263525947607732195 27704914895288921411598293)
                  ·
                    refine ⟨649333942858334095584335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27704914895288921411598293 649333942858334095584335)
                    ·
                      rfl

theorem cell23_3793720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_3793720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793720 prefixEnd_3793720 := by exact prefixLift 3793720
  have htrace : WordTrace (prefixWord ++ tailWord_3793720) baseStart_3793720 baseEnd_3793720 := by
    simpa [prefixWord, tailWord_3793720, baseEnd_3793720] using wordTrace_append hprefix tailTrace_3793720
  have hstable : (prefixWord ++ tailWord_3793720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793720).length < 2 ^ (prefixWord ++ tailWord_3793720).sum := by decide
  have hdescent : baseEnd_3793720 < baseStart_3793720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793737 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 2, 5]
def baseStart_3793737 : Nat := 118140960795 + 3793737 * 2 ^ 59
def prefixEnd_3793737 : Nat := 4983230072969 + 3 ^ 40 * 3793737 * 2
def baseEnd_3793737 : Nat := 649336852582042906746809

theorem tailTrace_3793737 : CollatzResearch.WordTrace tailWord_3793737 prefixEnd_3793737 649336852582042906746809 := by
  unfold tailWord_3793737
  simp only [CollatzResearch.WordTrace]
  refine ⟨138368955856946242541267465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92245970571297495027511643 138368955856946242541267465)
  ·
    refine ⟨103776716892709681905950599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138368955856946242541267465 103776716892709681905950599)
    ·
      refine ⟨155665075339064522858925899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103776716892709681905950599 155665075339064522858925899)
      ·
        refine ⟨233497613008596784288388849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155665075339064522858925899 233497613008596784288388849)
        ·
          refine ⟨175123209756447588216291637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233497613008596784288388849 175123209756447588216291637)
          ·
            refine ⟨16417800914666961395277341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175123209756447588216291637 16417800914666961395277341)
            ·
              refine ⟨6156675343000110523229003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16417800914666961395277341 6156675343000110523229003)
              ·
                refine ⟨9235013014500165784843505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156675343000110523229003 9235013014500165784843505)
                ·
                  refine ⟨6926259760875124338632629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235013014500165784843505 6926259760875124338632629)
                  ·
                    refine ⟨649336852582042906746809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6926259760875124338632629 649336852582042906746809)
                    ·
                      rfl

theorem cell23_3793737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_3793737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793737 prefixEnd_3793737 := by exact prefixLift 3793737
  have htrace : WordTrace (prefixWord ++ tailWord_3793737) baseStart_3793737 baseEnd_3793737 := by
    simpa [prefixWord, tailWord_3793737, baseEnd_3793737] using wordTrace_append hprefix tailTrace_3793737
  have hstable : (prefixWord ++ tailWord_3793737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793737).length < 2 ^ (prefixWord ++ tailWord_3793737).sum := by decide
  have hdescent : baseEnd_3793737 < baseStart_3793737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793777 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_3793777 : Nat := 118140960795 + 3793777 * 2 ^ 59
def prefixEnd_3793777 : Nat := 4983230072969 + 3 ^ 40 * 3793777 * 2
def baseEnd_3793777 : Nat := 1948031096972308563740243

theorem tailTrace_3793777 : CollatzResearch.WordTrace tailWord_3793777 prefixEnd_3793777 1948031096972308563740243 := by
  unfold tailWord_3793777
  simp only [CollatzResearch.WordTrace]
  refine ⟨138370414776801329372723585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92246943184534219581815723 138370414776801329372723585)
  ·
    refine ⟨103777811082600997029542689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138370414776801329372723585 103777811082600997029542689)
    ·
      refine ⟨77833358311950747772157017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103777811082600997029542689 77833358311950747772157017)
      ·
        refine ⟨58375018733963060829117763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77833358311950747772157017 58375018733963060829117763)
        ·
          refine ⟨87562528100944591243676645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58375018733963060829117763 87562528100944591243676645)
          ·
            refine ⟨16417974018927110858189371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87562528100944591243676645 16417974018927110858189371)
            ·
              refine ⟨24626961028390666287284057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16417974018927110858189371 24626961028390666287284057)
              ·
                refine ⟨18470220771292999715463043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24626961028390666287284057 18470220771292999715463043)
                ·
                  refine ⟨27705331156939499573194565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18470220771292999715463043 27705331156939499573194565)
                  ·
                    refine ⟨5194749591926156169973981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27705331156939499573194565 5194749591926156169973981)
                    ·
                      refine ⟨1948031096972308563740243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194749591926156169973981 1948031096972308563740243)
                      ·
                        rfl

theorem cell23_3793777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_3793777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793777 prefixEnd_3793777 := by exact prefixLift 3793777
  have htrace : WordTrace (prefixWord ++ tailWord_3793777) baseStart_3793777 baseEnd_3793777 := by
    simpa [prefixWord, tailWord_3793777, baseEnd_3793777] using wordTrace_append hprefix tailTrace_3793777
  have hstable : (prefixWord ++ tailWord_3793777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793777).length < 2 ^ (prefixWord ++ tailWord_3793777).sum := by decide
  have hdescent : baseEnd_3793777 < baseStart_3793777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793801 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 1, 4]
def baseStart_3793801 : Nat := 118140960795 + 3793801 * 2 ^ 59
def prefixEnd_3793801 : Nat := 4983230072969 + 3 ^ 40 * 3793801 * 2
def baseEnd_3793801 : Nat := 649347806836005489946711

theorem tailTrace_3793801 : CollatzResearch.WordTrace tailWord_3793801 prefixEnd_3793801 649347806836005489946711 := by
  unfold tailWord_3793801
  simp only [CollatzResearch.WordTrace]
  refine ⟨138371290128714381471597257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92247526752476254314398171 138371290128714381471597257)
  ·
    refine ⟨103778467596535786103697943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138371290128714381471597257 103778467596535786103697943)
    ·
      refine ⟨155667701394803679155546915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103778467596535786103697943 155667701394803679155546915)
      ·
        refine ⟨233501552092205518733320373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155667701394803679155546915 233501552092205518733320373)
        ·
          refine ⟨21890770508644267381248785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233501552092205518733320373 21890770508644267381248785)
          ·
            refine ⟨16418077881483200535936589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21890770508644267381248785 16418077881483200535936589)
            ·
              refine ⟨6156779205556200200976221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16418077881483200535936589 6156779205556200200976221)
              ·
                refine ⟨2308792202083575075366083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6156779205556200200976221 2308792202083575075366083)
                ·
                  refine ⟨3463188303125362613049125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308792202083575075366083 3463188303125362613049125)
                  ·
                    refine ⟨649347806836005489946711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3463188303125362613049125 649347806836005489946711)
                    ·
                      rfl

theorem cell23_3793801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 4].length) (baseStart_3793801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793801 prefixEnd_3793801 := by exact prefixLift 3793801
  have htrace : WordTrace (prefixWord ++ tailWord_3793801) baseStart_3793801 baseEnd_3793801 := by
    simpa [prefixWord, tailWord_3793801, baseEnd_3793801] using wordTrace_append hprefix tailTrace_3793801
  have hstable : (prefixWord ++ tailWord_3793801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793801).length < 2 ^ (prefixWord ++ tailWord_3793801).sum := by decide
  have hdescent : baseEnd_3793801 < baseStart_3793801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793818 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_3793818 : Nat := 118140960795 + 3793818 * 2 ^ 59
def prefixEnd_3793818 : Nat := 4983230072969 + 3 ^ 40 * 3793818 * 2
def baseEnd_3793818 : Nat := 649350716559714301109185

theorem tailTrace_3793818 : CollatzResearch.WordTrace tailWord_3793818 prefixEnd_3793818 649350716559714301109185 := by
  unfold tailWord_3793818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34592977542413198343741527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92247940113101862249977405 34592977542413198343741527)
  ·
    refine ⟨51889466313619797515612291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34592977542413198343741527 51889466313619797515612291)
    ·
      refine ⟨77834199470429696273418437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51889466313619797515612291 77834199470429696273418437)
      ·
        refine ⟨14593912400705568051265957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77834199470429696273418437 14593912400705568051265957)
        ·
          refine ⟨2736358575132294009612367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14593912400705568051265957 2736358575132294009612367)
          ·
            refine ⟨4104537862698441014418551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736358575132294009612367 4104537862698441014418551)
            ·
              refine ⟨6156806794047661521627827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104537862698441014418551 6156806794047661521627827)
              ·
                refine ⟨9235210191071492282441741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156806794047661521627827 9235210191071492282441741)
                ·
                  refine ⟨3463203821651809605915653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9235210191071492282441741 3463203821651809605915653)
                  ·
                    refine ⟨649350716559714301109185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3463203821651809605915653 649350716559714301109185)
                    ·
                      rfl

theorem cell23_3793818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_3793818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793818 prefixEnd_3793818 := by exact prefixLift 3793818
  have htrace : WordTrace (prefixWord ++ tailWord_3793818) baseStart_3793818 baseEnd_3793818 := by
    simpa [prefixWord, tailWord_3793818, baseEnd_3793818] using wordTrace_append hprefix tailTrace_3793818
  have hstable : (prefixWord ++ tailWord_3793818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793818).length < 2 ^ (prefixWord ++ tailWord_3793818).sum := by decide
  have hdescent : baseEnd_3793818 < baseStart_3793818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793898 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_3793898 : Nat := 118140960795 + 3793898 * 2 ^ 59
def prefixEnd_3793898 : Nat := 4983230072969 + 3 ^ 40 * 3793898 * 2
def baseEnd_3793898 : Nat := 1948093228131502590327187

theorem tailTrace_3793898 : CollatzResearch.WordTrace tailWord_3793898 prefixEnd_3793898 1948093228131502590327187 := by
  unfold tailWord_3793898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34593707002340741759469587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92249885339575311358585565 34593707002340741759469587)
  ·
    refine ⟨51890560503511112639204381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34593707002340741759469587 51890560503511112639204381)
    ·
      refine ⟨19458960188816667239701643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51890560503511112639204381 19458960188816667239701643)
      ·
        refine ⟨29188440283225000859552465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19458960188816667239701643 29188440283225000859552465)
        ·
          refine ⟨21891330212418750644664349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29188440283225000859552465 21891330212418750644664349)
          ·
            refine ⟨8209248829657031491749131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21891330212418750644664349 8209248829657031491749131)
            ·
              refine ⟨12313873244485547237623697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209248829657031491749131 12313873244485547237623697)
              ·
                refine ⟨9235404933364160428217773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12313873244485547237623697 9235404933364160428217773)
                ·
                  refine ⟨3463276850011560160581665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9235404933364160428217773 3463276850011560160581665)
                  ·
                    refine ⟨2597457637508670120436249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3463276850011560160581665 2597457637508670120436249)
                    ·
                      refine ⟨1948093228131502590327187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597457637508670120436249 1948093228131502590327187)
                      ·
                        rfl

theorem cell23_3793898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_3793898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793898 prefixEnd_3793898 := by exact prefixLift 3793898
  have htrace : WordTrace (prefixWord ++ tailWord_3793898) baseStart_3793898 baseEnd_3793898 := by
    simpa [prefixWord, tailWord_3793898, baseEnd_3793898] using wordTrace_append hprefix tailTrace_3793898
  have hstable : (prefixWord ++ tailWord_3793898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793898).length < 2 ^ (prefixWord ++ tailWord_3793898).sum := by decide
  have hdescent : baseEnd_3793898 < baseStart_3793898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793931 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 3]
def baseStart_3793931 : Nat := 118140960795 + 3793931 * 2 ^ 59
def prefixEnd_3793931 : Nat := 4983230072969 + 3 ^ 40 * 3793931 * 2
def baseEnd_3793931 : Nat := 1948110172993100961214535

theorem tailTrace_3793931 : CollatzResearch.WordTrace tailWord_3793931 prefixEnd_3793931 1948110172993100961214535 := by
  unfold tailWord_3793931
  simp only [CollatzResearch.WordTrace]
  refine ⟨138376031618243413673829647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92250687745495609115886431 138376031618243413673829647)
  ·
    refine ⟨207564047427365120510744471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138376031618243413673829647 207564047427365120510744471)
    ·
      refine ⟨311346071141047680766116707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207564047427365120510744471 311346071141047680766116707)
      ·
        refine ⟨467019106711571521149175061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311346071141047680766116707 467019106711571521149175061)
        ·
          refine ⟨21891520627104915053867581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 467019106711571521149175061 21891520627104915053867581)
          ·
            refine ⟨8209320235164343145200343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21891520627104915053867581 8209320235164343145200343)
            ·
              refine ⟨12313980352746514717800515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209320235164343145200343 12313980352746514717800515)
              ·
                refine ⟨18470970529119772076700773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313980352746514717800515 18470970529119772076700773)
                ·
                  refine ⟨3463306974209957264381395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18470970529119772076700773 3463306974209957264381395)
                  ·
                    refine ⟨5194960461314935896572093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463306974209957264381395 5194960461314935896572093)
                    ·
                      refine ⟨1948110172993100961214535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194960461314935896572093 1948110172993100961214535)
                      ·
                        rfl

theorem cell23_3793931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 3].length) (baseStart_3793931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793931 prefixEnd_3793931 := by exact prefixLift 3793931
  have htrace : WordTrace (prefixWord ++ tailWord_3793931) baseStart_3793931 baseEnd_3793931 := by
    simpa [prefixWord, tailWord_3793931, baseEnd_3793931] using wordTrace_append hprefix tailTrace_3793931
  have hstable : (prefixWord ++ tailWord_3793931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793931).length < 2 ^ (prefixWord ++ tailWord_3793931).sum := by decide
  have hdescent : baseEnd_3793931 < baseStart_3793931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793937 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_3793937 : Nat := 118140960795 + 3793937 * 2 ^ 59
def prefixEnd_3793937 : Nat := 4983230072969 + 3 ^ 40 * 3793937 * 2
def baseEnd_3793937 : Nat := 1948113253877027937739507

theorem tailTrace_3793937 : CollatzResearch.WordTrace tailWord_3793937 prefixEnd_3793937 1948113253877027937739507 := by
  unfold tailWord_3793937
  simp only [CollatzResearch.WordTrace]
  refine ⟨138376250456221676698548065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92250833637481117799032043 138376250456221676698548065)
  ·
    refine ⟨103782187842166257523911049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138376250456221676698548065 103782187842166257523911049)
    ·
      refine ⟨77836640881624693142933287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103782187842166257523911049 77836640881624693142933287)
      ·
        refine ⟨116754961322437039714399931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77836640881624693142933287 116754961322437039714399931)
        ·
          refine ⟨175132441983655559571599897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116754961322437039714399931 175132441983655559571599897)
          ·
            refine ⟨131349331487741669678699923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175132441983655559571599897 131349331487741669678699923)
            ·
              refine ⟨197023997231612504518049885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131349331487741669678699923 197023997231612504518049885)
              ·
                refine ⟨73883998961854689194268707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197023997231612504518049885 73883998961854689194268707)
                ·
                  refine ⟨110825998442782033791403061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73883998961854689194268707 110825998442782033791403061)
                  ·
                    refine ⟨10389937354010815667944037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110825998442782033791403061 10389937354010815667944037)
                    ·
                      refine ⟨1948113253877027937739507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10389937354010815667944037 1948113253877027937739507)
                      ·
                        rfl

theorem cell23_3793937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_3793937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793937 prefixEnd_3793937 := by exact prefixLift 3793937
  have htrace : WordTrace (prefixWord ++ tailWord_3793937) baseStart_3793937 baseEnd_3793937 := by
    simpa [prefixWord, tailWord_3793937, baseEnd_3793937] using wordTrace_append hprefix tailTrace_3793937
  have hstable : (prefixWord ++ tailWord_3793937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793937).length < 2 ^ (prefixWord ++ tailWord_3793937).sum := by decide
  have hdescent : baseEnd_3793937 < baseStart_3793937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793948 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3793948 : Nat := 118140960795 + 3793948 * 2 ^ 59
def prefixEnd_3793948 : Nat := 4983230072969 + 3 ^ 40 * 3793948 * 2
def baseEnd_3793948 : Nat := 1948118902164227394701957

theorem tailTrace_3793948 : CollatzResearch.WordTrace tailWord_3793948 prefixEnd_3793948 1948118902164227394701957 := by
  unfold tailWord_3793948
  simp only [CollatzResearch.WordTrace]
  refine ⟨69188325829590912788599249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92251101106121217051465665 69188325829590912788599249)
  ·
    refine ⟨51891244372193184591449437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69188325829590912788599249 51891244372193184591449437)
    ·
      refine ⟨19459216639572444221793539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51891244372193184591449437 19459216639572444221793539)
      ·
        refine ⟨29188824959358666332690309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19459216639572444221793539 29188824959358666332690309)
        ·
          refine ⟨5472904679879749937379433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29188824959358666332690309 5472904679879749937379433)
          ·
            refine ⟨4104678509909812453034575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472904679879749937379433 4104678509909812453034575)
            ·
              refine ⟨6157017764864718679551863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104678509909812453034575 6157017764864718679551863)
              ·
                refine ⟨9235526647297078019327795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157017764864718679551863 9235526647297078019327795)
                ·
                  refine ⟨13853289970945617028991693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235526647297078019327795 13853289970945617028991693)
                  ·
                    refine ⟨5194983739104606385871885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13853289970945617028991693 5194983739104606385871885)
                    ·
                      refine ⟨1948118902164227394701957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5194983739104606385871885 1948118902164227394701957)
                      ·
                        rfl

theorem cell23_3793948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3793948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793948 prefixEnd_3793948 := by exact prefixLift 3793948
  have htrace : WordTrace (prefixWord ++ tailWord_3793948) baseStart_3793948 baseEnd_3793948 := by
    simpa [prefixWord, tailWord_3793948, baseEnd_3793948] using wordTrace_append hprefix tailTrace_3793948
  have hstable : (prefixWord ++ tailWord_3793948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793948).length < 2 ^ (prefixWord ++ tailWord_3793948).sum := by decide
  have hdescent : baseEnd_3793948 < baseStart_3793948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793987 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_3793987 : Nat := 118140960795 + 3793987 * 2 ^ 59
def prefixEnd_3793987 : Nat := 4983230072969 + 3 ^ 40 * 3793987 * 2
def baseEnd_3793987 : Nat := 1948138927909752742114277

theorem tailTrace_3793987 : CollatzResearch.WordTrace tailWord_3793987 prefixEnd_3793987 1948138927909752742114277 := by
  unfold tailWord_3793987
  simp only [CollatzResearch.WordTrace]
  refine ⟨138378074106040535237868215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92252049404027023491912143 138378074106040535237868215)
  ·
    refine ⟨207567111159060802856802323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138378074106040535237868215 207567111159060802856802323)
    ·
      refine ⟨311350666738591204285203485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207567111159060802856802323 311350666738591204285203485)
      ·
        refine ⟨116756500026971701606951307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311350666738591204285203485 116756500026971701606951307)
        ·
          refine ⟨175134750040457552410426961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116756500026971701606951307 175134750040457552410426961)
          ·
            refine ⟨131351062530343164307820221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175134750040457552410426961 131351062530343164307820221)
            ·
              refine ⟨49256648448878686615432583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131351062530343164307820221 49256648448878686615432583)
              ·
                refine ⟨73884972673318029923148875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49256648448878686615432583 73884972673318029923148875)
                ·
                  refine ⟨110827459009977044884723313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73884972673318029923148875 110827459009977044884723313)
                  ·
                    refine ⟨83120594257482783663542485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110827459009977044884723313 83120594257482783663542485)
                    ·
                      refine ⟨1948138927909752742114277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83120594257482783663542485 1948138927909752742114277)
                      ·
                        rfl

theorem cell23_3793987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_3793987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793987 prefixEnd_3793987 := by exact prefixLift 3793987
  have htrace : WordTrace (prefixWord ++ tailWord_3793987) baseStart_3793987 baseEnd_3793987 := by
    simpa [prefixWord, tailWord_3793987, baseEnd_3793987] using wordTrace_append hprefix tailTrace_3793987
  have hstable : (prefixWord ++ tailWord_3793987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793987).length < 2 ^ (prefixWord ++ tailWord_3793987).sum := by decide
  have hdescent : baseEnd_3793987 < baseStart_3793987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793994 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_3793994 : Nat := 118140960795 + 3793994 * 2 ^ 59
def prefixEnd_3793994 : Nat := 4983230072969 + 3 ^ 40 * 3793994 * 2
def baseEnd_3793994 : Nat := 216460280252703801636305

theorem tailTrace_3793994 : CollatzResearch.WordTrace tailWord_3793994 prefixEnd_3793994 216460280252703801636305 := by
  unfold tailWord_3793994
  simp only [CollatzResearch.WordTrace]
  refine ⟨34594582354253793858343259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92252219611343450288915357 34594582354253793858343259)
  ·
    refine ⟨51891873531380690787514889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34594582354253793858343259 51891873531380690787514889)
    ·
      refine ⟨38918905148535518090636167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51891873531380690787514889 38918905148535518090636167)
      ·
        refine ⟨58378357722803277135954251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38918905148535518090636167 58378357722803277135954251)
        ·
          refine ⟨87567536584204915703931377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58378357722803277135954251 87567536584204915703931377)
          ·
            refine ⟨65675652438153686777948533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87567536584204915703931377 65675652438153686777948533)
            ·
              refine ⟨6157092416076908135432675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65675652438153686777948533 6157092416076908135432675)
              ·
                refine ⟨9235638624115362203149013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157092416076908135432675 9235638624115362203149013)
                ·
                  refine ⟨216460280252703801636305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9235638624115362203149013 216460280252703801636305)
                  ·
                    rfl

theorem cell23_3793994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_3793994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3793994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3793994 prefixEnd_3793994 := by exact prefixLift 3793994
  have htrace : WordTrace (prefixWord ++ tailWord_3793994) baseStart_3793994 baseEnd_3793994 := by
    simpa [prefixWord, tailWord_3793994, baseEnd_3793994] using wordTrace_append hprefix tailTrace_3793994
  have hstable : (prefixWord ++ tailWord_3793994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793994).length < 2 ^ (prefixWord ++ tailWord_3793994).sum := by decide
  have hdescent : baseEnd_3793994 < baseStart_3793994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794034 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3794034 : Nat := 118140960795 + 3794034 * 2 ^ 59
def prefixEnd_3794034 : Nat := 4983230072969 + 3 ^ 40 * 3794034 * 2
def baseEnd_3794034 : Nat := 1948163061500514058226561

theorem tailTrace_3794034 : CollatzResearch.WordTrace tailWord_3794034 prefixEnd_3794034 1948163061500514058226561 := by
  unfold tailWord_3794034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34594947084217565566207289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92253192224580174843219437 34594947084217565566207289)
  ·
    refine ⟨25946210313163174174655467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34594947084217565566207289 25946210313163174174655467)
    ·
      refine ⟨38919315469744761261983201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25946210313163174174655467 38919315469744761261983201)
      ·
        refine ⟨29189486602308570946487401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38919315469744761261983201 29189486602308570946487401)
        ·
          refine ⟨21892114951731428209865551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29189486602308570946487401 21892114951731428209865551)
          ·
            refine ⟨32838172427597142314798327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21892114951731428209865551 32838172427597142314798327)
            ·
              refine ⟨49257258641395713472197491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32838172427597142314798327 49257258641395713472197491)
              ·
                refine ⟨73885887962093570208296237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49257258641395713472197491 73885887962093570208296237)
                ·
                  refine ⟨27707207985785088828111089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73885887962093570208296237 27707207985785088828111089)
                  ·
                    refine ⟨20780405989338816621083317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27707207985785088828111089 20780405989338816621083317)
                    ·
                      refine ⟨1948163061500514058226561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20780405989338816621083317 1948163061500514058226561)
                      ·
                        rfl

theorem cell23_3794034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3794034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794034 prefixEnd_3794034 := by exact prefixLift 3794034
  have htrace : WordTrace (prefixWord ++ tailWord_3794034) baseStart_3794034 baseEnd_3794034 := by
    simpa [prefixWord, tailWord_3794034, baseEnd_3794034] using wordTrace_append hprefix tailTrace_3794034
  have hstable : (prefixWord ++ tailWord_3794034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794034).length < 2 ^ (prefixWord ++ tailWord_3794034).sum := by decide
  have hdescent : baseEnd_3794034 < baseStart_3794034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794071 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 5, 4]
def baseStart_3794071 : Nat := 118140960795 + 3794071 * 2 ^ 59
def prefixEnd_3794071 : Nat := 4983230072969 + 3 ^ 40 * 3794071 * 2
def baseEnd_3794071 : Nat := 649394020094910137821297

theorem tailTrace_3794071 : CollatzResearch.WordTrace tailWord_3794071 prefixEnd_3794071 649394020094910137821297 := by
  unfold tailWord_3794071
  simp only [CollatzResearch.WordTrace]
  refine ⟨138381137837736217583926067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92254091891824145055950711 138381137837736217583926067)
  ·
    refine ⟨207571706756604326375889101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138381137837736217583926067 207571706756604326375889101)
    ·
      refine ⟨77839390033726622390958413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207571706756604326375889101 77839390033726622390958413)
      ·
        refine ⟨29189771262647483396609405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77839390033726622390958413 29189771262647483396609405)
        ·
          refine ⟨10946164223492806273728527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29189771262647483396609405 10946164223492806273728527)
          ·
            refine ⟨16419246335239209410592791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946164223492806273728527 16419246335239209410592791)
            ·
              refine ⟨24628869502858814115889187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16419246335239209410592791 24628869502858814115889187)
              ·
                refine ⟨36943304254288221173833781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24628869502858814115889187 36943304254288221173833781)
                ·
                  refine ⟨3463434773839520735046917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36943304254288221173833781 3463434773839520735046917)
                  ·
                    refine ⟨649394020094910137821297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3463434773839520735046917 649394020094910137821297)
                    ·
                      rfl

theorem cell23_3794071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_3794071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794071 prefixEnd_3794071 := by exact prefixLift 3794071
  have htrace : WordTrace (prefixWord ++ tailWord_3794071) baseStart_3794071 baseEnd_3794071 := by
    simpa [prefixWord, tailWord_3794071, baseEnd_3794071] using wordTrace_append hprefix tailTrace_3794071
  have hstable : (prefixWord ++ tailWord_3794071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794071).length < 2 ^ (prefixWord ++ tailWord_3794071).sum := by decide
  have hdescent : baseEnd_3794071 < baseStart_3794071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794078 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3794078 : Nat := 118140960795 + 3794078 * 2 ^ 59
def prefixEnd_3794078 : Nat := 4983230072969 + 3 ^ 40 * 3794078 * 2
def baseEnd_3794078 : Nat := 1948185654649311886076359

theorem tailTrace_3794078 : CollatzResearch.WordTrace tailWord_3794078 prefixEnd_3794078 1948185654649311886076359 := by
  unfold tailWord_3794078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297674143588857222428861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92254262099140571852953925 17297674143588857222428861)
  ·
    refine ⟨6486627803845821458410823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17297674143588857222428861 6486627803845821458410823)
    ·
      refine ⟨9729941705768732187616235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6486627803845821458410823 9729941705768732187616235)
      ·
        refine ⟨14594912558653098281424353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9729941705768732187616235 14594912558653098281424353)
        ·
          refine ⟨10946184418989823711068265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14594912558653098281424353 10946184418989823711068265)
          ·
            refine ⟨8209638314242367783301199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10946184418989823711068265 8209638314242367783301199)
            ·
              refine ⟨12314457471363551674951799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209638314242367783301199 12314457471363551674951799)
              ·
                refine ⟨18471686207045327512427699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314457471363551674951799 18471686207045327512427699)
                ·
                  refine ⟨27707529310567991268641549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18471686207045327512427699 27707529310567991268641549)
                  ·
                    refine ⟨10390323491462996725740581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27707529310567991268641549 10390323491462996725740581)
                    ·
                      refine ⟨1948185654649311886076359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10390323491462996725740581 1948185654649311886076359)
                      ·
                        rfl

theorem cell23_3794078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3794078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794078 prefixEnd_3794078 := by exact prefixLift 3794078
  have htrace : WordTrace (prefixWord ++ tailWord_3794078) baseStart_3794078 baseEnd_3794078 := by
    simpa [prefixWord, tailWord_3794078, baseEnd_3794078] using wordTrace_append hprefix tailTrace_3794078
  have hstable : (prefixWord ++ tailWord_3794078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794078).length < 2 ^ (prefixWord ++ tailWord_3794078).sum := by decide
  have hdescent : baseEnd_3794078 < baseStart_3794078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794081 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3794081 : Nat := 118140960795 + 3794081 * 2 ^ 59
def prefixEnd_3794081 : Nat := 4983230072969 + 3 ^ 40 * 3794081 * 2
def baseEnd_3794081 : Nat := 1948187195091275374338845

theorem tailTrace_3794081 : CollatzResearch.WordTrace tailWord_3794081 prefixEnd_3794081 1948187195091275374338845 := by
  unfold tailWord_3794081
  simp only [CollatzResearch.WordTrace]
  refine ⟨138381502567699989291790097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92254335045133326194526731 138381502567699989291790097)
  ·
    refine ⟨103786126925774991968842573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138381502567699989291790097 103786126925774991968842573)
    ·
      refine ⟨38919797597165621988315965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103786126925774991968842573 38919797597165621988315965)
      ·
        refine ⟨14594924098937108245618487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38919797597165621988315965 14594924098937108245618487)
        ·
          refine ⟨21892386148405662368427731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14594924098937108245618487 21892386148405662368427731)
          ·
            refine ⟨32838579222608493552641597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21892386148405662368427731 32838579222608493552641597)
            ·
              refine ⟨12314467208478185082240599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32838579222608493552641597 12314467208478185082240599)
              ·
                refine ⟨18471700812717277623360899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314467208478185082240599 18471700812717277623360899)
                ·
                  refine ⟨27707551219075916435041349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18471700812717277623360899 27707551219075916435041349)
                  ·
                    refine ⟨5195165853576734331570253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27707551219075916435041349 5195165853576734331570253)
                    ·
                      refine ⟨1948187195091275374338845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195165853576734331570253 1948187195091275374338845)
                      ·
                        rfl

theorem cell23_3794081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3794081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794081 prefixEnd_3794081 := by exact prefixLift 3794081
  have htrace : WordTrace (prefixWord ++ tailWord_3794081) baseStart_3794081 baseEnd_3794081 := by
    simpa [prefixWord, tailWord_3794081, baseEnd_3794081] using wordTrace_append hprefix tailTrace_3794081
  have hstable : (prefixWord ++ tailWord_3794081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794081).length < 2 ^ (prefixWord ++ tailWord_3794081).sum := by decide
  have hdescent : baseEnd_3794081 < baseStart_3794081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794138 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2]
def baseStart_3794138 : Nat := 118140960795 + 3794138 * 2 ^ 59
def prefixEnd_3794138 : Nat := 4983230072969 + 3 ^ 40 * 3794138 * 2
def baseEnd_3794138 : Nat := 1948216463488581651326083

theorem tailTrace_3794138 : CollatzResearch.WordTrace tailWord_3794138 prefixEnd_3794138 1948216463488581651326083 := by
  unfold tailWord_3794138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34595895382123372006653767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92255721018995658684410045 34595895382123372006653767)
  ·
    refine ⟨51893843073185058009980651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34595895382123372006653767 51893843073185058009980651)
    ·
      refine ⟨77840764609777587014970977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51893843073185058009980651 77840764609777587014970977)
      ·
        refine ⟨58380573457333190261228233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77840764609777587014970977 58380573457333190261228233)
        ·
          refine ⟨43785430092999892695921175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58380573457333190261228233 43785430092999892695921175)
          ·
            refine ⟨65678145139499839043881763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43785430092999892695921175 65678145139499839043881763)
            ·
              refine ⟨98517217709249758565822645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65678145139499839043881763 98517217709249758565822645)
              ·
                refine ⟨9235989160242164865545873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98517217709249758565822645 9235989160242164865545873)
                ·
                  refine ⟨6926991870181623649159405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235989160242164865545873 6926991870181623649159405)
                  ·
                    refine ⟨2597621951318108868434777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6926991870181623649159405 2597621951318108868434777)
                    ·
                      refine ⟨1948216463488581651326083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597621951318108868434777 1948216463488581651326083)
                      ·
                        rfl

theorem cell23_3794138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_3794138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794138 prefixEnd_3794138 := by exact prefixLift 3794138
  have htrace : WordTrace (prefixWord ++ tailWord_3794138) baseStart_3794138 baseEnd_3794138 := by
    simpa [prefixWord, tailWord_3794138, baseEnd_3794138] using wordTrace_append hprefix tailTrace_3794138
  have hstable : (prefixWord ++ tailWord_3794138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794138).length < 2 ^ (prefixWord ++ tailWord_3794138).sum := by decide
  have hdescent : baseEnd_3794138 < baseStart_3794138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794162 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3794162 : Nat := 118140960795 + 3794162 * 2 ^ 59
def prefixEnd_3794162 : Nat := 4983230072969 + 3 ^ 40 * 3794162 * 2
def baseEnd_3794162 : Nat := 1948228787024289557425973

theorem tailTrace_3794162 : CollatzResearch.WordTrace tailWord_3794162 prefixEnd_3794162 1948228787024289557425973 := by
  unfold tailWord_3794162
  simp only [CollatzResearch.WordTrace]
  refine ⟨34596114220101635031372185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92256304586937693416992493 34596114220101635031372185)
  ·
    refine ⟨25947085665076226273529139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34596114220101635031372185 25947085665076226273529139)
    ·
      refine ⟨38920628497614339410293709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25947085665076226273529139 38920628497614339410293709)
      ·
        refine ⟨14595235686605377278860141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38920628497614339410293709 14595235686605377278860141)
        ·
          refine ⟨5473213382477016479572553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14595235686605377278860141 5473213382477016479572553)
          ·
            refine ⟨4104910036857762359679415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473213382477016479572553 4104910036857762359679415)
            ·
              refine ⟨6157365055286643539519123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104910036857762359679415 6157365055286643539519123)
              ·
                refine ⟨9236047582929965309278685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157365055286643539519123 9236047582929965309278685)
                ·
                  refine ⟨3463517843598736990979507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9236047582929965309278685 3463517843598736990979507)
                  ·
                    refine ⟨5195276765398105486469261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463517843598736990979507 5195276765398105486469261)
                    ·
                      refine ⟨1948228787024289557425973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195276765398105486469261 1948228787024289557425973)
                      ·
                        rfl

theorem cell23_3794162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3794162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794162 prefixEnd_3794162 := by exact prefixLift 3794162
  have htrace : WordTrace (prefixWord ++ tailWord_3794162) baseStart_3794162 baseEnd_3794162 := by
    simpa [prefixWord, tailWord_3794162, baseEnd_3794162] using wordTrace_append hprefix tailTrace_3794162
  have hstable : (prefixWord ++ tailWord_3794162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794162).length < 2 ^ (prefixWord ++ tailWord_3794162).sum := by decide
  have hdescent : baseEnd_3794162 < baseStart_3794162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794181 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_3794181 : Nat := 118140960795 + 3794181 * 2 ^ 59
def prefixEnd_3794181 : Nat := 4983230072969 + 3 ^ 40 * 3794181 * 2
def baseEnd_3794181 : Nat := 1948238543156724983088385

theorem tailTrace_3794181 : CollatzResearch.WordTrace tailWord_3794181 prefixEnd_3794181 1948238543156724983088385 := by
  unfold tailWord_3794181
  simp only [CollatzResearch.WordTrace]
  refine ⟨138385149867337706370430397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92256766578225137580286931 138385149867337706370430397)
  ·
    refine ⟨51894431200251639888911399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138385149867337706370430397 51894431200251639888911399)
    ·
      refine ⟨77841646800377459833367099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51894431200251639888911399 77841646800377459833367099)
      ·
        refine ⟨116762470200566189750050649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77841646800377459833367099 116762470200566189750050649)
        ·
          refine ⟨87571852650424642312537987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116762470200566189750050649 87571852650424642312537987)
          ·
            refine ⟨131357778975636963468806981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87571852650424642312537987 131357778975636963468806981)
            ·
              refine ⟨24629583557931930650401309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131357778975636963468806981 24629583557931930650401309)
              ·
                refine ⟨9236093834224473993900491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24629583557931930650401309 9236093834224473993900491)
                ·
                  refine ⟨13854140751336710990850737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236093834224473993900491 13854140751336710990850737)
                  ·
                    refine ⟨10390605563502533243138053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13854140751336710990850737 10390605563502533243138053)
                    ·
                      refine ⟨1948238543156724983088385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10390605563502533243138053 1948238543156724983088385)
                      ·
                        rfl

theorem cell23_3794181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_3794181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794181 prefixEnd_3794181 := by exact prefixLift 3794181
  have htrace : WordTrace (prefixWord ++ tailWord_3794181) baseStart_3794181 baseEnd_3794181 := by
    simpa [prefixWord, tailWord_3794181, baseEnd_3794181] using wordTrace_append hprefix tailTrace_3794181
  have hstable : (prefixWord ++ tailWord_3794181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794181).length < 2 ^ (prefixWord ++ tailWord_3794181).sum := by decide
  have hdescent : baseEnd_3794181 < baseStart_3794181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794188 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3794188 : Nat := 118140960795 + 3794188 * 2 ^ 59
def prefixEnd_3794188 : Nat := 4983230072969 + 3 ^ 40 * 3794188 * 2
def baseEnd_3794188 : Nat := 1948242137521306455700853

theorem tailTrace_3794188 : CollatzResearch.WordTrace tailWord_3794188 prefixEnd_3794188 1948242137521306455700853 := by
  unfold tailWord_3794188
  simp only [CollatzResearch.WordTrace]
  refine ⟨69192702589156173282967609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92256936785541564377290145 69192702589156173282967609)
  ·
    refine ⟨51894526941867129962225707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69192702589156173282967609 51894526941867129962225707)
    ·
      refine ⟨77841790412800694943338561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51894526941867129962225707 77841790412800694943338561)
      ·
        refine ⟨58381342809600521207503921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77841790412800694943338561 58381342809600521207503921)
        ·
          refine ⟨43786007107200390905627941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58381342809600521207503921 43786007107200390905627941)
          ·
            refine ⟨8209876332600073294805239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43786007107200390905627941 8209876332600073294805239)
            ·
              refine ⟨12314814498900109942207859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209876332600073294805239 12314814498900109942207859)
              ·
                refine ⟨18472221748350164913311789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314814498900109942207859 18472221748350164913311789)
                ·
                  refine ⟨6927083155631311842491921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18472221748350164913311789 6927083155631311842491921)
                  ·
                    refine ⟨5195312366723483881868941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6927083155631311842491921 5195312366723483881868941)
                    ·
                      refine ⟨1948242137521306455700853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195312366723483881868941 1948242137521306455700853)
                      ·
                        rfl

theorem cell23_3794188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3794188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794188 prefixEnd_3794188 := by exact prefixLift 3794188
  have htrace : WordTrace (prefixWord ++ tailWord_3794188) baseStart_3794188 baseEnd_3794188 := by
    simpa [prefixWord, tailWord_3794188, baseEnd_3794188] using wordTrace_append hprefix tailTrace_3794188
  have hstable : (prefixWord ++ tailWord_3794188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794188).length < 2 ^ (prefixWord ++ tailWord_3794188).sum := by decide
  have hdescent : baseEnd_3794188 < baseStart_3794188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794205 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3794205 : Nat := 118140960795 + 3794205 * 2 ^ 59
def prefixEnd_3794205 : Nat := 4983230072969 + 3 ^ 40 * 3794205 * 2
def baseEnd_3794205 : Nat := 1948250866692432889188275

theorem tailTrace_3794205 : CollatzResearch.WordTrace tailWord_3794205 prefixEnd_3794205 1948250866692432889188275 := by
  unfold tailWord_3794205
  simp only [CollatzResearch.WordTrace]
  refine ⟨138386025219250758469304069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92257350146167172312869379 138386025219250758469304069)
  ·
    refine ⟨25947379728609517212994513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138386025219250758469304069 25947379728609517212994513)
    ·
      refine ⟨19460534796457137909745885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25947379728609517212994513 19460534796457137909745885)
      ·
        refine ⟨7297700548671426716154707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19460534796457137909745885 7297700548671426716154707)
        ·
          refine ⟨10946550823007140074232061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297700548671426716154707 10946550823007140074232061)
          ·
            refine ⟨4104956558627677527837023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10946550823007140074232061 4104956558627677527837023)
            ·
              refine ⟨6157434837941516291755535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104956558627677527837023 6157434837941516291755535)
              ·
                refine ⟨9236152256912274437633303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157434837941516291755535 9236152256912274437633303)
                ·
                  refine ⟨13854228385368411656449955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236152256912274437633303 13854228385368411656449955)
                  ·
                    refine ⟨20781342578052617484674933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13854228385368411656449955 20781342578052617484674933)
                    ·
                      refine ⟨1948250866692432889188275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20781342578052617484674933 1948250866692432889188275)
                      ·
                        rfl

theorem cell23_3794205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3794205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794205 prefixEnd_3794205 := by exact prefixLift 3794205
  have htrace : WordTrace (prefixWord ++ tailWord_3794205) baseStart_3794205 baseEnd_3794205 := by
    simpa [prefixWord, tailWord_3794205, baseEnd_3794205] using wordTrace_append hprefix tailTrace_3794205
  have hstable : (prefixWord ++ tailWord_3794205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794205).length < 2 ^ (prefixWord ++ tailWord_3794205).sum := by decide
  have hdescent : baseEnd_3794205 < baseStart_3794205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794253 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3794253 : Nat := 118140960795 + 3794253 * 2 ^ 59
def prefixEnd_3794253 : Nat := 4983230072969 + 3 ^ 40 * 3794253 * 2
def baseEnd_3794253 : Nat := 1948275513763848701388055

theorem tailTrace_3794253 : CollatzResearch.WordTrace tailWord_3794253 prefixEnd_3794253 1948275513763848701388055 := by
  unfold tailWord_3794253
  simp only [CollatzResearch.WordTrace]
  refine ⟨138387775923076862667051413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92258517282051241778034275 138387775923076862667051413)
  ·
    refine ⟨6486926996394227937518035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138387775923076862667051413 6486926996394227937518035)
    ·
      refine ⟨9730390494591341906277053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6486926996394227937518035 9730390494591341906277053)
      ·
        refine ⟨3648896435471753214853895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9730390494591341906277053 3648896435471753214853895)
        ·
          refine ⟨5473344653207629822280843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648896435471753214853895 5473344653207629822280843)
          ·
            refine ⟨8210016979811444733421265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473344653207629822280843 8210016979811444733421265)
            ·
              refine ⟨6157512734858583550065949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210016979811444733421265 6157512734858583550065949)
              ·
                refine ⟨2309067275571968831274731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6157512734858583550065949 2309067275571968831274731)
                ·
                  refine ⟨3463600913357953246912097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309067275571968831274731 3463600913357953246912097)
                  ·
                    refine ⟨2597700685018464935184073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3463600913357953246912097 2597700685018464935184073)
                    ·
                      refine ⟨1948275513763848701388055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597700685018464935184073 1948275513763848701388055)
                      ·
                        rfl

theorem cell23_3794253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3794253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794253 prefixEnd_3794253 := by exact prefixLift 3794253
  have htrace : WordTrace (prefixWord ++ tailWord_3794253) baseStart_3794253 baseEnd_3794253 := by
    simpa [prefixWord, tailWord_3794253, baseEnd_3794253] using wordTrace_append hprefix tailTrace_3794253
  have hstable : (prefixWord ++ tailWord_3794253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794253).length < 2 ^ (prefixWord ++ tailWord_3794253).sum := by decide
  have hdescent : baseEnd_3794253 < baseStart_3794253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794286 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3794286 : Nat := 118140960795 + 3794286 * 2 ^ 59
def prefixEnd_3794286 : Nat := 4983230072969 + 3 ^ 40 * 3794286 * 2
def baseEnd_3794286 : Nat := 1948292458625447072275403

theorem tailTrace_3794286 : CollatzResearch.WordTrace tailWord_3794286 prefixEnd_3794286 1948292458625447072275403 := by
  unfold tailWord_3794286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298622441494663662875339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92259319687971539535335141 17298622441494663662875339)
  ·
    refine ⟨25947933662241995494313009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17298622441494663662875339 25947933662241995494313009)
    ·
      refine ⟨19460950246681496620734757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25947933662241995494313009 19460950246681496620734757)
      ·
        refine ⟨3648928171252780616387767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19460950246681496620734757 3648928171252780616387767)
        ·
          refine ⟨5473392256879170924581651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648928171252780616387767 5473392256879170924581651)
          ·
            refine ⟨8210088385318756386872477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473392256879170924581651 8210088385318756386872477)
            ·
              refine ⟨3078783144494533645077179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8210088385318756386872477 3078783144494533645077179)
              ·
                refine ⟨4618174716741800467615769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078783144494533645077179 4618174716741800467615769)
                ·
                  refine ⟨3463631037556350350711827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4618174716741800467615769 3463631037556350350711827)
                  ·
                    refine ⟨5195446556334525526067741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463631037556350350711827 5195446556334525526067741)
                    ·
                      refine ⟨1948292458625447072275403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195446556334525526067741 1948292458625447072275403)
                      ·
                        rfl

theorem cell23_3794286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3794286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794286 prefixEnd_3794286 := by exact prefixLift 3794286
  have htrace : WordTrace (prefixWord ++ tailWord_3794286) baseStart_3794286 baseEnd_3794286 := by
    simpa [prefixWord, tailWord_3794286, baseEnd_3794286] using wordTrace_append hprefix tailTrace_3794286
  have hstable : (prefixWord ++ tailWord_3794286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794286).length < 2 ^ (prefixWord ++ tailWord_3794286).sum := by decide
  have hdescent : baseEnd_3794286 < baseStart_3794286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794321 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_3794321 : Nat := 118140960795 + 3794321 * 2 ^ 59
def prefixEnd_3794321 : Nat := 4983230072969 + 3 ^ 40 * 3794321 * 2
def baseEnd_3794321 : Nat := 1948310430448354435337741

theorem tailTrace_3794321 : CollatzResearch.WordTrace tailWord_3794321 prefixEnd_3794321 1948310430448354435337741 := by
  unfold tailWord_3794321
  simp only [CollatzResearch.WordTrace]
  refine ⟨138390256086830510280526817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92260170724553673520351211 138390256086830510280526817)
  ·
    refine ⟨103792692065122882710395113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138390256086830510280526817 103792692065122882710395113)
    ·
      refine ⟨77844519048842162032796335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103792692065122882710395113 77844519048842162032796335)
      ·
        refine ⟨116766778573263243049194503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77844519048842162032796335 116766778573263243049194503)
        ·
          refine ⟨175150167859894864573791755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116766778573263243049194503 175150167859894864573791755)
          ·
            refine ⟨262725251789842296860687633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175150167859894864573791755 262725251789842296860687633)
            ·
              refine ⟨197043938842381722645515725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262725251789842296860687633 197043938842381722645515725)
              ·
                refine ⟨73891477065893145992068397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197043938842381722645515725 73891477065893145992068397)
                ·
                  refine ⟨27709303899709929747025649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73891477065893145992068397 27709303899709929747025649)
                  ·
                    refine ⟨20781977924782447310269237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27709303899709929747025649 20781977924782447310269237)
                    ·
                      refine ⟨1948310430448354435337741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20781977924782447310269237 1948310430448354435337741)
                      ·
                        rfl

theorem cell23_3794321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_3794321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794321 prefixEnd_3794321 := by exact prefixLift 3794321
  have htrace : WordTrace (prefixWord ++ tailWord_3794321) baseStart_3794321 baseEnd_3794321 := by
    simpa [prefixWord, tailWord_3794321, baseEnd_3794321] using wordTrace_append hprefix tailTrace_3794321
  have hstable : (prefixWord ++ tailWord_3794321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794321).length < 2 ^ (prefixWord ++ tailWord_3794321).sum := by decide
  have hdescent : baseEnd_3794321 < baseStart_3794321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794332 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 7]
def baseStart_3794332 : Nat := 118140960795 + 3794332 * 2 ^ 59
def prefixEnd_3794332 : Nat := 4983230072969 + 3 ^ 40 * 3794332 * 2
def baseEnd_3794332 : Nat := 216479564303950432477799

theorem tailTrace_3794332 : CollatzResearch.WordTrace tailWord_3794332 prefixEnd_3794332 216479564303950432477799 := by
  unfold tailWord_3794332
  simp only [CollatzResearch.WordTrace]
  refine ⟨69195328644895329579588625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92260438193193772772784833 69195328644895329579588625)
  ·
    refine ⟨51896496483671497184691469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69195328644895329579588625 51896496483671497184691469)
    ·
      refine ⟨19461186181376811444259301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51896496483671497184691469 19461186181376811444259301)
      ·
        refine ⟨3648972409008152145798619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19461186181376811444259301 3648972409008152145798619)
        ·
          refine ⟨5473458613512228218697929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648972409008152145798619 5473458613512228218697929)
          ·
            refine ⟨4105093960134171164023447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473458613512228218697929 4105093960134171164023447)
            ·
              refine ⟨6157640940201256746035171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105093960134171164023447 6157640940201256746035171)
              ·
                refine ⟨9236461410301885119052757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157640940201256746035171 9236461410301885119052757)
                ·
                  refine ⟨216479564303950432477799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9236461410301885119052757 216479564303950432477799)
                  ·
                    rfl

theorem cell23_3794332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_3794332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794332 prefixEnd_3794332 := by exact prefixLift 3794332
  have htrace : WordTrace (prefixWord ++ tailWord_3794332) baseStart_3794332 baseEnd_3794332 := by
    simpa [prefixWord, tailWord_3794332, baseEnd_3794332] using wordTrace_append hprefix tailTrace_3794332
  have hstable : (prefixWord ++ tailWord_3794332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794332).length < 2 ^ (prefixWord ++ tailWord_3794332).sum := by decide
  have hdescent : baseEnd_3794332 < baseStart_3794332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794338 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3794338 : Nat := 118140960795 + 3794338 * 2 ^ 59
def prefixEnd_3794338 : Nat := 4983230072969 + 3 ^ 40 * 3794338 * 2
def baseEnd_3794338 : Nat := 1948319159619480868825163

theorem tailTrace_3794338 : CollatzResearch.WordTrace tailWord_3794338 prefixEnd_3794338 1948319159619480868825163 := by
  unfold tailWord_3794338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34597719031942230545973917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92260584085179281455930445 34597719031942230545973917)
  ·
    refine ⟨12974144636978336454740219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34597719031942230545973917 12974144636978336454740219)
    ·
      refine ⟨19461216955467504682110329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12974144636978336454740219 19461216955467504682110329)
      ·
        refine ⟨14595912716600628511582747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19461216955467504682110329 14595912716600628511582747)
        ·
          refine ⟨21893869074900942767374121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14595912716600628511582747 21893869074900942767374121)
          ·
            refine ⟨16420401806175707075530591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21893869074900942767374121 16420401806175707075530591)
            ·
              refine ⟨24630602709263560613295887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16420401806175707075530591 24630602709263560613295887)
              ·
                refine ⟨36945904063895340919943831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24630602709263560613295887 36945904063895340919943831)
                ·
                  refine ⟨55418856095843011379915747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36945904063895340919943831 55418856095843011379915747)
                  ·
                    refine ⟨83128284143764517069873621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55418856095843011379915747 83128284143764517069873621)
                    ·
                      refine ⟨1948319159619480868825163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83128284143764517069873621 1948319159619480868825163)
                      ·
                        rfl

theorem cell23_3794338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3794338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794338 prefixEnd_3794338 := by exact prefixLift 3794338
  have htrace : WordTrace (prefixWord ++ tailWord_3794338) baseStart_3794338 baseEnd_3794338 := by
    simpa [prefixWord, tailWord_3794338, baseEnd_3794338] using wordTrace_append hprefix tailTrace_3794338
  have hstable : (prefixWord ++ tailWord_3794338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794338).length < 2 ^ (prefixWord ++ tailWord_3794338).sum := by decide
  have hdescent : baseEnd_3794338 < baseStart_3794338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794341 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3794341 : Nat := 118140960795 + 3794341 * 2 ^ 59
def prefixEnd_3794341 : Nat := 4983230072969 + 3 ^ 40 * 3794341 * 2
def baseEnd_3794341 : Nat := 649440233353814785695883

theorem tailTrace_3794341 : CollatzResearch.WordTrace tailWord_3794341 prefixEnd_3794341 649440233353814785695883 := by
  unfold tailWord_3794341
  simp only [CollatzResearch.WordTrace]
  refine ⟨138390985546758053696254877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92260657031172035797503251 138390985546758053696254877)
  ·
    refine ⟨51896619580034270136095579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138390985546758053696254877 51896619580034270136095579)
    ·
      refine ⟨77844929370051405204143369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51896619580034270136095579 77844929370051405204143369)
      ·
        refine ⟨58383697027538553903107527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77844929370051405204143369 58383697027538553903107527)
        ·
          refine ⟨87575545541307830854661291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58383697027538553903107527 87575545541307830854661291)
          ·
            refine ⟨131363318311961746281991937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87575545541307830854661291 131363318311961746281991937)
            ·
              refine ⟨98522488733971309711493953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131363318311961746281991937 98522488733971309711493953)
              ·
                refine ⟨73891866550478482283620465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98522488733971309711493953 73891866550478482283620465)
                ·
                  refine ⟨55418899912858861712715349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73891866550478482283620465 55418899912858861712715349)
                  ·
                    refine ⟨649440233353814785695883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55418899912858861712715349 649440233353814785695883)
                    ·
                      rfl

theorem cell23_3794341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3794341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794341 prefixEnd_3794341 := by exact prefixLift 3794341
  have htrace : WordTrace (prefixWord ++ tailWord_3794341) baseStart_3794341 baseEnd_3794341 := by
    simpa [prefixWord, tailWord_3794341, baseEnd_3794341] using wordTrace_append hprefix tailTrace_3794341
  have hstable : (prefixWord ++ tailWord_3794341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794341).length < 2 ^ (prefixWord ++ tailWord_3794341).sum := by decide
  have hdescent : baseEnd_3794341 < baseStart_3794341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794351 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_3794351 : Nat := 118140960795 + 3794351 * 2 ^ 59
def prefixEnd_3794351 : Nat := 4983230072969 + 3 ^ 40 * 3794351 * 2
def baseEnd_3794351 : Nat := 1948325834867989317962603

theorem tailTrace_3794351 : CollatzResearch.WordTrace tailWord_3794351 prefixEnd_3794351 1948325834867989317962603 := by
  unfold tailWord_3794351
  simp only [CollatzResearch.WordTrace]
  refine ⟨138391350276721825404118907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92260900184481216936079271 138391350276721825404118907)
  ·
    refine ⟨207587025415082738106178361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138391350276721825404118907 207587025415082738106178361)
    ·
      refine ⟨155690269061312053579633771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207587025415082738106178361 155690269061312053579633771)
      ·
        refine ⟨233535403591968080369450657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155690269061312053579633771 233535403591968080369450657)
        ·
          refine ⟨175151552693976060277087993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233535403591968080369450657 175151552693976060277087993)
          ·
            refine ⟨131363664520482045207815995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175151552693976060277087993 131363664520482045207815995)
            ·
              refine ⟨197045496780723067811723993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131363664520482045207815995 197045496780723067811723993)
              ·
                refine ⟨147784122585542300858792995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197045496780723067811723993 147784122585542300858792995)
                ·
                  refine ⟨221676183878313451288189493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147784122585542300858792995 221676183878313451288189493)
                  ·
                    refine ⟨20782142238591886058267765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221676183878313451288189493 20782142238591886058267765)
                    ·
                      refine ⟨1948325834867989317962603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20782142238591886058267765 1948325834867989317962603)
                      ·
                        rfl

theorem cell23_3794351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_3794351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794351 prefixEnd_3794351 := by exact prefixLift 3794351
  have htrace : WordTrace (prefixWord ++ tailWord_3794351) baseStart_3794351 baseEnd_3794351 := by
    simpa [prefixWord, tailWord_3794351, baseEnd_3794351] using wordTrace_append hprefix tailTrace_3794351
  have hstable : (prefixWord ++ tailWord_3794351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794351).length < 2 ^ (prefixWord ++ tailWord_3794351).sum := by decide
  have hdescent : baseEnd_3794351 < baseStart_3794351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794365 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3794365 : Nat := 118140960795 + 3794365 * 2 ^ 59
def prefixEnd_3794365 : Nat := 4983230072969 + 3 ^ 40 * 3794365 * 2
def baseEnd_3794365 : Nat := 1948333023597152263187539

theorem tailTrace_3794365 : CollatzResearch.WordTrace tailWord_3794365 prefixEnd_3794365 1948333023597152263187539 := by
  unfold tailWord_3794365
  simp only [CollatzResearch.WordTrace]
  refine ⟨138391860898671105795128549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92261240599114070530085699 138391860898671105795128549)
  ·
    refine ⟨25948473918500832336586603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138391860898671105795128549 25948473918500832336586603)
    ·
      refine ⟨38922710877751248504879905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25948473918500832336586603 38922710877751248504879905)
      ·
        refine ⟨29192033158313436378659929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38922710877751248504879905 29192033158313436378659929)
        ·
          refine ⟨21894024868735077283994947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29192033158313436378659929 21894024868735077283994947)
          ·
            refine ⟨32841037303102615925992421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21894024868735077283994947 32841037303102615925992421)
            ·
              refine ⟨6157694494331740486123579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32841037303102615925992421 6157694494331740486123579)
              ·
                refine ⟨9236541741497610729185369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157694494331740486123579 9236541741497610729185369)
                ·
                  refine ⟨6927406306123208046889027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9236541741497610729185369 6927406306123208046889027)
                  ·
                    refine ⟨10391109459184812070333541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927406306123208046889027 10391109459184812070333541)
                    ·
                      refine ⟨1948333023597152263187539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10391109459184812070333541 1948333023597152263187539)
                      ·
                        rfl

theorem cell23_3794365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3794365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794365 prefixEnd_3794365 := by exact prefixLift 3794365
  have htrace : WordTrace (prefixWord ++ tailWord_3794365) baseStart_3794365 baseEnd_3794365 := by
    simpa [prefixWord, tailWord_3794365, baseEnd_3794365] using wordTrace_append hprefix tailTrace_3794365
  have hstable : (prefixWord ++ tailWord_3794365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794365).length < 2 ^ (prefixWord ++ tailWord_3794365).sum := by decide
  have hdescent : baseEnd_3794365 < baseStart_3794365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794368 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_3794368 : Nat := 118140960795 + 3794368 * 2 ^ 59
def prefixEnd_3794368 : Nat := 4983230072969 + 3 ^ 40 * 3794368 * 2
def baseEnd_3794368 : Nat := 1948334564039115751450025

theorem tailTrace_3794368 : CollatzResearch.WordTrace tailWord_3794368 prefixEnd_3794368 1948334564039115751450025 := by
  unfold tailWord_3794368
  simp only [CollatzResearch.WordTrace]
  refine ⟨69195985158830118653743879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92261313545106824871658505 69195985158830118653743879)
  ·
    refine ⟨103793977738245177980615819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69195985158830118653743879 103793977738245177980615819)
    ·
      refine ⟨155690966607367766970923729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103793977738245177980615819 155690966607367766970923729)
      ·
        refine ⟨116768224955525825228192797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155690966607367766970923729 116768224955525825228192797)
        ·
          refine ⟨43788084358322184460572299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116768224955525825228192797 43788084358322184460572299)
          ·
            refine ⟨65682126537483276690858449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43788084358322184460572299 65682126537483276690858449)
            ·
              refine ⟨49261594903112457518143837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65682126537483276690858449 49261594903112457518143837)
              ·
                refine ⟨18473098088667171569303939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49261594903112457518143837 18473098088667171569303939)
                ·
                  refine ⟨27709647133000757353955909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18473098088667171569303939 27709647133000757353955909)
                  ·
                    refine ⟨5195558837437642003866733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27709647133000757353955909 5195558837437642003866733)
                    ·
                      refine ⟨1948334564039115751450025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195558837437642003866733 1948334564039115751450025)
                      ·
                        rfl

theorem cell23_3794368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_3794368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794368 prefixEnd_3794368 := by exact prefixLift 3794368
  have htrace : WordTrace (prefixWord ++ tailWord_3794368) baseStart_3794368 baseEnd_3794368 := by
    simpa [prefixWord, tailWord_3794368, baseEnd_3794368] using wordTrace_append hprefix tailTrace_3794368
  have hstable : (prefixWord ++ tailWord_3794368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794368).length < 2 ^ (prefixWord ++ tailWord_3794368).sum := by decide
  have hdescent : baseEnd_3794368 < baseStart_3794368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794371 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 10]
def baseStart_3794371 : Nat := 118140960795 + 3794371 * 2 ^ 59
def prefixEnd_3794371 : Nat := 4983230072969 + 3 ^ 40 * 3794371 * 2
def baseEnd_3794371 : Nat := 216481789386786582190279

theorem tailTrace_3794371 : CollatzResearch.WordTrace tailWord_3794371 prefixEnd_3794371 216481789386786582190279 := by
  unfold tailWord_3794371
  simp only [CollatzResearch.WordTrace]
  refine ⟨138392079736649368819846967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92261386491099579213231311 138392079736649368819846967)
  ·
    refine ⟨207588119604974053229770451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138392079736649368819846967 207588119604974053229770451)
    ·
      refine ⟨311382179407461079844655677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207588119604974053229770451 311382179407461079844655677)
      ·
        refine ⟨116768317277797904941745879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311382179407461079844655677 116768317277797904941745879)
        ·
          refine ⟨175152475916696857412618819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116768317277797904941745879 175152475916696857412618819)
          ·
            refine ⟨262728713875045286118928229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175152475916696857412618819 262728713875045286118928229)
            ·
              refine ⟨49261633851570991147299043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262728713875045286118928229 49261633851570991147299043)
              ·
                refine ⟨73892450777356486720948565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49261633851570991147299043 73892450777356486720948565)
                ·
                  refine ⟨216481789386786582190279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 73892450777356486720948565 216481789386786582190279)
                  ·
                    rfl

theorem cell23_3794371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 10].length) (baseStart_3794371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794371 prefixEnd_3794371 := by exact prefixLift 3794371
  have htrace : WordTrace (prefixWord ++ tailWord_3794371) baseStart_3794371 baseEnd_3794371 := by
    simpa [prefixWord, tailWord_3794371, baseEnd_3794371] using wordTrace_append hprefix tailTrace_3794371
  have hstable : (prefixWord ++ tailWord_3794371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794371).length < 2 ^ (prefixWord ++ tailWord_3794371).sum := by decide
  have hdescent : baseEnd_3794371 < baseStart_3794371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794405 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 6]
def baseStart_3794405 : Nat := 118140960795 + 3794405 * 2 ^ 59
def prefixEnd_3794405 : Nat := 4983230072969 + 3 ^ 40 * 3794405 * 2
def baseEnd_3794405 : Nat := 216483729202592456298595

theorem tailTrace_3794405 : CollatzResearch.WordTrace tailWord_3794405 prefixEnd_3794405 216483729202592456298595 := by
  unfold tailWord_3794405
  simp only [CollatzResearch.WordTrace]
  refine ⟨138393319818526192626584669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92262213212350795084389779 138393319818526192626584669)
  ·
    refine ⟨51897494931947322234969251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138393319818526192626584669 51897494931947322234969251)
    ·
      refine ⟨77846242397920983352453877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51897494931947322234969251 77846242397920983352453877)
      ·
        refine ⟨7298085224805092189292551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77846242397920983352453877 7298085224805092189292551)
        ·
          refine ⟨10947127837207638283938827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298085224805092189292551 10947127837207638283938827)
          ·
            refine ⟨16420691755811457425908241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10947127837207638283938827 16420691755811457425908241)
            ·
              refine ⟨12315518816858593069431181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16420691755811457425908241 12315518816858593069431181)
              ·
                refine ⟨4618319556321972401036693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12315518816858593069431181 4618319556321972401036693)
                ·
                  refine ⟨216483729202592456298595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4618319556321972401036693 216483729202592456298595)
                  ·
                    rfl

theorem cell23_3794405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_3794405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794405 prefixEnd_3794405 := by exact prefixLift 3794405
  have htrace : WordTrace (prefixWord ++ tailWord_3794405) baseStart_3794405 baseEnd_3794405 := by
    simpa [prefixWord, tailWord_3794405, baseEnd_3794405] using wordTrace_append hprefix tailTrace_3794405
  have hstable : (prefixWord ++ tailWord_3794405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794405).length < 2 ^ (prefixWord ++ tailWord_3794405).sum := by decide
  have hdescent : baseEnd_3794405 < baseStart_3794405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794415 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 3]
def baseStart_3794415 : Nat := 118140960795 + 3794415 * 2 ^ 59
def prefixEnd_3794415 : Nat := 4983230072969 + 3 ^ 40 * 3794415 * 2
def baseEnd_3794415 : Nat := 1948358697629877067562309

theorem tailTrace_3794415 : CollatzResearch.WordTrace tailWord_3794415 prefixEnd_3794415 1948358697629877067562309 := by
  unfold tailWord_3794415
  simp only [CollatzResearch.WordTrace]
  refine ⟨138393684548489964334448699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92262456365659976222965799 138393684548489964334448699)
  ·
    refine ⟨207590526822734946501673049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138393684548489964334448699 207590526822734946501673049)
    ·
      refine ⟨155692895117051209876254787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207590526822734946501673049 155692895117051209876254787)
      ·
        refine ⟨233539342675576814814382181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155692895117051209876254787 233539342675576814814382181)
        ·
          refine ⟨43788626751670652777696659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233539342675576814814382181 43788626751670652777696659)
          ·
            refine ⟨65682940127505979166544989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43788626751670652777696659 65682940127505979166544989)
            ·
              refine ⟨24631102547814742187454371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65682940127505979166544989 24631102547814742187454371)
              ·
                refine ⟨36946653821722113281181557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24631102547814742187454371 36946653821722113281181557)
                ·
                  refine ⟨3463748795786448120110771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36946653821722113281181557 3463748795786448120110771)
                  ·
                    refine ⟨5195623193679672180166157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463748795786448120110771 5195623193679672180166157)
                    ·
                      refine ⟨1948358697629877067562309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195623193679672180166157 1948358697629877067562309)
                      ·
                        rfl

theorem cell23_3794415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_3794415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794415 prefixEnd_3794415 := by exact prefixLift 3794415
  have htrace : WordTrace (prefixWord ++ tailWord_3794415) baseStart_3794415 baseEnd_3794415 := by
    simpa [prefixWord, tailWord_3794415, baseEnd_3794415] using wordTrace_append hprefix tailTrace_3794415
  have hstable : (prefixWord ++ tailWord_3794415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794415).length < 2 ^ (prefixWord ++ tailWord_3794415).sum := by decide
  have hdescent : baseEnd_3794415 < baseStart_3794415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794465 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3794465 : Nat := 118140960795 + 3794465 * 2 ^ 59
def prefixEnd_3794465 : Nat := 4983230072969 + 3 ^ 40 * 3794465 * 2
def baseEnd_3794465 : Nat := 649461457220867290645693

theorem tailTrace_3794465 : CollatzResearch.WordTrace tailWord_3794465 prefixEnd_3794465 649461457220867290645693 := by
  unfold tailWord_3794465
  simp only [CollatzResearch.WordTrace]
  refine ⟨138395508198308822873768849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92263672132205881915845899 138395508198308822873768849)
  ·
    refine ⟨103796631148731617155326637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138395508198308822873768849 103796631148731617155326637)
    ·
      refine ⟨38923736680774356433247489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103796631148731617155326637 38923736680774356433247489)
      ·
        refine ⟨29192802510580767324935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38923736680774356433247489 29192802510580767324935617)
        ·
          refine ⟨21894601882935575493701713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29192802510580767324935617 21894601882935575493701713)
          ·
            refine ⟨16420951412201681620276285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21894601882935575493701713 16420951412201681620276285)
            ·
              refine ⟨6157856779575630607603607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16420951412201681620276285 6157856779575630607603607)
              ·
                refine ⟨9236785169363445911405411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157856779575630607603607 9236785169363445911405411)
                ·
                  refine ⟨13855177754045168867108117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236785169363445911405411 13855177754045168867108117)
                  ·
                    refine ⟨649461457220867290645693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13855177754045168867108117 649461457220867290645693)
                    ·
                      rfl

theorem cell23_3794465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3794465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794465 prefixEnd_3794465 := by exact prefixLift 3794465
  have htrace : WordTrace (prefixWord ++ tailWord_3794465) baseStart_3794465 baseEnd_3794465 := by
    simpa [prefixWord, tailWord_3794465, baseEnd_3794465] using wordTrace_append hprefix tailTrace_3794465
  have hstable : (prefixWord ++ tailWord_3794465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794465).length < 2 ^ (prefixWord ++ tailWord_3794465).sum := by decide
  have hdescent : baseEnd_3794465 < baseStart_3794465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794492 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3794492 : Nat := 118140960795 + 3794492 * 2 ^ 59
def prefixEnd_3794492 : Nat := 4983230072969 + 3 ^ 40 * 3794492 * 2
def baseEnd_3794492 : Nat := 1948398235640273266299455

theorem tailTrace_3794492 : CollatzResearch.WordTrace tailWord_3794492 prefixEnd_3794492 1948398235640273266299455 := by
  unfold tailWord_3794492
  simp only [CollatzResearch.WordTrace]
  refine ⟨69198246484605503242500865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92264328646140670990001153 69198246484605503242500865)
  ·
    refine ⟨51898684863454127431875649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69198246484605503242500865 51898684863454127431875649)
    ·
      refine ⟨38924013647590595573906737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51898684863454127431875649 38924013647590595573906737)
      ·
        refine ⟨29193010235692946680430053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38924013647590595573906737 29193010235692946680430053)
        ·
          refine ⟨5473689419192427502580635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29193010235692946680430053 5473689419192427502580635)
          ·
            refine ⟨8210534128788641253870953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473689419192427502580635 8210534128788641253870953)
            ·
              refine ⟨6157900596591480940403215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210534128788641253870953 6157900596591480940403215)
              ·
                refine ⟨9236850894887221410604823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157900596591480940403215 9236850894887221410604823)
                ·
                  refine ⟨13855276342330832115907235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236850894887221410604823 13855276342330832115907235)
                  ·
                    refine ⟨20782914513496248173860853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13855276342330832115907235 20782914513496248173860853)
                    ·
                      refine ⟨1948398235640273266299455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20782914513496248173860853 1948398235640273266299455)
                      ·
                        rfl

theorem cell23_3794492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3794492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794492 prefixEnd_3794492 := by exact prefixLift 3794492
  have htrace : WordTrace (prefixWord ++ tailWord_3794492) baseStart_3794492 baseEnd_3794492 := by
    simpa [prefixWord, tailWord_3794492, baseEnd_3794492] using wordTrace_append hprefix tailTrace_3794492
  have hstable : (prefixWord ++ tailWord_3794492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794492).length < 2 ^ (prefixWord ++ tailWord_3794492).sum := by decide
  have hdescent : baseEnd_3794492 < baseStart_3794492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794528 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_3794528 : Nat := 118140960795 + 3794528 * 2 ^ 59
def prefixEnd_3794528 : Nat := 4983230072969 + 3 ^ 40 * 3794528 * 2
def baseEnd_3794528 : Nat := 1948416720943835125449289

theorem tailTrace_3794528 : CollatzResearch.WordTrace tailWord_3794528 prefixEnd_3794528 1948416720943835125449289 := by
  unfold tailWord_3794528
  simp only [CollatzResearch.WordTrace]
  refine ⟨69198902998540292316656119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92265203998053723088874825 69198902998540292316656119)
  ·
    refine ⟨103798354497810438474984179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69198902998540292316656119 103798354497810438474984179)
    ·
      refine ⟨155697531746715657712476269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103798354497810438474984179 155697531746715657712476269)
      ·
        refine ⟨58386574405018371642178601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155697531746715657712476269 58386574405018371642178601)
        ·
          refine ⟨43789930803763778731633951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58386574405018371642178601 43789930803763778731633951)
          ·
            refine ⟨65684896205645668097450927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43789930803763778731633951 65684896205645668097450927)
            ·
              refine ⟨98527344308468502146176391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65684896205645668097450927 98527344308468502146176391)
              ·
                refine ⟨147791016462702753219264587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98527344308468502146176391 147791016462702753219264587)
                ·
                  refine ⟨221686524694054129828896881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147791016462702753219264587 221686524694054129828896881)
                  ·
                    refine ⟨166264893520540597371672661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221686524694054129828896881 166264893520540597371672661)
                    ·
                      refine ⟨1948416720943835125449289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 166264893520540597371672661 1948416720943835125449289)
                      ·
                        rfl

theorem cell23_3794528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_3794528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794528 prefixEnd_3794528 := by exact prefixLift 3794528
  have htrace : WordTrace (prefixWord ++ tailWord_3794528) baseStart_3794528 baseEnd_3794528 := by
    simpa [prefixWord, tailWord_3794528, baseEnd_3794528] using wordTrace_append hprefix tailTrace_3794528
  have hstable : (prefixWord ++ tailWord_3794528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794528).length < 2 ^ (prefixWord ++ tailWord_3794528).sum := by decide
  have hdescent : baseEnd_3794528 < baseStart_3794528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794565 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_3794565 : Nat := 118140960795 + 3794565 * 2 ^ 59
def prefixEnd_3794565 : Nat := 4983230072969 + 3 ^ 40 * 3794565 * 2
def baseEnd_3794565 : Nat := 1948435719728051480686619

theorem tailTrace_3794565 : CollatzResearch.WordTrace tailWord_3794565 prefixEnd_3794565 1948435719728051480686619 := by
  unfold tailWord_3794565
  simp only [CollatzResearch.WordTrace]
  refine ⟨138399155497946539952409149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92266103665297693301606099 138399155497946539952409149)
  ·
    refine ⟨51899683311729952482153431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138399155497946539952409149 51899683311729952482153431)
    ·
      refine ⟨77849524967594928723230147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51899683311729952482153431 77849524967594928723230147)
      ·
        refine ⟨116774287451392393084845221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77849524967594928723230147 116774287451392393084845221)
        ·
          refine ⟨21895178897136073703408479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116774287451392393084845221 21895178897136073703408479)
          ·
            refine ⟨32842768345704110555112719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21895178897136073703408479 32842768345704110555112719)
            ·
              refine ⟨49264152518556165832669079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32842768345704110555112719 49264152518556165832669079)
              ·
                refine ⟨73896228777834248749003619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49264152518556165832669079 73896228777834248749003619)
                ·
                  refine ⟨110844343166751373123505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73896228777834248749003619 110844343166751373123505429)
                  ·
                    refine ⟨5195828585941470615164317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110844343166751373123505429 5195828585941470615164317)
                    ·
                      refine ⟨1948435719728051480686619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195828585941470615164317 1948435719728051480686619)
                      ·
                        rfl

theorem cell23_3794565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_3794565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794565 prefixEnd_3794565 := by exact prefixLift 3794565
  have htrace : WordTrace (prefixWord ++ tailWord_3794565) baseStart_3794565 baseEnd_3794565 := by
    simpa [prefixWord, tailWord_3794565, baseEnd_3794565] using wordTrace_append hprefix tailTrace_3794565
  have hstable : (prefixWord ++ tailWord_3794565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794565).length < 2 ^ (prefixWord ++ tailWord_3794565).sum := by decide
  have hdescent : baseEnd_3794565 < baseStart_3794565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794595 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 3]
def baseStart_3794595 : Nat := 118140960795 + 3794595 * 2 ^ 59
def prefixEnd_3794595 : Nat := 4983230072969 + 3 ^ 40 * 3794595 * 2
def baseEnd_3794595 : Nat := 1948451124147686363311481

theorem tailTrace_3794595 : CollatzResearch.WordTrace tailWord_3794595 prefixEnd_3794595 1948451124147686363311481 := by
  unfold tailWord_3794595
  simp only [CollatzResearch.WordTrace]
  refine ⟨138400249687837855076001239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92266833125225236717334159 138400249687837855076001239)
  ·
    refine ⟨207600374531756782614001859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138400249687837855076001239 207600374531756782614001859)
    ·
      refine ⟨311400561797635173921002789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207600374531756782614001859 311400561797635173921002789)
      ·
        refine ⟨58387605337056595110188023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311400561797635173921002789 58387605337056595110188023)
        ·
          refine ⟨87581408005584892665282035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58387605337056595110188023 87581408005584892665282035)
          ·
            refine ⟨131372112008377338997923053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87581408005584892665282035 131372112008377338997923053)
            ·
              refine ⟨49264542003141502124221145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131372112008377338997923053 49264542003141502124221145)
              ·
                refine ⟨36948406502356126593165859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49264542003141502124221145 36948406502356126593165859)
                ·
                  refine ⟨55422609753534189889748789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36948406502356126593165859 55422609753534189889748789)
                  ·
                    refine ⟨5195869664393830302163949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55422609753534189889748789 5195869664393830302163949)
                    ·
                      refine ⟨1948451124147686363311481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5195869664393830302163949 1948451124147686363311481)
                      ·
                        rfl

theorem cell23_3794595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_3794595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794595 prefixEnd_3794595 := by exact prefixLift 3794595
  have htrace : WordTrace (prefixWord ++ tailWord_3794595) baseStart_3794595 baseEnd_3794595 := by
    simpa [prefixWord, tailWord_3794595, baseEnd_3794595] using wordTrace_append hprefix tailTrace_3794595
  have hstable : (prefixWord ++ tailWord_3794595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794595).length < 2 ^ (prefixWord ++ tailWord_3794595).sum := by decide
  have hdescent : baseEnd_3794595 < baseStart_3794595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794600 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3794600 : Nat := 118140960795 + 3794600 * 2 ^ 59
def prefixEnd_3794600 : Nat := 4983230072969 + 3 ^ 40 * 3794600 * 2
def baseEnd_3794600 : Nat := 1948453691550958843748959

theorem tailTrace_3794600 : CollatzResearch.WordTrace tailWord_3794600 prefixEnd_3794600 1948453691550958843748959 := by
  unfold tailWord_3794600
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200216026409870464966627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92266954701879827286622169 69200216026409870464966627)
  ·
    refine ⟨103800324039614805697449941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69200216026409870464966627 103800324039614805697449941)
    ·
      refine ⟨2432820094678472008533983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 103800324039614805697449941 2432820094678472008533983)
      ·
        refine ⟨3649230142017708012800975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432820094678472008533983 3649230142017708012800975)
        ·
          refine ⟨5473845213026562019201463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649230142017708012800975 5473845213026562019201463)
          ·
            refine ⟨8210767819539843028802195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473845213026562019201463 8210767819539843028802195)
            ·
              refine ⟨12316151729309764543203293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210767819539843028802195 12316151729309764543203293)
              ·
                refine ⟨4618556898491161703701235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12316151729309764543203293 4618556898491161703701235)
                ·
                  refine ⟨6927835347736742555551853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618556898491161703701235 6927835347736742555551853)
                  ·
                    refine ⟨2597938255401278458331945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6927835347736742555551853 2597938255401278458331945)
                    ·
                      refine ⟨1948453691550958843748959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597938255401278458331945 1948453691550958843748959)
                      ·
                        rfl

theorem cell23_3794600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3794600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794600 prefixEnd_3794600 := by exact prefixLift 3794600
  have htrace : WordTrace (prefixWord ++ tailWord_3794600) baseStart_3794600 baseEnd_3794600 := by
    simpa [prefixWord, tailWord_3794600, baseEnd_3794600] using wordTrace_append hprefix tailTrace_3794600
  have hstable : (prefixWord ++ tailWord_3794600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794600).length < 2 ^ (prefixWord ++ tailWord_3794600).sum := by decide
  have hdescent : baseEnd_3794600 < baseStart_3794600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794630 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3794630 : Nat := 118140960795 + 3794630 * 2 ^ 59
def prefixEnd_3794630 : Nat := 4983230072969 + 3 ^ 40 * 3794630 * 2
def baseEnd_3794630 : Nat := 1948469095970593726373821

theorem tailTrace_3794630 : CollatzResearch.WordTrace tailWord_3794630 prefixEnd_3794630 1948469095970593726373821 := by
  unfold tailWord_3794630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325047695084720501672667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92267684161807370702350229 4325047695084720501672667)
  ·
    refine ⟨6487571542627080752509001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325047695084720501672667 6487571542627080752509001)
    ·
      refine ⟨4865678656970310564381751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487571542627080752509001 4865678656970310564381751)
      ·
        refine ⟨7298517985455465846572627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865678656970310564381751 7298517985455465846572627)
        ·
          refine ⟨10947776978183198769858941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298517985455465846572627 10947776978183198769858941)
          ·
            refine ⟨4105416366818699538697103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10947776978183198769858941 4105416366818699538697103)
            ·
              refine ⟨6158124550228049308045655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105416366818699538697103 6158124550228049308045655)
              ·
                refine ⟨9237186825342073962068483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158124550228049308045655 9237186825342073962068483)
                ·
                  refine ⟨13855780238013110943102725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9237186825342073962068483 13855780238013110943102725)
                  ·
                    refine ⟨2597958794627458301831761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13855780238013110943102725 2597958794627458301831761)
                    ·
                      refine ⟨1948469095970593726373821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2597958794627458301831761 1948469095970593726373821)
                      ·
                        rfl

theorem cell23_3794630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3794630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794630 prefixEnd_3794630 := by exact prefixLift 3794630
  have htrace : WordTrace (prefixWord ++ tailWord_3794630) baseStart_3794630 baseEnd_3794630 := by
    simpa [prefixWord, tailWord_3794630, baseEnd_3794630] using wordTrace_append hprefix tailTrace_3794630
  have hstable : (prefixWord ++ tailWord_3794630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794630).length < 2 ^ (prefixWord ++ tailWord_3794630).sum := by decide
  have hdescent : baseEnd_3794630 < baseStart_3794630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794653 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 5]
def baseStart_3794653 : Nat := 118140960795 + 3794653 * 2 ^ 59
def prefixEnd_3794653 : Nat := 4983230072969 + 3 ^ 40 * 3794653 * 2
def baseEnd_3794653 : Nat := 216497878447294126265135

theorem tailTrace_3794653 : CollatzResearch.WordTrace tailWord_3794653 prefixEnd_3794653 216497878447294126265135 := by
  unfold tailWord_3794653
  simp only [CollatzResearch.WordTrace]
  refine ⟨138402365121627730981612613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92268243414418487321075075 138402365121627730981612613)
  ·
    refine ⟨25950443460305199559052365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138402365121627730981612613 25950443460305199559052365)
    ·
      refine ⟨9731416297614449834644637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25950443460305199559052365 9731416297614449834644637)
      ·
        refine ⟨3649281111605418687991739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9731416297614449834644637 3649281111605418687991739)
        ·
          refine ⟨5473921667408128031987609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649281111605418687991739 5473921667408128031987609)
          ·
            refine ⟨4105441250556096023990707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473921667408128031987609 4105441250556096023990707)
            ·
              refine ⟨6158161875834144035986061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105441250556096023990707 6158161875834144035986061)
              ·
                refine ⟨2309310703437804013494773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6158161875834144035986061 2309310703437804013494773)
                ·
                  refine ⟨216497878447294126265135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2309310703437804013494773 216497878447294126265135)
                  ·
                    rfl

theorem cell23_3794653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_3794653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794653 prefixEnd_3794653 := by exact prefixLift 3794653
  have htrace : WordTrace (prefixWord ++ tailWord_3794653) baseStart_3794653 baseEnd_3794653 := by
    simpa [prefixWord, tailWord_3794653, baseEnd_3794653] using wordTrace_append hprefix tailTrace_3794653
  have hstable : (prefixWord ++ tailWord_3794653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794653).length < 2 ^ (prefixWord ++ tailWord_3794653).sum := by decide
  have hdescent : baseEnd_3794653 < baseStart_3794653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794669 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3794669 : Nat := 118140960795 + 3794669 * 2 ^ 59
def prefixEnd_3794669 : Nat := 4983230072969 + 3 ^ 40 * 3794669 * 2
def baseEnd_3794669 : Nat := 1948489121716119073786141

theorem tailTrace_3794669 : CollatzResearch.WordTrace tailWord_3794669 prefixEnd_3794669 1948489121716119073786141 := by
  unfold tailWord_3794669
  simp only [CollatzResearch.WordTrace]
  refine ⟨138402948689569765714195061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92268632459713177142796707 138402948689569765714195061)
  ·
    refine ⟨12975276439647165535705787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138402948689569765714195061 12975276439647165535705787)
    ·
      refine ⟨19462914659470748303558681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12975276439647165535705787 19462914659470748303558681)
      ·
        refine ⟨14597185994603061227669011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19462914659470748303558681 14597185994603061227669011)
        ·
          refine ⟨21895778991904591841503517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14597185994603061227669011 21895778991904591841503517)
          ·
            refine ⟨8210917121964221940563819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21895778991904591841503517 8210917121964221940563819)
            ·
              refine ⟨12316375682946332910845729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210917121964221940563819 12316375682946332910845729)
              ·
                refine ⟨9237281762209749683134297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12316375682946332910845729 9237281762209749683134297)
                ·
                  refine ⟨6927961321657312262350723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9237281762209749683134297 6927961321657312262350723)
                  ·
                    refine ⟨10391941982485968393526085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927961321657312262350723 10391941982485968393526085)
                    ·
                      refine ⟨1948489121716119073786141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10391941982485968393526085 1948489121716119073786141)
                      ·
                        rfl

theorem cell23_3794669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3794669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794669 prefixEnd_3794669 := by exact prefixLift 3794669
  have htrace : WordTrace (prefixWord ++ tailWord_3794669) baseStart_3794669 baseEnd_3794669 := by
    simpa [prefixWord, tailWord_3794669, baseEnd_3794669] using wordTrace_append hprefix tailTrace_3794669
  have hstable : (prefixWord ++ tailWord_3794669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794669).length < 2 ^ (prefixWord ++ tailWord_3794669).sum := by decide
  have hdescent : baseEnd_3794669 < baseStart_3794669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794675 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 8]
def baseStart_3794675 : Nat := 118140960795 + 3794675 * 2 ^ 59
def prefixEnd_3794675 : Nat := 4983230072969 + 3 ^ 40 * 3794675 * 2
def baseEnd_3794675 : Nat := 216499133622227338923457

theorem tailTrace_3794675 : CollatzResearch.WordTrace tailWord_3794675 prefixEnd_3794675 216499133622227338923457 := by
  unfold tailWord_3794675
  simp only [CollatzResearch.WordTrace]
  refine ⟨138403167527548028738913479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92268778351698685825942319 138403167527548028738913479)
  ·
    refine ⟨207604751291322043108370219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138403167527548028738913479 207604751291322043108370219)
    ·
      refine ⟨311407126936983064662555329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207604751291322043108370219 311407126936983064662555329)
      ·
        refine ⟨233555345202737298496916497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311407126936983064662555329 233555345202737298496916497)
        ·
          refine ⟨175166508902052973872687373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233555345202737298496916497 175166508902052973872687373)
          ·
            refine ⟨65687440838269865202257765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175166508902052973872687373 65687440838269865202257765)
            ·
              refine ⟨12316395157175599725423331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65687440838269865202257765 12316395157175599725423331)
              ·
                refine ⟨18474592735763399588134997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316395157175599725423331 18474592735763399588134997)
                ·
                  refine ⟨216499133622227338923457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18474592735763399588134997 216499133622227338923457)
                  ·
                    rfl

theorem cell23_3794675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 8].length) (baseStart_3794675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794675 prefixEnd_3794675 := by exact prefixLift 3794675
  have htrace : WordTrace (prefixWord ++ tailWord_3794675) baseStart_3794675 baseEnd_3794675 := by
    simpa [prefixWord, tailWord_3794675, baseEnd_3794675] using wordTrace_append hprefix tailTrace_3794675
  have hstable : (prefixWord ++ tailWord_3794675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794675).length < 2 ^ (prefixWord ++ tailWord_3794675).sum := by decide
  have hdescent : baseEnd_3794675 < baseStart_3794675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794676 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3794676 : Nat := 118140960795 + 3794676 * 2 ^ 59
def prefixEnd_3794676 : Nat := 4983230072969 + 3 ^ 40 * 3794676 * 2
def baseEnd_3794676 : Nat := 1948492716080700546398609

theorem tailTrace_3794676 : CollatzResearch.WordTrace tailWord_3794676 prefixEnd_3794676 1948492716080700546398609 := by
  unfold tailWord_3794676
  simp only [CollatzResearch.WordTrace]
  refine ⟨69201602000272202954849941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92268802667029603939799921 69201602000272202954849941)
  ·
    refine ⟨3243825093762759513508591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69201602000272202954849941 3243825093762759513508591)
    ·
      refine ⟨4865737640644139270262887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243825093762759513508591 4865737640644139270262887)
      ·
        refine ⟨7298606460966208905394331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865737640644139270262887 7298606460966208905394331)
        ·
          refine ⟨10947909691449313358091497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298606460966208905394331 10947909691449313358091497)
          ·
            refine ⟨8210932268586985018568623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10947909691449313358091497 8210932268586985018568623)
            ·
              refine ⟨12316398402880477527852935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210932268586985018568623 12316398402880477527852935)
              ·
                refine ⟨18474597604320716291779403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316398402880477527852935 18474597604320716291779403)
                ·
                  refine ⟨27711896406481074437669105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18474597604320716291779403 27711896406481074437669105)
                  ·
                    refine ⟨20783922304860805828251829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27711896406481074437669105 20783922304860805828251829)
                    ·
                      refine ⟨1948492716080700546398609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20783922304860805828251829 1948492716080700546398609)
                      ·
                        rfl

theorem cell23_3794676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3794676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794676 prefixEnd_3794676 := by exact prefixLift 3794676
  have htrace : WordTrace (prefixWord ++ tailWord_3794676) baseStart_3794676 baseEnd_3794676 := by
    simpa [prefixWord, tailWord_3794676, baseEnd_3794676] using wordTrace_append hprefix tailTrace_3794676
  have hstable : (prefixWord ++ tailWord_3794676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794676).length < 2 ^ (prefixWord ++ tailWord_3794676).sum := by decide
  have hdescent : baseEnd_3794676 < baseStart_3794676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794679 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 1, 4]
def baseStart_3794679 : Nat := 118140960795 + 3794679 * 2 ^ 59
def prefixEnd_3794679 : Nat := 4983230072969 + 3 ^ 40 * 3794679 * 2
def baseEnd_3794679 : Nat := 649498085507554678220365

theorem tailTrace_3794679 : CollatzResearch.WordTrace tailWord_3794679 prefixEnd_3794679 649498085507554678220365 := by
  unfold tailWord_3794679
  simp only [CollatzResearch.WordTrace]
  refine ⟨138403313419533537422059091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92268875613022358281372727 138403313419533537422059091)
  ·
    refine ⟨207604970129300306133088637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138403313419533537422059091 207604970129300306133088637)
    ·
      refine ⟨77851863798487614799908239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207604970129300306133088637 77851863798487614799908239)
      ·
        refine ⟨116777795697731422199862359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77851863798487614799908239 116777795697731422199862359)
        ·
          refine ⟨175166693546597133299793539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116777795697731422199862359 175166693546597133299793539)
          ·
            refine ⟨262750040319895699949690309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175166693546597133299793539 262750040319895699949690309)
            ·
              refine ⟨49265632559980443740566933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262750040319895699949690309 49265632559980443740566933)
              ·
                refine ⟨2309326526249083300339075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49265632559980443740566933 2309326526249083300339075)
                ·
                  refine ⟨3463989789373624950508613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309326526249083300339075 3463989789373624950508613)
                  ·
                    refine ⟨649498085507554678220365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3463989789373624950508613 649498085507554678220365)
                    ·
                      rfl

theorem cell23_3794679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_3794679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794679 prefixEnd_3794679 := by exact prefixLift 3794679
  have htrace : WordTrace (prefixWord ++ tailWord_3794679) baseStart_3794679 baseEnd_3794679 := by
    simpa [prefixWord, tailWord_3794679, baseEnd_3794679] using wordTrace_append hprefix tailTrace_3794679
  have hstable : (prefixWord ++ tailWord_3794679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794679).length < 2 ^ (prefixWord ++ tailWord_3794679).sum := by decide
  have hdescent : baseEnd_3794679 < baseStart_3794679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794702 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3794702 : Nat := 118140960795 + 3794702 * 2 ^ 59
def prefixEnd_3794702 : Nat := 4983230072969 + 3 ^ 40 * 3794702 * 2
def baseEnd_3794702 : Nat := 1948506066577717444673489

theorem tailTrace_3794702 : CollatzResearch.WordTrace tailWord_3794702 prefixEnd_3794702 1948506066577717444673489 := by
  unfold tailWord_3794702
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300519037306276543768295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92269434865633474900097573 17300519037306276543768295)
  ·
    refine ⟨25950778555959414815652443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17300519037306276543768295 25950778555959414815652443)
    ·
      refine ⟨38926167833939122223478665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25950778555959414815652443 38926167833939122223478665)
      ·
        refine ⟨29194625875454341667608999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38926167833939122223478665 29194625875454341667608999)
        ·
          refine ⟨43791938813181512501413499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29194625875454341667608999 43791938813181512501413499)
          ·
            refine ⟨65687908219772268752120249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43791938813181512501413499 65687908219772268752120249)
            ·
              refine ⟨49265931164829201564090187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65687908219772268752120249 49265931164829201564090187)
              ·
                refine ⟨73898896747243802346135281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49265931164829201564090187 73898896747243802346135281)
                ·
                  refine ⟨55424172560432851759601461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73898896747243802346135281 55424172560432851759601461)
                  ·
                    refine ⟨5196016177540579852462637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55424172560432851759601461 5196016177540579852462637)
                    ·
                      refine ⟨1948506066577717444673489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196016177540579852462637 1948506066577717444673489)
                      ·
                        rfl

theorem cell23_3794702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3794702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794702 prefixEnd_3794702 := by exact prefixLift 3794702
  have htrace : WordTrace (prefixWord ++ tailWord_3794702) baseStart_3794702 baseEnd_3794702 := by
    simpa [prefixWord, tailWord_3794702, baseEnd_3794702] using wordTrace_append hprefix tailTrace_3794702
  have hstable : (prefixWord ++ tailWord_3794702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794702).length < 2 ^ (prefixWord ++ tailWord_3794702).sum := by decide
  have hdescent : baseEnd_3794702 < baseStart_3794702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794706 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3794706 : Nat := 118140960795 + 3794706 * 2 ^ 59
def prefixEnd_3794706 : Nat := 4983230072969 + 3 ^ 40 * 3794706 * 2
def baseEnd_3794706 : Nat := 1948508120500335429023471

theorem tailTrace_3794706 : CollatzResearch.WordTrace tailWord_3794706 prefixEnd_3794706 1948508120500335429023471 := by
  unfold tailWord_3794706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34601074547608930258322993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92269532126957147355527981 34601074547608930258322993)
  ·
    refine ⟨25950805910706697693742245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34601074547608930258322993 25950805910706697693742245)
    ·
      refine ⟨4865776108257505817576671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25950805910706697693742245 4865776108257505817576671)
      ·
        refine ⟨7298664162386258726365007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865776108257505817576671 7298664162386258726365007)
        ·
          refine ⟨10947996243579388089547511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298664162386258726365007 10947996243579388089547511)
          ·
            refine ⟨16421994365369082134321267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10947996243579388089547511 16421994365369082134321267)
            ·
              refine ⟨24632991548053623201481901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16421994365369082134321267 24632991548053623201481901)
              ·
                refine ⟨9237371830520108700555713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24632991548053623201481901 9237371830520108700555713)
                ·
                  refine ⟨6928028872890081525416785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9237371830520108700555713 6928028872890081525416785)
                  ·
                    refine ⟨5196021654667561144062589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928028872890081525416785 5196021654667561144062589)
                    ·
                      refine ⟨1948508120500335429023471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196021654667561144062589 1948508120500335429023471)
                      ·
                        rfl

theorem cell23_3794706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3794706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794706 prefixEnd_3794706 := by exact prefixLift 3794706
  have htrace : WordTrace (prefixWord ++ tailWord_3794706) baseStart_3794706 baseEnd_3794706 := by
    simpa [prefixWord, tailWord_3794706, baseEnd_3794706] using wordTrace_append hprefix tailTrace_3794706
  have hstable : (prefixWord ++ tailWord_3794706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794706).length < 2 ^ (prefixWord ++ tailWord_3794706).sum := by decide
  have hdescent : baseEnd_3794706 < baseStart_3794706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794752 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 8, 4]
def baseStart_3794752 : Nat := 118140960795 + 3794752 * 2 ^ 59
def prefixEnd_3794752 : Nat := 4983230072969 + 3 ^ 40 * 3794752 * 2
def baseEnd_3794752 : Nat := 649510580203480749682753

theorem tailTrace_3794752 : CollatzResearch.WordTrace tailWord_3794752 prefixEnd_3794752 649510580203480749682753 := by
  unfold tailWord_3794752
  simp only [CollatzResearch.WordTrace]
  refine ⟨69202987974134535444733255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92270650632179380592977673 69202987974134535444733255)
  ·
    refine ⟨103804481961201803167099883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69202987974134535444733255 103804481961201803167099883)
    ·
      refine ⟨155706722941802704750649825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103804481961201803167099883 155706722941802704750649825)
      ·
        refine ⟨116780042206352028562987369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155706722941802704750649825 116780042206352028562987369)
        ·
          refine ⟨87585031654764021422240527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116780042206352028562987369 87585031654764021422240527)
          ·
            refine ⟨131377547482146032133360791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87585031654764021422240527 131377547482146032133360791)
            ·
              refine ⟨197066321223219048200041187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131377547482146032133360791 197066321223219048200041187)
              ·
                refine ⟨295599481834828572300061781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197066321223219048200041187 295599481834828572300061781)
                ·
                  refine ⟨3464056427751897331641349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 295599481834828572300061781 3464056427751897331641349)
                  ·
                    refine ⟨649510580203480749682753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464056427751897331641349 649510580203480749682753)
                    ·
                      rfl

theorem cell23_3794752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_3794752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794752 prefixEnd_3794752 := by exact prefixLift 3794752
  have htrace : WordTrace (prefixWord ++ tailWord_3794752) baseStart_3794752 baseEnd_3794752 := by
    simpa [prefixWord, tailWord_3794752, baseEnd_3794752] using wordTrace_append hprefix tailTrace_3794752
  have hstable : (prefixWord ++ tailWord_3794752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794752).length < 2 ^ (prefixWord ++ tailWord_3794752).sum := by decide
  have hdescent : baseEnd_3794752 < baseStart_3794752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794786 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3794786 : Nat := 118140960795 + 3794786 * 2 ^ 59
def prefixEnd_3794786 : Nat := 4983230072969 + 3 ^ 40 * 3794786 * 2
def baseEnd_3794786 : Nat := 649516399650898372007701

theorem tailTrace_3794786 : CollatzResearch.WordTrace tailWord_3794786 prefixEnd_3794786 649516399650898372007701 := by
  unfold tailWord_3794786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34601804007536473674051053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92271477353430596464136141 34601804007536473674051053)
  ·
    refine ⟨12975676502826177627769145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34601804007536473674051053 12975676502826177627769145)
    ·
      refine ⟨9731757377119633220826859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12975676502826177627769145 9731757377119633220826859)
      ·
        refine ⟨14597636065679449831240289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731757377119633220826859 14597636065679449831240289)
        ·
          refine ⟨10948227049259587373430217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14597636065679449831240289 10948227049259587373430217)
          ·
            refine ⟨8211170286944690530072663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10948227049259587373430217 8211170286944690530072663)
            ·
              refine ⟨12316755430417035795108995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211170286944690530072663 12316755430417035795108995)
              ·
                refine ⟨18475133145625553692663493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316755430417035795108995 18475133145625553692663493)
                ·
                  refine ⟨3464087464804791317374405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18475133145625553692663493 3464087464804791317374405)
                  ·
                    refine ⟨649516399650898372007701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464087464804791317374405 649516399650898372007701)
                    ·
                      rfl

theorem cell23_3794786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3794786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794786 prefixEnd_3794786 := by exact prefixLift 3794786
  have htrace : WordTrace (prefixWord ++ tailWord_3794786) baseStart_3794786 baseEnd_3794786 := by
    simpa [prefixWord, tailWord_3794786, baseEnd_3794786] using wordTrace_append hprefix tailTrace_3794786
  have hstable : (prefixWord ++ tailWord_3794786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794786).length < 2 ^ (prefixWord ++ tailWord_3794786).sum := by decide
  have hdescent : baseEnd_3794786 < baseStart_3794786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794806 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3794806 : Nat := 118140960795 + 3794806 * 2 ^ 59
def prefixEnd_3794806 : Nat := 4983230072969 + 3 ^ 40 * 3794806 * 2
def baseEnd_3794806 : Nat := 1948559468565785037773011

theorem tailTrace_3794806 : CollatzResearch.WordTrace tailWord_3794806 prefixEnd_3794806 1948559468565785037773011 := by
  unfold tailWord_3794806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650496593129589881995767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92271963660048958741288181 8650496593129589881995767)
  ·
    refine ⟨12975744889694384822993651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650496593129589881995767 12975744889694384822993651)
    ·
      refine ⟨19463617334541577234490477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12975744889694384822993651 19463617334541577234490477)
      ·
        refine ⟨7298856500453091462933929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19463617334541577234490477 7298856500453091462933929)
        ·
          refine ⟨5474142375339818597200447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7298856500453091462933929 5474142375339818597200447)
          ·
            refine ⟨8211213563009727895800671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474142375339818597200447 8211213563009727895800671)
            ·
              refine ⟨12316820344514591843701007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211213563009727895800671 12316820344514591843701007)
              ·
                refine ⟨18475230516771887765551511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316820344514591843701007 18475230516771887765551511)
                ·
                  refine ⟨27712845775157831648327267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18475230516771887765551511 27712845775157831648327267)
                  ·
                    refine ⟨41569268662736747472490901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27712845775157831648327267 41569268662736747472490901)
                    ·
                      refine ⟨1948559468565785037773011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41569268662736747472490901 1948559468565785037773011)
                      ·
                        rfl

theorem cell23_3794806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3794806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794806 prefixEnd_3794806 := by exact prefixLift 3794806
  have htrace : WordTrace (prefixWord ++ tailWord_3794806) baseStart_3794806 baseEnd_3794806 := by
    simpa [prefixWord, tailWord_3794806, baseEnd_3794806] using wordTrace_append hprefix tailTrace_3794806
  have hstable : (prefixWord ++ tailWord_3794806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794806).length < 2 ^ (prefixWord ++ tailWord_3794806).sum := by decide
  have hdescent : baseEnd_3794806 < baseStart_3794806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794869 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3794869 : Nat := 118140960795 + 3794869 * 2 ^ 59
def prefixEnd_3794869 : Nat := 4983230072969 + 3 ^ 40 * 3794869 * 2
def baseEnd_3794869 : Nat := 1948591817847018291285221

theorem tailTrace_3794869 : CollatzResearch.WordTrace tailWord_3794869 prefixEnd_3794869 1948591817847018291285221 := by
  unfold tailWord_3794869
  simp only [CollatzResearch.WordTrace]
  refine ⟨138410243288845199871475661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92273495525896799914317107 138410243288845199871475661)
  ·
    refine ⟨51903841233316949951803373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138410243288845199871475661 51903841233316949951803373)
    ·
      refine ⟨19463940462493856231926265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51903841233316949951803373 19463940462493856231926265)
      ·
        refine ⟨14597955346870392173944699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19463940462493856231926265 14597955346870392173944699)
        ·
          refine ⟨21896933020305588260917049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14597955346870392173944699 21896933020305588260917049)
          ·
            refine ⟨16422699765229191195687787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21896933020305588260917049 16422699765229191195687787)
            ·
              refine ⟨24634049647843786793531681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16422699765229191195687787 24634049647843786793531681)
              ·
                refine ⟨18475537235882840095148761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24634049647843786793531681 18475537235882840095148761)
                ·
                  refine ⟨13856652926912130071361571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18475537235882840095148761 13856652926912130071361571)
                  ·
                    refine ⟨20784979390368195107042357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13856652926912130071361571 20784979390368195107042357)
                    ·
                      refine ⟨1948591817847018291285221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20784979390368195107042357 1948591817847018291285221)
                      ·
                        rfl

theorem cell23_3794869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3794869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794869 prefixEnd_3794869 := by exact prefixLift 3794869
  have htrace : WordTrace (prefixWord ++ tailWord_3794869) baseStart_3794869 baseEnd_3794869 := by
    simpa [prefixWord, tailWord_3794869, baseEnd_3794869] using wordTrace_append hprefix tailTrace_3794869
  have hstable : (prefixWord ++ tailWord_3794869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794869).length < 2 ^ (prefixWord ++ tailWord_3794869).sum := by decide
  have hdescent : baseEnd_3794869 < baseStart_3794869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794872 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 9]
def baseStart_3794872 : Nat := 118140960795 + 3794872 * 2 ^ 59
def prefixEnd_3794872 : Nat := 4983230072969 + 3 ^ 40 * 3794872 * 2
def baseEnd_3794872 : Nat := 216510373143220197727523

theorem tailTrace_3794872 : CollatzResearch.WordTrace tailWord_3794872 prefixEnd_3794872 216510373143220197727523 := by
  unfold tailWord_3794872
  simp only [CollatzResearch.WordTrace]
  refine ⟨69205176353917165691917435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92273568471889554255889913 69205176353917165691917435)
  ·
    refine ⟨103807764530875748537876153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69205176353917165691917435 103807764530875748537876153)
    ·
      refine ⟨77855823398156811403407115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103807764530875748537876153 77855823398156811403407115)
      ·
        refine ⟨116783735097235217105110673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77855823398156811403407115 116783735097235217105110673)
        ·
          refine ⟨87587801322926412828833005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116783735097235217105110673 87587801322926412828833005)
          ·
            refine ⟨32845425496097404810812377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87587801322926412828833005 32845425496097404810812377)
            ·
              refine ⟨24634069122073053608109283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32845425496097404810812377 24634069122073053608109283)
              ·
                refine ⟨36951103683109580412163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24634069122073053608109283 36951103683109580412163925)
                ·
                  refine ⟨216510373143220197727523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36951103683109580412163925 216510373143220197727523)
                  ·
                    rfl

theorem cell23_3794872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_3794872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794872 prefixEnd_3794872 := by exact prefixLift 3794872
  have htrace : WordTrace (prefixWord ++ tailWord_3794872) baseStart_3794872 baseEnd_3794872 := by
    simpa [prefixWord, tailWord_3794872, baseEnd_3794872] using wordTrace_append hprefix tailTrace_3794872
  have hstable : (prefixWord ++ tailWord_3794872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794872).length < 2 ^ (prefixWord ++ tailWord_3794872).sum := by decide
  have hdescent : baseEnd_3794872 < baseStart_3794872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794900 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_3794900 : Nat := 118140960795 + 3794900 * 2 ^ 59
def prefixEnd_3794900 : Nat := 4983230072969 + 3 ^ 40 * 3794900 * 2
def baseEnd_3794900 : Nat := 1948607735747307669997579

theorem tailTrace_3794900 : CollatzResearch.WordTrace tailWord_3794900 prefixEnd_3794900 1948607735747307669997579 := by
  unfold tailWord_3794900
  simp only [CollatzResearch.WordTrace]
  refine ⟨69205686975866446082927077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92274249301155261443902769 69205686975866446082927077)
  ·
    refine ⟨12976066307974958640548827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69205686975866446082927077 12976066307974958640548827)
    ·
      refine ⟨19464099461962437960823241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12976066307974958640548827 19464099461962437960823241)
      ·
        refine ⟨14598074596471828470617431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19464099461962437960823241 14598074596471828470617431)
        ·
          refine ⟨21897111894707742705926147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14598074596471828470617431 21897111894707742705926147)
          ·
            refine ⟨32845667842061614058889221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21897111894707742705926147 32845667842061614058889221)
            ·
              refine ⟨6158562720386552636041729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32845667842061614058889221 6158562720386552636041729)
              ·
                refine ⟨4618922040289914477031297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6158562720386552636041729 4618922040289914477031297)
                ·
                  refine ⟨3464191530217435857773473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4618922040289914477031297 3464191530217435857773473)
                  ·
                    refine ⟨2598143647663076893330105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3464191530217435857773473 2598143647663076893330105)
                    ·
                      refine ⟨1948607735747307669997579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598143647663076893330105 1948607735747307669997579)
                      ·
                        rfl

theorem cell23_3794900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_3794900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794900 prefixEnd_3794900 := by exact prefixLift 3794900
  have htrace : WordTrace (prefixWord ++ tailWord_3794900) baseStart_3794900 baseEnd_3794900 := by
    simpa [prefixWord, tailWord_3794900, baseEnd_3794900] using wordTrace_append hprefix tailTrace_3794900
  have hstable : (prefixWord ++ tailWord_3794900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794900).length < 2 ^ (prefixWord ++ tailWord_3794900).sum := by decide
  have hdescent : baseEnd_3794900 < baseStart_3794900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794956 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 4, 4, 2]
def baseStart_3794956 : Nat := 118140960795 + 3794956 * 2 ^ 59
def prefixEnd_3794956 : Nat := 4983230072969 + 3 ^ 40 * 3794956 * 2
def baseEnd_3794956 : Nat := 1948636490663959450897321

theorem tailTrace_3794956 : CollatzResearch.WordTrace tailWord_3794956 prefixEnd_3794956 1948636490663959450897321 := by
  unfold tailWord_3794956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69206708219765006864946361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92275610959686675819928481 69206708219765006864946361)
  ·
    refine ⟨51905031164823755148709771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69206708219765006864946361 51905031164823755148709771)
    ·
      refine ⟨77857546747235632723064657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51905031164823755148709771 77857546747235632723064657)
      ·
        refine ⟨58393160060426724542298493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77857546747235632723064657 58393160060426724542298493)
        ·
          refine ⟨21897435022660021703361935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58393160060426724542298493 21897435022660021703361935)
          ·
            refine ⟨32846152533990032555042903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21897435022660021703361935 32846152533990032555042903)
            ·
              refine ⟨49269228800985048832564355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32846152533990032555042903 49269228800985048832564355)
              ·
                refine ⟨73903843201477573248846533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49269228800985048832564355 73903843201477573248846533)
                ·
                  refine ⟨13856970600277044984158725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73903843201477573248846533 13856970600277044984158725)
                  ·
                    refine ⟨2598181987551945934529761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13856970600277044984158725 2598181987551945934529761)
                    ·
                      refine ⟨1948636490663959450897321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598181987551945934529761 1948636490663959450897321)
                      ·
                        rfl

theorem cell23_3794956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_3794956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794956 prefixEnd_3794956 := by exact prefixLift 3794956
  have htrace : WordTrace (prefixWord ++ tailWord_3794956) baseStart_3794956 baseEnd_3794956 := by
    simpa [prefixWord, tailWord_3794956, baseEnd_3794956] using wordTrace_append hprefix tailTrace_3794956
  have hstable : (prefixWord ++ tailWord_3794956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794956).length < 2 ^ (prefixWord ++ tailWord_3794956).sum := by decide
  have hdescent : baseEnd_3794956 < baseStart_3794956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794973 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_3794973 : Nat := 118140960795 + 3794973 * 2 ^ 59
def prefixEnd_3794973 : Nat := 4983230072969 + 3 ^ 40 * 3794973 * 2
def baseEnd_3794973 : Nat := 1948645219835085884384743

theorem tailTrace_3794973 : CollatzResearch.WordTrace tailWord_3794973 prefixEnd_3794973 1948645219835085884384743 := by
  unfold tailWord_3794973
  simp only [CollatzResearch.WordTrace]
  refine ⟨138414036480468425633261573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92276024320312283755507715 138414036480468425633261573)
  ·
    refine ⟨25952631840087829806236545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138414036480468425633261573 25952631840087829806236545)
    ·
      refine ⟨19464473880065872354677409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25952631840087829806236545 19464473880065872354677409)
      ·
        refine ⟨14598355410049404266008057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19464473880065872354677409 14598355410049404266008057)
        ·
          refine ⟨10948766557537053199506043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14598355410049404266008057 10948766557537053199506043)
          ·
            refine ⟨16423149836305579799259065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10948766557537053199506043 16423149836305579799259065)
            ·
              refine ⟨12317362377229184849444299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16423149836305579799259065 12317362377229184849444299)
              ·
                refine ⟨18476043565843777274166449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317362377229184849444299 18476043565843777274166449)
                ·
                  refine ⟨13857032674382832955624837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18476043565843777274166449 13857032674382832955624837)
                  ·
                    refine ⟨2598193626446781179179657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13857032674382832955624837 2598193626446781179179657)
                    ·
                      refine ⟨1948645219835085884384743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598193626446781179179657 1948645219835085884384743)
                      ·
                        rfl

theorem cell23_3794973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_3794973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3794973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3794973 prefixEnd_3794973 := by exact prefixLift 3794973
  have htrace : WordTrace (prefixWord ++ tailWord_3794973) baseStart_3794973 baseEnd_3794973 := by
    simpa [prefixWord, tailWord_3794973, baseEnd_3794973] using wordTrace_append hprefix tailTrace_3794973
  have hstable : (prefixWord ++ tailWord_3794973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794973).length < 2 ^ (prefixWord ++ tailWord_3794973).sum := by decide
  have hdescent : baseEnd_3794973 < baseStart_3794973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795016 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_3795016 : Nat := 118140960795 + 3795016 * 2 ^ 59
def prefixEnd_3795016 : Nat := 4983230072969 + 3 ^ 40 * 3795016 * 2
def baseEnd_3795016 : Nat := 1948667299503229216147045

theorem tailTrace_3795016 : CollatzResearch.WordTrace tailWord_3795016 prefixEnd_3795016 1948667299503229216147045 := by
  unfold tailWord_3795016
  simp only [CollatzResearch.WordTrace]
  refine ⟨69207802409656321988538451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92277069879541762651384601 69207802409656321988538451)
  ·
    refine ⟨103811703614484482982807677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69207802409656321988538451 103811703614484482982807677)
    ·
      refine ⟨38929388855431681118552879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103811703614484482982807677 38929388855431681118552879)
      ·
        refine ⟨58394083283147521677829319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38929388855431681118552879 58394083283147521677829319)
        ·
          refine ⟨87591124924721282516743979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58394083283147521677829319 87591124924721282516743979)
          ·
            refine ⟨131386687387081923775115969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87591124924721282516743979 131386687387081923775115969)
            ·
              refine ⟨98540015540311442831336977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131386687387081923775115969 98540015540311442831336977)
              ·
                refine ⟨73905011655233582123502733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98540015540311442831336977 73905011655233582123502733)
                ·
                  refine ⟨27714379370712593296313525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73905011655233582123502733 27714379370712593296313525)
                  ·
                    refine ⟨2598223066004305621529393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27714379370712593296313525 2598223066004305621529393)
                    ·
                      refine ⟨1948667299503229216147045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598223066004305621529393 1948667299503229216147045)
                      ·
                        rfl

theorem cell23_3795016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_3795016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795016 prefixEnd_3795016 := by exact prefixLift 3795016
  have htrace : WordTrace (prefixWord ++ tailWord_3795016) baseStart_3795016 baseEnd_3795016 := by
    simpa [prefixWord, tailWord_3795016, baseEnd_3795016] using wordTrace_append hprefix tailTrace_3795016
  have hstable : (prefixWord ++ tailWord_3795016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795016).length < 2 ^ (prefixWord ++ tailWord_3795016).sum := by decide
  have hdescent : baseEnd_3795016 < baseStart_3795016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795030 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3795030 : Nat := 118140960795 + 3795030 * 2 ^ 59
def prefixEnd_3795030 : Nat := 4983230072969 + 3 ^ 40 * 3795030 * 2
def baseEnd_3795030 : Nat := 216519387581376906819109

theorem tailTrace_3795030 : CollatzResearch.WordTrace tailWord_3795030 prefixEnd_3795030 216519387581376906819109 := by
  unfold tailWord_3795030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651007215078870273005409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92277410294174616245391029 8651007215078870273005409)
  ·
    refine ⟨6488255411309152704754057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8651007215078870273005409 6488255411309152704754057)
    ·
      refine ⟨4866191558481864528565543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6488255411309152704754057 4866191558481864528565543)
      ·
        refine ⟨7299287337722796792848315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866191558481864528565543 7299287337722796792848315)
        ·
          refine ⟨10948931006584195189272473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299287337722796792848315 10948931006584195189272473)
          ·
            refine ⟨8211698254938146391954355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10948931006584195189272473 8211698254938146391954355)
            ·
              refine ⟨12317547382407219587931533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211698254938146391954355 12317547382407219587931533)
              ·
                refine ⟨4619080268402707345474325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12317547382407219587931533 4619080268402707345474325)
                ·
                  refine ⟨216519387581376906819109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4619080268402707345474325 216519387581376906819109)
                  ·
                    rfl

theorem cell23_3795030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3795030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795030 prefixEnd_3795030 := by exact prefixLift 3795030
  have htrace : WordTrace (prefixWord ++ tailWord_3795030) baseStart_3795030 baseEnd_3795030 := by
    simpa [prefixWord, tailWord_3795030, baseEnd_3795030] using wordTrace_append hprefix tailTrace_3795030
  have hstable : (prefixWord ++ tailWord_3795030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795030).length < 2 ^ (prefixWord ++ tailWord_3795030).sum := by decide
  have hdescent : baseEnd_3795030 < baseStart_3795030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795056 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_3795056 : Nat := 118140960795 + 3795056 * 2 ^ 59
def prefixEnd_3795056 : Nat := 4983230072969 + 3 ^ 40 * 3795056 * 2
def baseEnd_3795056 : Nat := 649562612909803019882287

theorem tailTrace_3795056 : CollatzResearch.WordTrace tailWord_3795056 prefixEnd_3795056 649562612909803019882287 := by
  unfold tailWord_3795056
  simp only [CollatzResearch.WordTrace]
  refine ⟨69208531869583865404266511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92278042492778487205688681 69208531869583865404266511)
  ·
    refine ⟨103812797804375798106399767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69208531869583865404266511 103812797804375798106399767)
    ·
      refine ⟨155719196706563697159599651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103812797804375798106399767 155719196706563697159599651)
      ·
        refine ⟨233578795059845545739399477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155719196706563697159599651 233578795059845545739399477)
        ·
          refine ⟨21898012036860519913068701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233578795059845545739399477 21898012036860519913068701)
          ·
            refine ⟨8211754513822694967400763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21898012036860519913068701 8211754513822694967400763)
            ·
              refine ⟨12317631770734042451101145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211754513822694967400763 12317631770734042451101145)
              ·
                refine ⟨9238223828050531838325859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12317631770734042451101145 9238223828050531838325859)
                ·
                  refine ⟨13857335742075797757488789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9238223828050531838325859 13857335742075797757488789)
                  ·
                    refine ⟨649562612909803019882287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13857335742075797757488789 649562612909803019882287)
                    ·
                      rfl

theorem cell23_3795056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_3795056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795056 prefixEnd_3795056 := by exact prefixLift 3795056
  have htrace : WordTrace (prefixWord ++ tailWord_3795056) baseStart_3795056 baseEnd_3795056 := by
    simpa [prefixWord, tailWord_3795056, baseEnd_3795056] using wordTrace_append hprefix tailTrace_3795056
  have hstable : (prefixWord ++ tailWord_3795056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795056).length < 2 ^ (prefixWord ++ tailWord_3795056).sum := by decide
  have hdescent : baseEnd_3795056 < baseStart_3795056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795069 : List Nat := [1, 4, 1, 1, 3, 13]
def baseStart_3795069 : Nat := 118140960795 + 3795069 * 2 ^ 59
def prefixEnd_3795069 : Nat := 4983230072969 + 3 ^ 40 * 3795069 * 2
def baseEnd_3795069 : Nat := 8019318987563446538207

theorem tailTrace_3795069 : CollatzResearch.WordTrace tailWord_3795069 prefixEnd_3795069 8019318987563446538207 := by
  unfold tailWord_3795069
  simp only [CollatzResearch.WordTrace]
  refine ⟨138417537888120634028756261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92278358592080422685837507 138417537888120634028756261)
  ·
    refine ⟨25953288354022618880391799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138417537888120634028756261 25953288354022618880391799)
    ·
      refine ⟨38929932531033928320587699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25953288354022618880391799 38929932531033928320587699)
      ·
        refine ⟨58394898796550892480881549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38929932531033928320587699 58394898796550892480881549)
        ·
          refine ⟨21898087048706584680330581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58394898796550892480881549 21898087048706584680330581)
          ·
            refine ⟨8019318987563446538207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 21898087048706584680330581 8019318987563446538207)
            ·
              rfl

theorem cell23_3795069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 13].length) (baseStart_3795069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795069 prefixEnd_3795069 := by exact prefixLift 3795069
  have htrace : WordTrace (prefixWord ++ tailWord_3795069) baseStart_3795069 baseEnd_3795069 := by
    simpa [prefixWord, tailWord_3795069, baseEnd_3795069] using wordTrace_append hprefix tailTrace_3795069
  have hstable : (prefixWord ++ tailWord_3795069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795069).length < 2 ^ (prefixWord ++ tailWord_3795069).sum := by decide
  have hdescent : baseEnd_3795069 < baseStart_3795069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795076 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3795076 : Nat := 118140960795 + 3795076 * 2 ^ 59
def prefixEnd_3795076 : Nat := 4983230072969 + 3 ^ 40 * 3795076 * 2
def baseEnd_3795076 : Nat := 1948698108342498981396769

theorem tailTrace_3795076 : CollatzResearch.WordTrace tailWord_3795076 prefixEnd_3795076 1948698108342498981396769 := by
  unfold tailWord_3795076
  simp only [CollatzResearch.WordTrace]
  refine ⟨69208896599547637112130541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92278528799396849482840721 69208896599547637112130541)
  ·
    refine ⟨25953336224830363917048953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69208896599547637112130541 25953336224830363917048953)
    ·
      refine ⟨19465002168622772937786715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25953336224830363917048953 19465002168622772937786715)
      ·
        refine ⟨29197503252934159406680073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465002168622772937786715 29197503252934159406680073)
        ·
          refine ⟨21898127439700619555010055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29197503252934159406680073 21898127439700619555010055)
          ·
            refine ⟨32847191159550929332515083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21898127439700619555010055 32847191159550929332515083)
            ·
              refine ⟨49270786739326393998772625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32847191159550929332515083 49270786739326393998772625)
              ·
                refine ⟨36953090054494795499079469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49270786739326393998772625 36953090054494795499079469)
                ·
                  refine ⟨13857408770435548312154801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36953090054494795499079469 13857408770435548312154801)
                  ·
                    refine ⟨10393056577826661234116101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13857408770435548312154801 10393056577826661234116101)
                    ·
                      refine ⟨1948698108342498981396769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10393056577826661234116101 1948698108342498981396769)
                      ·
                        rfl

theorem cell23_3795076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3795076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795076 prefixEnd_3795076 := by exact prefixLift 3795076
  have htrace : WordTrace (prefixWord ++ tailWord_3795076) baseStart_3795076 baseEnd_3795076 := by
    simpa [prefixWord, tailWord_3795076, baseEnd_3795076] using wordTrace_append hprefix tailTrace_3795076
  have hstable : (prefixWord ++ tailWord_3795076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795076).length < 2 ^ (prefixWord ++ tailWord_3795076).sum := by decide
  have hdescent : baseEnd_3795076 < baseStart_3795076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795099 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 2, 7]
def baseStart_3795099 : Nat := 118140960795 + 3795099 * 2 ^ 59
def prefixEnd_3795099 : Nat := 4983230072969 + 3 ^ 40 * 3795099 * 2
def baseEnd_3795099 : Nat := 649569972799184130469721

theorem tailTrace_3795099 : CollatzResearch.WordTrace tailWord_3795099 prefixEnd_3795099 649569972799184130469721 := by
  unfold tailWord_3795099
  simp only [CollatzResearch.WordTrace]
  refine ⟨138418632078011949152348351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92279088052007966101565567 138418632078011949152348351)
  ·
    refine ⟨207627948117017923728522527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138418632078011949152348351 207627948117017923728522527)
    ·
      refine ⟨311441922175526885592783791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207627948117017923728522527 311441922175526885592783791)
      ·
        refine ⟨467162883263290328389175687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311441922175526885592783791 467162883263290328389175687)
        ·
          refine ⟨700744324894935492583763531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467162883263290328389175687 700744324894935492583763531)
          ·
            refine ⟨1051116487342403238875645297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700744324894935492583763531 1051116487342403238875645297)
            ·
              refine ⟨788337365506802429156733973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051116487342403238875645297 788337365506802429156733973)
              ·
                refine ⟨36953314008131363866721905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 788337365506802429156733973 36953314008131363866721905)
                ·
                  refine ⟨27714985506098522900041429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36953314008131363866721905 27714985506098522900041429)
                  ·
                    refine ⟨649569972799184130469721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27714985506098522900041429 649569972799184130469721)
                    ·
                      rfl

theorem cell23_3795099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_3795099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795099 prefixEnd_3795099 := by exact prefixLift 3795099
  have htrace : WordTrace (prefixWord ++ tailWord_3795099) baseStart_3795099 baseEnd_3795099 := by
    simpa [prefixWord, tailWord_3795099, baseEnd_3795099] using wordTrace_append hprefix tailTrace_3795099
  have hstable : (prefixWord ++ tailWord_3795099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795099).length < 2 ^ (prefixWord ++ tailWord_3795099).sum := by decide
  have hdescent : baseEnd_3795099 < baseStart_3795099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795103 : List Nat := [1, 1, 2, 6, 1, 2, 3, 7]
def baseStart_3795103 : Nat := 118140960795 + 3795103 * 2 ^ 59
def prefixEnd_3795103 : Nat := 4983230072969 + 3 ^ 40 * 3795103 * 2
def baseEnd_3795103 : Nat := 72174517493339643546635

theorem tailTrace_3795103 : CollatzResearch.WordTrace tailWord_3795103 prefixEnd_3795103 72174517493339643546635 := by
  unfold tailWord_3795103
  simp only [CollatzResearch.WordTrace]
  refine ⟨138418777969997457835493963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92279185313331638556995975 138418777969997457835493963)
  ·
    refine ⟨207628166954996186753240945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138418777969997457835493963 207628166954996186753240945)
    ·
      refine ⟨155721125216247140064930709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207628166954996186753240945 155721125216247140064930709)
      ·
        refine ⟨7299427744511584690543627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155721125216247140064930709 7299427744511584690543627)
        ·
          refine ⟨10949141616767377035815441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299427744511584690543627 10949141616767377035815441)
          ·
            refine ⟨8211856212575532776861581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10949141616767377035815441 8211856212575532776861581)
            ·
              refine ⟨3079446079715824791323093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8211856212575532776861581 3079446079715824791323093)
              ·
                refine ⟨72174517493339643546635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3079446079715824791323093 72174517493339643546635)
                ·
                  rfl

theorem cell23_3795103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 7].length) (baseStart_3795103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795103 prefixEnd_3795103 := by exact prefixLift 3795103
  have htrace : WordTrace (prefixWord ++ tailWord_3795103) baseStart_3795103 baseEnd_3795103 := by
    simpa [prefixWord, tailWord_3795103, baseEnd_3795103] using wordTrace_append hprefix tailTrace_3795103
  have hstable : (prefixWord ++ tailWord_3795103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795103).length < 2 ^ (prefixWord ++ tailWord_3795103).sum := by decide
  have hdescent : baseEnd_3795103 < baseStart_3795103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795114 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3795114 : Nat := 118140960795 + 3795114 * 2 ^ 59
def prefixEnd_3795114 : Nat := 4983230072969 + 3 ^ 40 * 3795114 * 2
def baseEnd_3795114 : Nat := 1948717620607369832721595

theorem tailTrace_3795114 : CollatzResearch.WordTrace tailWord_3795114 prefixEnd_3795114 1948717620607369832721595 := by
  unfold tailWord_3795114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34604794793239401678536099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92279452781971737809429597 34604794793239401678536099)
  ·
    refine ⟨51907192189859102517804149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34604794793239401678536099 51907192189859102517804149)
    ·
      refine ⟨4866299267799290861044139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51907192189859102517804149 4866299267799290861044139)
      ·
        refine ⟨7299448901698936291566209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866299267799290861044139 7299448901698936291566209)
        ·
          refine ⟨5474586676274202218674657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299448901698936291566209 5474586676274202218674657)
          ·
            refine ⟨4105940007205651664005993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5474586676274202218674657 4105940007205651664005993)
            ·
              refine ⟨3079455005404238748004495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105940007205651664005993 3079455005404238748004495)
              ·
                refine ⟨4619182508106358122006743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079455005404238748004495 4619182508106358122006743)
                ·
                  refine ⟨6928773762159537183010115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619182508106358122006743 6928773762159537183010115)
                  ·
                    refine ⟨10393160643239305774515173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6928773762159537183010115 10393160643239305774515173)
                    ·
                      refine ⟨1948717620607369832721595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10393160643239305774515173 1948717620607369832721595)
                      ·
                        rfl

theorem cell23_3795114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3795114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795114 prefixEnd_3795114 := by exact prefixLift 3795114
  have htrace : WordTrace (prefixWord ++ tailWord_3795114) baseStart_3795114 baseEnd_3795114 := by
    simpa [prefixWord, tailWord_3795114, baseEnd_3795114] using wordTrace_append hprefix tailTrace_3795114
  have hstable : (prefixWord ++ tailWord_3795114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795114).length < 2 ^ (prefixWord ++ tailWord_3795114).sum := by decide
  have hdescent : baseEnd_3795114 < baseStart_3795114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795117 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_3795117 : Nat := 118140960795 + 3795117 * 2 ^ 59
def prefixEnd_3795117 : Nat := 4983230072969 + 3 ^ 40 * 3795117 * 2
def baseEnd_3795117 : Nat := 1948719161049333320984081

theorem tailTrace_3795117 : CollatzResearch.WordTrace tailWord_3795117 prefixEnd_3795117 1948719161049333320984081 := by
  unfold tailWord_3795117
  simp only [CollatzResearch.WordTrace]
  refine ⟨138419288591946738226503605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92279525727964492151002403 138419288591946738226503605)
  ·
    refine ⟨12976808305495006708734713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138419288591946738226503605 12976808305495006708734713)
    ·
      refine ⟨9732606229121255031551035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12976808305495006708734713 9732606229121255031551035)
      ·
        refine ⟨14598909343681882547326553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9732606229121255031551035 14598909343681882547326553)
        ·
          refine ⟨10949182007761411910494915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14598909343681882547326553 10949182007761411910494915)
          ·
            refine ⟨16423773011642117865742373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10949182007761411910494915 16423773011642117865742373)
            ·
              refine ⟨3079457439682897099826695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16423773011642117865742373 3079457439682897099826695)
              ·
                refine ⟨4619186159524345649740043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079457439682897099826695 4619186159524345649740043)
                ·
                  refine ⟨6928779239286518474610065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619186159524345649740043 6928779239286518474610065)
                  ·
                    refine ⟨5196584429464888855957549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928779239286518474610065 5196584429464888855957549)
                    ·
                      refine ⟨1948719161049333320984081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196584429464888855957549 1948719161049333320984081)
                      ·
                        rfl

theorem cell23_3795117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_3795117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795117 prefixEnd_3795117 := by exact prefixLift 3795117
  have htrace : WordTrace (prefixWord ++ tailWord_3795117) baseStart_3795117 baseEnd_3795117 := by
    simpa [prefixWord, tailWord_3795117, baseEnd_3795117] using wordTrace_append hprefix tailTrace_3795117
  have hstable : (prefixWord ++ tailWord_3795117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795117).length < 2 ^ (prefixWord ++ tailWord_3795117).sum := by decide
  have hdescent : baseEnd_3795117 < baseStart_3795117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795124 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3795124 : Nat := 118140960795 + 3795124 * 2 ^ 59
def prefixEnd_3795124 : Nat := 4983230072969 + 3 ^ 40 * 3795124 * 2
def baseEnd_3795124 : Nat := 649574251804638264532183

theorem tailTrace_3795124 : CollatzResearch.WordTrace tailWord_3795124 prefixEnd_3795124 649574251804638264532183 := by
  unfold tailWord_3795124
  simp only [CollatzResearch.WordTrace]
  refine ⟨69209771951460689211004213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92279695935280918948005617 69209771951460689211004213)
  ·
    refine ⟨6488416120449439613531645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69209771951460689211004213 6488416120449439613531645)
    ·
      refine ⟨2433156045168539855074367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6488416120449439613531645 2433156045168539855074367)
      ·
        refine ⟨3649734067752809782611551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433156045168539855074367 3649734067752809782611551)
        ·
          refine ⟨5474601101629214673917327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649734067752809782611551 5474601101629214673917327)
          ·
            refine ⟨8211901652443822010875991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474601101629214673917327 8211901652443822010875991)
            ·
              refine ⟨12317852478665733016313987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211901652443822010875991 12317852478665733016313987)
              ·
                refine ⟨18476778717998599524470981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317852478665733016313987 18476778717998599524470981)
                ·
                  refine ⟨3464396009624737410838309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18476778717998599524470981 3464396009624737410838309)
                  ·
                    refine ⟨649574251804638264532183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464396009624737410838309 649574251804638264532183)
                    ·
                      rfl

theorem cell23_3795124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3795124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795124 prefixEnd_3795124 := by exact prefixLift 3795124
  have htrace : WordTrace (prefixWord ++ tailWord_3795124) baseStart_3795124 baseEnd_3795124 := by
    simpa [prefixWord, tailWord_3795124, baseEnd_3795124] using wordTrace_append hprefix tailTrace_3795124
  have hstable : (prefixWord ++ tailWord_3795124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795124).length < 2 ^ (prefixWord ++ tailWord_3795124).sum := by decide
  have hdescent : baseEnd_3795124 < baseStart_3795124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795130 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_3795130 : Nat := 118140960795 + 3795130 * 2 ^ 59
def prefixEnd_3795130 : Nat := 4983230072969 + 3 ^ 40 * 3795130 * 2
def baseEnd_3795130 : Nat := 1948725836297841770121521

theorem tailTrace_3795130 : CollatzResearch.WordTrace tailWord_3795130 prefixEnd_3795130 1948725836297841770121521 := by
  unfold tailWord_3795130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34604940685224910361681711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92279841827266427631151229 34604940685224910361681711)
  ·
    refine ⟨51907411027837365542522567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34604940685224910361681711 51907411027837365542522567)
    ·
      refine ⟨77861116541756048313783851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51907411027837365542522567 77861116541756048313783851)
      ·
        refine ⟨116791674812634072470675777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77861116541756048313783851 116791674812634072470675777)
        ·
          refine ⟨87593756109475554353006833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116791674812634072470675777 87593756109475554353006833)
          ·
            refine ⟨65695317082106665764755125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87593756109475554353006833 65695317082106665764755125)
            ·
              refine ⟨6158935976447499915445793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65695317082106665764755125 6158935976447499915445793)
              ·
                refine ⟨4619201982335624936584345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6158935976447499915445793 4619201982335624936584345)
                ·
                  refine ⟨3464401486751718702438259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619201982335624936584345 3464401486751718702438259)
                  ·
                    refine ⟨5196602230127578053657389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464401486751718702438259 5196602230127578053657389)
                    ·
                      refine ⟨1948725836297841770121521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196602230127578053657389 1948725836297841770121521)
                      ·
                        rfl

theorem cell23_3795130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_3795130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795130 prefixEnd_3795130 := by exact prefixLift 3795130
  have htrace : WordTrace (prefixWord ++ tailWord_3795130) baseStart_3795130 baseEnd_3795130 := by
    simpa [prefixWord, tailWord_3795130, baseEnd_3795130] using wordTrace_append hprefix tailTrace_3795130
  have hstable : (prefixWord ++ tailWord_3795130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795130).length < 2 ^ (prefixWord ++ tailWord_3795130).sum := by decide
  have hdescent : baseEnd_3795130 < baseStart_3795130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795146 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_3795146 : Nat := 118140960795 + 3795146 * 2 ^ 59
def prefixEnd_3795146 : Nat := 4983230072969 + 3 ^ 40 * 3795146 * 2
def baseEnd_3795146 : Nat := 649578017329437902507149

theorem tailTrace_3795146 : CollatzResearch.WordTrace tailWord_3795146 prefixEnd_3795146 649578017329437902507149 := by
  unfold tailWord_3795146
  simp only [CollatzResearch.WordTrace]
  refine ⟨34605086577210419044827323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92280230872561117452872861 34605086577210419044827323)
  ·
    refine ⟨51907629865815628567240985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34605086577210419044827323 51907629865815628567240985)
    ·
      refine ⟨38930722399361721425430739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51907629865815628567240985 38930722399361721425430739)
      ·
        refine ⟨58396083599042582138146109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38930722399361721425430739 58396083599042582138146109)
        ·
          refine ⟨21898531349640968301804791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58396083599042582138146109 21898531349640968301804791)
          ·
            refine ⟨32847797024461452452707187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21898531349640968301804791 32847797024461452452707187)
            ·
              refine ⟨49271695536692178679060781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32847797024461452452707187 49271695536692178679060781)
              ·
                refine ⟨18476885826259567004647793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49271695536692178679060781 18476885826259567004647793)
                ·
                  refine ⟨13857664369694675253485845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18476885826259567004647793 13857664369694675253485845)
                  ·
                    refine ⟨649578017329437902507149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13857664369694675253485845 649578017329437902507149)
                    ·
                      rfl

theorem cell23_3795146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_3795146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795146 prefixEnd_3795146 := by exact prefixLift 3795146
  have htrace : WordTrace (prefixWord ++ tailWord_3795146) baseStart_3795146 baseEnd_3795146 := by
    simpa [prefixWord, tailWord_3795146, baseEnd_3795146] using wordTrace_append hprefix tailTrace_3795146
  have hstable : (prefixWord ++ tailWord_3795146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795146).length < 2 ^ (prefixWord ++ tailWord_3795146).sum := by decide
  have hdescent : baseEnd_3795146 < baseStart_3795146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795173 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3795173 : Nat := 118140960795 + 3795173 * 2 ^ 59
def prefixEnd_3795173 : Nat := 4983230072969 + 3 ^ 40 * 3795173 * 2
def baseEnd_3795173 : Nat := 1948747915965985101883823

theorem tailTrace_3795173 : CollatzResearch.WordTrace tailWord_3795173 prefixEnd_3795173 1948747915965985101883823 := by
  unfold tailWord_3795173
  simp only [CollatzResearch.WordTrace]
  refine ⟨138421331079743859790542173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92280887386495906527028115 138421331079743859790542173)
  ·
    refine ⟨51907999154903947421453315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138421331079743859790542173 51907999154903947421453315)
    ·
      refine ⟨77861998732355921132179973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51907999154903947421453315 77861998732355921132179973)
      ·
        refine ⟨14599124762316735212283745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77861998732355921132179973 14599124762316735212283745)
        ·
          refine ⟨10949343571737551409212809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14599124762316735212283745 10949343571737551409212809)
          ·
            refine ⟨8212007678803163556909607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10949343571737551409212809 8212007678803163556909607)
            ·
              refine ⟨12318011518204745335364411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212007678803163556909607 12318011518204745335364411)
              ·
                refine ⟨18477017277307118003046617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12318011518204745335364411 18477017277307118003046617)
                ·
                  refine ⟨13857762957980338502284963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18477017277307118003046617 13857762957980338502284963)
                  ·
                    refine ⟨20786644436970507753427445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13857762957980338502284963 20786644436970507753427445)
                    ·
                      refine ⟨1948747915965985101883823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20786644436970507753427445 1948747915965985101883823)
                      ·
                        rfl

theorem cell23_3795173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3795173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795173 prefixEnd_3795173 := by exact prefixLift 3795173
  have htrace : WordTrace (prefixWord ++ tailWord_3795173) baseStart_3795173 baseEnd_3795173 := by
    simpa [prefixWord, tailWord_3795173, baseEnd_3795173] using wordTrace_append hprefix tailTrace_3795173
  have hstable : (prefixWord ++ tailWord_3795173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795173).length < 2 ^ (prefixWord ++ tailWord_3795173).sum := by decide
  have hdescent : baseEnd_3795173 < baseStart_3795173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795204 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3795204 : Nat := 118140960795 + 3795204 * 2 ^ 59
def prefixEnd_3795204 : Nat := 4983230072969 + 3 ^ 40 * 3795204 * 2
def baseEnd_3795204 : Nat := 1948763833866274480596181

theorem tailTrace_3795204 : CollatzResearch.WordTrace tailWord_3795204 prefixEnd_3795204 1948763833866274480596181 := by
  unfold tailWord_3795204
  simp only [CollatzResearch.WordTrace]
  refine ⟨69211230871315776042460333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92281641161754368056613777 69211230871315776042460333)
  ·
    refine ⟨25954211576743416015922625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69211230871315776042460333 25954211576743416015922625)
    ·
      refine ⟨19465658682557562011941969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25954211576743416015922625 19465658682557562011941969)
      ·
        refine ⟨14599244011918171508956477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19465658682557562011941969 14599244011918171508956477)
        ·
          refine ⟨5474716504469314315858679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14599244011918171508956477 5474716504469314315858679)
          ·
            refine ⟨8212074756703971473788019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474716504469314315858679 8212074756703971473788019)
            ·
              refine ⟨12318112135055957210682029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212074756703971473788019 12318112135055957210682029)
              ·
                refine ⟨4619292050645983954005761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12318112135055957210682029 4619292050645983954005761)
                ·
                  refine ⟨3464469037984487965504321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619292050645983954005761 3464469037984487965504321)
                  ·
                    refine ⟨2598351778488365974128241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3464469037984487965504321 2598351778488365974128241)
                    ·
                      refine ⟨1948763833866274480596181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598351778488365974128241 1948763833866274480596181)
                      ·
                        rfl

theorem cell23_3795204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3795204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795204 prefixEnd_3795204 := by exact prefixLift 3795204
  have htrace : WordTrace (prefixWord ++ tailWord_3795204) baseStart_3795204 baseEnd_3795204 := by
    simpa [prefixWord, tailWord_3795204, baseEnd_3795204] using wordTrace_append hprefix tailTrace_3795204
  have hstable : (prefixWord ++ tailWord_3795204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795204).length < 2 ^ (prefixWord ++ tailWord_3795204).sum := by decide
  have hdescent : baseEnd_3795204 < baseStart_3795204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795223 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 2, 5]
def baseStart_3795223 : Nat := 118140960795 + 3795223 * 2 ^ 59
def prefixEnd_3795223 : Nat := 4983230072969 + 3 ^ 40 * 3795223 * 2
def baseEnd_3795223 : Nat := 649591196666236635419531

theorem tailTrace_3795223 : CollatzResearch.WordTrace tailWord_3795223 prefixEnd_3795223 649591196666236635419531 := by
  unfold tailWord_3795223
  simp only [CollatzResearch.WordTrace]
  refine ⟨138423154729562718329862323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92282103153041812219908215 138423154729562718329862323)
  ·
    refine ⟨207634732094344077494793485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138423154729562718329862323 207634732094344077494793485)
    ·
      refine ⟨77863024535379029060547557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207634732094344077494793485 77863024535379029060547557)
      ·
        refine ⟨14599317100383567948852667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77863024535379029060547557 14599317100383567948852667)
        ·
          refine ⟨21898975650575351923279001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14599317100383567948852667 21898975650575351923279001)
          ·
            refine ⟨16424231737931513942459251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21898975650575351923279001 16424231737931513942459251)
            ·
              refine ⟨24636347606897270913688877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424231737931513942459251 24636347606897270913688877)
              ·
                refine ⟨9238630352586476592633329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24636347606897270913688877 9238630352586476592633329)
                ·
                  refine ⟨6928972764439857444474997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9238630352586476592633329 6928972764439857444474997)
                  ·
                    refine ⟨649591196666236635419531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6928972764439857444474997 649591196666236635419531)
                    ·
                      rfl

theorem cell23_3795223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_3795223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795223 prefixEnd_3795223 := by exact prefixLift 3795223
  have htrace : WordTrace (prefixWord ++ tailWord_3795223) baseStart_3795223 baseEnd_3795223 := by
    simpa [prefixWord, tailWord_3795223, baseEnd_3795223] using wordTrace_append hprefix tailTrace_3795223
  have hstable : (prefixWord ++ tailWord_3795223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795223).length < 2 ^ (prefixWord ++ tailWord_3795223).sum := by decide
  have hdescent : baseEnd_3795223 < baseStart_3795223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795260 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_3795260 : Nat := 118140960795 + 3795260 * 2 ^ 59
def prefixEnd_3795260 : Nat := 4983230072969 + 3 ^ 40 * 3795260 * 2
def baseEnd_3795260 : Nat := 1948792588782926261495923

theorem tailTrace_3795260 : CollatzResearch.WordTrace tailWord_3795260 prefixEnd_3795260 1948792588782926261495923 := by
  unfold tailWord_3795260
  simp only [CollatzResearch.WordTrace]
  refine ⟨69212252115214336824479617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92283002820285782432639489 69212252115214336824479617)
  ·
    refine ⟨51909189086410752618359713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69212252115214336824479617 51909189086410752618359713)
    ·
      refine ⟨38931891814808064463769785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51909189086410752618359713 38931891814808064463769785)
      ·
        refine ⟨29198918861106048347827339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38931891814808064463769785 29198918861106048347827339)
        ·
          refine ⟨43798378291659072521741009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29198918861106048347827339 43798378291659072521741009)
          ·
            refine ⟨32848783718744304391305757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43798378291659072521741009 32848783718744304391305757)
            ·
              refine ⟨12318293894529114146739659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32848783718744304391305757 12318293894529114146739659)
              ·
                refine ⟨18477440841793671220109489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12318293894529114146739659 18477440841793671220109489)
                ·
                  refine ⟨13858080631345253415082117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18477440841793671220109489 13858080631345253415082117)
                  ·
                    refine ⟨2598390118377235015327897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13858080631345253415082117 2598390118377235015327897)
                    ·
                      refine ⟨1948792588782926261495923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598390118377235015327897 1948792588782926261495923)
                      ·
                        rfl

theorem cell23_3795260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_3795260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795260 prefixEnd_3795260 := by exact prefixLift 3795260
  have htrace : WordTrace (prefixWord ++ tailWord_3795260) baseStart_3795260 baseEnd_3795260 := by
    simpa [prefixWord, tailWord_3795260, baseEnd_3795260] using wordTrace_append hprefix tailTrace_3795260
  have hstable : (prefixWord ++ tailWord_3795260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795260).length < 2 ^ (prefixWord ++ tailWord_3795260).sum := by decide
  have hdescent : baseEnd_3795260 < baseStart_3795260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795263 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_3795263 : Nat := 118140960795 + 3795263 * 2 ^ 59
def prefixEnd_3795263 : Nat := 4983230072969 + 3 ^ 40 * 3795263 * 2
def baseEnd_3795263 : Nat := 1948794129224889749758409

theorem tailTrace_3795263 : CollatzResearch.WordTrace tailWord_3795263 prefixEnd_3795263 1948794129224889749758409 := by
  unfold tailWord_3795263
  simp only [CollatzResearch.WordTrace]
  refine ⟨138424613649417805161318443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92283075766278536774212295 138424613649417805161318443)
  ·
    refine ⟨207636920474126707741977665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138424613649417805161318443 207636920474126707741977665)
    ·
      refine ⟨155727690355595030806483249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207636920474126707741977665 155727690355595030806483249)
      ·
        refine ⟨116795767766696273104862437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155727690355595030806483249 116795767766696273104862437)
        ·
          refine ⟨21899206456255551207161707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116795767766696273104862437 21899206456255551207161707)
          ·
            refine ⟨32848809684383326810742561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21899206456255551207161707 32848809684383326810742561)
            ·
              refine ⟨24636607263287495108056921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32848809684383326810742561 24636607263287495108056921)
              ·
                refine ⟨18477455447465621331042691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24636607263287495108056921 18477455447465621331042691)
                ·
                  refine ⟨27716183171198431996564037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18477455447465621331042691 27716183171198431996564037)
                  ·
                    refine ⟨5196784344599705999355757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27716183171198431996564037 5196784344599705999355757)
                    ·
                      refine ⟨1948794129224889749758409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196784344599705999355757 1948794129224889749758409)
                      ·
                        rfl

theorem cell23_3795263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_3795263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795263 prefixEnd_3795263 := by exact prefixLift 3795263
  have htrace : WordTrace (prefixWord ++ tailWord_3795263) baseStart_3795263 baseEnd_3795263 := by
    simpa [prefixWord, tailWord_3795263, baseEnd_3795263] using wordTrace_append hprefix tailTrace_3795263
  have hstable : (prefixWord ++ tailWord_3795263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795263).length < 2 ^ (prefixWord ++ tailWord_3795263).sum := by decide
  have hdescent : baseEnd_3795263 < baseStart_3795263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795280 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_3795280 : Nat := 118140960795 + 3795280 * 2 ^ 59
def prefixEnd_3795280 : Nat := 4983230072969 + 3 ^ 40 * 3795280 * 2
def baseEnd_3795280 : Nat := 1948802858396016183245831

theorem tailTrace_3795280 : CollatzResearch.WordTrace tailWord_3795280 prefixEnd_3795280 1948802858396016183245831 := by
  unfold tailWord_3795280
  simp only [CollatzResearch.WordTrace]
  refine ⟨69212616845178108532343647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92283489126904144709791529 69212616845178108532343647)
  ·
    refine ⟨103818925267767162798515471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69212616845178108532343647 103818925267767162798515471)
    ·
      refine ⟨155728387901650744197773207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103818925267767162798515471 155728387901650744197773207)
      ·
        refine ⟨233592581852476116296659811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155728387901650744197773207 233592581852476116296659811)
        ·
          refine ⟨350388872778714174444989717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233592581852476116296659811 350388872778714174444989717)
          ·
            refine ⟨16424478411502226927108893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350388872778714174444989717 16424478411502226927108893)
            ·
              refine ⟨6159179404313335097665835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16424478411502226927108893 6159179404313335097665835)
              ·
                refine ⟨9238769106470002646498753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6159179404313335097665835 9238769106470002646498753)
                ·
                  refine ⟨6929076829852501984874065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9238769106470002646498753 6929076829852501984874065)
                  ·
                    refine ⟨5196807622389376488655549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6929076829852501984874065 5196807622389376488655549)
                    ·
                      refine ⟨1948802858396016183245831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196807622389376488655549 1948802858396016183245831)
                      ·
                        rfl

theorem cell23_3795280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_3795280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795280 prefixEnd_3795280 := by exact prefixLift 3795280
  have htrace : WordTrace (prefixWord ++ tailWord_3795280) baseStart_3795280 baseEnd_3795280 := by
    simpa [prefixWord, tailWord_3795280, baseEnd_3795280] using wordTrace_append hprefix tailTrace_3795280
  have hstable : (prefixWord ++ tailWord_3795280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795280).length < 2 ^ (prefixWord ++ tailWord_3795280).sum := by decide
  have hdescent : baseEnd_3795280 < baseStart_3795280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795287 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 1, 4]
def baseStart_3795287 : Nat := 118140960795 + 3795287 * 2 ^ 59
def prefixEnd_3795287 : Nat := 4983230072969 + 3 ^ 40 * 3795287 * 2
def baseEnd_3795287 : Nat := 649602150920199218619433

theorem tailTrace_3795287 : CollatzResearch.WordTrace tailWord_3795287 prefixEnd_3795287 649602150920199218619433 := by
  unfold tailWord_3795287
  simp only [CollatzResearch.WordTrace]
  refine ⟨138425489001330857260192115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92283659334220571506794743 138425489001330857260192115)
  ·
    refine ⟨207638233501996285890288173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138425489001330857260192115 207638233501996285890288173)
    ·
      refine ⟨77864337563248607208858065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207638233501996285890288173 77864337563248607208858065)
      ·
        refine ⟨58398253172436455406643549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77864337563248607208858065 58398253172436455406643549)
        ·
          refine ⟨21899344939663670777491331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58398253172436455406643549 21899344939663670777491331)
          ·
            refine ⟨32849017409495506166236997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21899344939663670777491331 32849017409495506166236997)
            ·
              refine ⟨6159190764280407406169437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32849017409495506166236997 6159190764280407406169437)
              ·
                refine ⟨2309696536605152777313539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6159190764280407406169437 2309696536605152777313539)
                ·
                  refine ⟨3464544804907729165970309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309696536605152777313539 3464544804907729165970309)
                  ·
                    refine ⟨649602150920199218619433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464544804907729165970309 649602150920199218619433)
                    ·
                      rfl

theorem cell23_3795287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_3795287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795287 prefixEnd_3795287 := by exact prefixLift 3795287
  have htrace : WordTrace (prefixWord ++ tailWord_3795287) baseStart_3795287 baseEnd_3795287 := by
    simpa [prefixWord, tailWord_3795287, baseEnd_3795287] using wordTrace_append hprefix tailTrace_3795287
  have hstable : (prefixWord ++ tailWord_3795287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795287).length < 2 ^ (prefixWord ++ tailWord_3795287).sum := by decide
  have hdescent : baseEnd_3795287 < baseStart_3795287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795303 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3795303 : Nat := 118140960795 + 3795303 * 2 ^ 59
def prefixEnd_3795303 : Nat := 4983230072969 + 3 ^ 40 * 3795303 * 2
def baseEnd_3795303 : Nat := 1948814668451069593258225

theorem tailTrace_3795303 : CollatzResearch.WordTrace tailWord_3795303 prefixEnd_3795303 1948814668451069593258225 := by
  unfold tailWord_3795303
  simp only [CollatzResearch.WordTrace]
  refine ⟨138426072569272891992774563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92284048379515261328516375 138426072569272891992774563)
  ·
    refine ⟨207639108853909337989161845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138426072569272891992774563 207639108853909337989161845)
    ·
      refine ⟨19466166455054000436483923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207639108853909337989161845 19466166455054000436483923)
      ·
        refine ⟨29199249682581000654725885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19466166455054000436483923 29199249682581000654725885)
        ·
          refine ⟨10949718630967875245522207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29199249682581000654725885 10949718630967875245522207)
          ·
            refine ⟨16424577946451812868283311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10949718630967875245522207 16424577946451812868283311)
            ·
              refine ⟨24636866919677719302424967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424577946451812868283311 24636866919677719302424967)
              ·
                refine ⟨36955300379516578953637451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24636866919677719302424967 36955300379516578953637451)
                ·
                  refine ⟨55432950569274868430456177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36955300379516578953637451 55432950569274868430456177)
                  ·
                    refine ⟨41574712926956151322842133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55432950569274868430456177 41574712926956151322842133)
                    ·
                      refine ⟨1948814668451069593258225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41574712926956151322842133 1948814668451069593258225)
                      ·
                        rfl

theorem cell23_3795303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3795303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795303 prefixEnd_3795303 := by exact prefixLift 3795303
  have htrace : WordTrace (prefixWord ++ tailWord_3795303) baseStart_3795303 baseEnd_3795303 := by
    simpa [prefixWord, tailWord_3795303, baseEnd_3795303] using wordTrace_append hprefix tailTrace_3795303
  have hstable : (prefixWord ++ tailWord_3795303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795303).length < 2 ^ (prefixWord ++ tailWord_3795303).sum := by decide
  have hdescent : baseEnd_3795303 < baseStart_3795303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795317 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 6]
def baseStart_3795317 : Nat := 118140960795 + 3795317 * 2 ^ 59
def prefixEnd_3795317 : Nat := 4983230072969 + 3 ^ 40 * 3795317 * 2
def baseEnd_3795317 : Nat := 216535761908914726498129

theorem tailTrace_3795317 : CollatzResearch.WordTrace tailWord_3795317 prefixEnd_3795317 216535761908914726498129 := by
  unfold tailWord_3795317
  simp only [CollatzResearch.WordTrace]
  refine ⟨138426583191222172383784205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92284388794148114922522803 138426583191222172383784205)
  ·
    refine ⟨51909968696708314643919077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138426583191222172383784205 51909968696708314643919077)
    ·
      refine ⟨9733119130632808995734827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51909968696708314643919077 9733119130632808995734827)
      ·
        refine ⟨14599678695949213493602241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9733119130632808995734827 14599678695949213493602241)
        ·
          refine ⟨10949759021961910120201681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14599678695949213493602241 10949759021961910120201681)
          ·
            refine ⟨8212319266471432590151261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10949759021961910120201681 8212319266471432590151261)
            ·
              refine ⟨3079619724926787221306723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8212319266471432590151261 3079619724926787221306723)
              ·
                refine ⟨4619429587390180831960085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079619724926787221306723 4619429587390180831960085)
                ·
                  refine ⟨216535761908914726498129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4619429587390180831960085 216535761908914726498129)
                  ·
                    rfl

theorem cell23_3795317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_3795317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795317 prefixEnd_3795317 := by exact prefixLift 3795317
  have htrace : WordTrace (prefixWord ++ tailWord_3795317) baseStart_3795317 baseEnd_3795317 := by
    simpa [prefixWord, tailWord_3795317, baseEnd_3795317] using wordTrace_append hprefix tailTrace_3795317
  have hstable : (prefixWord ++ tailWord_3795317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795317).length < 2 ^ (prefixWord ++ tailWord_3795317).sum := by decide
  have hdescent : baseEnd_3795317 < baseStart_3795317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795338 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_3795338 : Nat := 118140960795 + 3795338 * 2 ^ 59
def prefixEnd_3795338 : Nat := 4983230072969 + 3 ^ 40 * 3795338 * 2
def baseEnd_3795338 : Nat := 649610880091325652106855

theorem tailTrace_3795338 : CollatzResearch.WordTrace tailWord_3795338 prefixEnd_3795338 649610880091325652106855 := by
  unfold tailWord_3795338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34606837281036523242574667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92284899416097395313532445 34606837281036523242574667)
  ·
    refine ⟨51910255921554784863862001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34606837281036523242574667 51910255921554784863862001)
    ·
      refine ⟨38932691941166088647896501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51910255921554784863862001 38932691941166088647896501)
      ·
        refine ⟨3649939869484320810740297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38932691941166088647896501 3649939869484320810740297)
        ·
          refine ⟨2737454902113240608055223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3649939869484320810740297 2737454902113240608055223)
          ·
            refine ⟨4106182353169860912082835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737454902113240608055223 4106182353169860912082835)
            ·
              refine ⟨6159273529754791368124253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106182353169860912082835 6159273529754791368124253)
              ·
                refine ⟨2309727573658046763046595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6159273529754791368124253 2309727573658046763046595)
                ·
                  refine ⟨3464591360487070144569893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309727573658046763046595 3464591360487070144569893)
                  ·
                    refine ⟨649610880091325652106855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464591360487070144569893 649610880091325652106855)
                    ·
                      rfl

theorem cell23_3795338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_3795338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795338 prefixEnd_3795338 := by exact prefixLift 3795338
  have htrace : WordTrace (prefixWord ++ tailWord_3795338) baseStart_3795338 baseEnd_3795338 := by
    simpa [prefixWord, tailWord_3795338, baseEnd_3795338] using wordTrace_append hprefix tailTrace_3795338
  have hstable : (prefixWord ++ tailWord_3795338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795338).length < 2 ^ (prefixWord ++ tailWord_3795338).sum := by decide
  have hdescent : baseEnd_3795338 < baseStart_3795338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795360 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 4, 4]
def baseStart_3795360 : Nat := 118140960795 + 3795360 * 2 ^ 59
def prefixEnd_3795360 : Nat := 4983230072969 + 3 ^ 40 * 3795360 * 2
def baseEnd_3795360 : Nat := 649614645616125290081821

theorem tailTrace_3795360 : CollatzResearch.WordTrace tailWord_3795360 prefixEnd_3795360 649614645616125290081821 := by
  unfold tailWord_3795360
  simp only [CollatzResearch.WordTrace]
  refine ⟨69214075765033195363799767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92285434353377593818399689 69214075765033195363799767)
  ·
    refine ⟨103821113647549793045699651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69214075765033195363799767 103821113647549793045699651)
    ·
      refine ⟨155731670471324689568549477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103821113647549793045699651 155731670471324689568549477)
      ·
        refine ⟨29199688213373379294103027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155731670471324689568549477 29199688213373379294103027)
        ·
          refine ⟨43799532320060068941154541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29199688213373379294103027 43799532320060068941154541)
          ·
            refine ⟨16424824620022525852932953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43799532320060068941154541 16424824620022525852932953)
            ·
              refine ⟨12318618465016894389699715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16424824620022525852932953 12318618465016894389699715)
              ·
                refine ⟨18477927697525341584549573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12318618465016894389699715 18477927697525341584549573)
                ·
                  refine ⟨3464611443286001547103045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18477927697525341584549573 3464611443286001547103045)
                  ·
                    refine ⟨649614645616125290081821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464611443286001547103045 649614645616125290081821)
                    ·
                      rfl

theorem cell23_3795360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_3795360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795360 prefixEnd_3795360 := by exact prefixLift 3795360
  have htrace : WordTrace (prefixWord ++ tailWord_3795360) baseStart_3795360 baseEnd_3795360 := by
    simpa [prefixWord, tailWord_3795360, baseEnd_3795360] using wordTrace_append hprefix tailTrace_3795360
  have hstable : (prefixWord ++ tailWord_3795360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795360).length < 2 ^ (prefixWord ++ tailWord_3795360).sum := by decide
  have hdescent : baseEnd_3795360 < baseStart_3795360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795361 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3795361 : Nat := 118140960795 + 3795361 * 2 ^ 59
def prefixEnd_3795361 : Nat := 4983230072969 + 3 ^ 40 * 3795361 * 2
def baseEnd_3795361 : Nat := 1948844450329030366332959

theorem tailTrace_3795361 : CollatzResearch.WordTrace tailWord_3795361 prefixEnd_3795361 1948844450329030366332959 := by
  unfold tailWord_3795361
  simp only [CollatzResearch.WordTrace]
  refine ⟨138428188003062767898385937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92285458668708511932257291 138428188003062767898385937)
  ·
    refine ⟨103821141002297075923789453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138428188003062767898385937 103821141002297075923789453)
    ·
      refine ⟨38932927875861403471421045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103821141002297075923789453 38932927875861403471421045)
      ·
        refine ⟨3649961988362006575445723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38932927875861403471421045 3649961988362006575445723)
        ·
          refine ⟨5474942982543009863168585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649961988362006575445723 5474942982543009863168585)
          ·
            refine ⟨4106207236907257397376439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5474942982543009863168585 4106207236907257397376439)
            ·
              refine ⟨6159310855360886096064659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106207236907257397376439 6159310855360886096064659)
              ·
                refine ⟨9238966283041329144096989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6159310855360886096064659 9238966283041329144096989)
                ·
                  refine ⟨3464612356140498429036371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9238966283041329144096989 3464612356140498429036371)
                  ·
                    refine ⟨5196918534210747643554557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464612356140498429036371 5196918534210747643554557)
                    ·
                      refine ⟨1948844450329030366332959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196918534210747643554557 1948844450329030366332959)
                      ·
                        rfl

theorem cell23_3795361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3795361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795361 prefixEnd_3795361 := by exact prefixLift 3795361
  have htrace : WordTrace (prefixWord ++ tailWord_3795361) baseStart_3795361 baseEnd_3795361 := by
    simpa [prefixWord, tailWord_3795361, baseEnd_3795361] using wordTrace_append hprefix tailTrace_3795361
  have hstable : (prefixWord ++ tailWord_3795361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795361).length < 2 ^ (prefixWord ++ tailWord_3795361).sum := by decide
  have hdescent : baseEnd_3795361 < baseStart_3795361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795363 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3795363 : Nat := 118140960795 + 3795363 * 2 ^ 59
def prefixEnd_3795363 : Nat := 4983230072969 + 3 ^ 40 * 3795363 * 2
def baseEnd_3795363 : Nat := 1948845477290339358507949

theorem tailTrace_3795363 : CollatzResearch.WordTrace tailWord_3795363 prefixEnd_3795363 1948845477290339358507949 := by
  unfold tailWord_3795363
  simp only [CollatzResearch.WordTrace]
  refine ⟨138428260949055522239958743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92285507299370348159972495 138428260949055522239958743)
  ·
    refine ⟨207642391423583283359938115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138428260949055522239958743 207642391423583283359938115)
    ·
      refine ⟨311463587135374925039907173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207642391423583283359938115 311463587135374925039907173)
      ·
        refine ⟨58399422587882798444982595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311463587135374925039907173 58399422587882798444982595)
        ·
          refine ⟨87599133881824197667473893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58399422587882798444982595 87599133881824197667473893)
          ·
            refine ⟨16424837602842037062651355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87599133881824197667473893 16424837602842037062651355)
            ·
              refine ⟨24637256404263055593977033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424837602842037062651355 24637256404263055593977033)
              ·
                refine ⟨18477942303197291695482775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24637256404263055593977033 18477942303197291695482775)
                ·
                  refine ⟨27716913454795937543224163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18477942303197291695482775 27716913454795937543224163)
                  ·
                    refine ⟨41575370182193906314836245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27716913454795937543224163 41575370182193906314836245)
                    ·
                      refine ⟨1948845477290339358507949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41575370182193906314836245 1948845477290339358507949)
                      ·
                        rfl

theorem cell23_3795363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3795363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795363 prefixEnd_3795363 := by exact prefixLift 3795363
  have htrace : WordTrace (prefixWord ++ tailWord_3795363) baseStart_3795363 baseEnd_3795363 := by
    simpa [prefixWord, tailWord_3795363, baseEnd_3795363] using wordTrace_append hprefix tailTrace_3795363
  have hstable : (prefixWord ++ tailWord_3795363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795363).length < 2 ^ (prefixWord ++ tailWord_3795363).sum := by decide
  have hdescent : baseEnd_3795363 < baseStart_3795363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795377 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 2, 4]
def baseStart_3795377 : Nat := 118140960795 + 3795377 * 2 ^ 59
def prefixEnd_3795377 : Nat := 4983230072969 + 3 ^ 40 * 3795377 * 2
def baseEnd_3795377 : Nat := 649617555339834101244295

theorem tailTrace_3795377 : CollatzResearch.WordTrace tailWord_3795377 prefixEnd_3795377 649617555339834101244295 := by
  unfold tailWord_3795377
  simp only [CollatzResearch.WordTrace]
  refine ⟨138428771571004802630968385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92285847714003201753978923 138428771571004802630968385)
  ·
    refine ⟨103821578678253601973226289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138428771571004802630968385 103821578678253601973226289)
    ·
      refine ⟨77866184008690201479919717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103821578678253601973226289 77866184008690201479919717)
      ·
        refine ⟨14599909501629412777484947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77866184008690201479919717 14599909501629412777484947)
        ·
          refine ⟨21899864252444119166227421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14599909501629412777484947 21899864252444119166227421)
          ·
            refine ⟨8212449094666544687335283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21899864252444119166227421 8212449094666544687335283)
            ·
              refine ⟨12318673641999817031002925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212449094666544687335283 12318673641999817031002925)
              ·
                refine ⟨4619502615749931386626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12318673641999817031002925 4619502615749931386626097)
                ·
                  refine ⟨3464626961812448539969573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619502615749931386626097 3464626961812448539969573)
                  ·
                    refine ⟨649617555339834101244295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464626961812448539969573 649617555339834101244295)
                    ·
                      rfl

theorem cell23_3795377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_3795377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795377 prefixEnd_3795377 := by exact prefixLift 3795377
  have htrace : WordTrace (prefixWord ++ tailWord_3795377) baseStart_3795377 baseEnd_3795377 := by
    simpa [prefixWord, tailWord_3795377, baseEnd_3795377] using wordTrace_append hprefix tailTrace_3795377
  have hstable : (prefixWord ++ tailWord_3795377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795377).length < 2 ^ (prefixWord ++ tailWord_3795377).sum := by decide
  have hdescent : baseEnd_3795377 < baseStart_3795377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795400 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_3795400 : Nat := 118140960795 + 3795400 * 2 ^ 59
def prefixEnd_3795400 : Nat := 4983230072969 + 3 ^ 40 * 3795400 * 2
def baseEnd_3795400 : Nat := 1948864476074555713745279

theorem tailTrace_3795400 : CollatzResearch.WordTrace tailWord_3795400 prefixEnd_3795400 1948864476074555713745279 := by
  unfold tailWord_3795400
  simp only [CollatzResearch.WordTrace]
  refine ⟨69214805224960738779527827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92286406966614318372703769 69214805224960738779527827)
  ·
    refine ⟨103822207837441108169291741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69214805224960738779527827 103822207837441108169291741)
    ·
      refine ⟨38933327939040415563484403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103822207837441108169291741 38933327939040415563484403)
      ·
        refine ⟨58399991908560623345226605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38933327939040415563484403 58399991908560623345226605)
        ·
          refine ⟨21899996965710233754459977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58399991908560623345226605 21899996965710233754459977)
          ·
            refine ⟨16424997724282675315844983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21899996965710233754459977 16424997724282675315844983)
            ·
              refine ⟨24637496586424012973767475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424997724282675315844983 24637496586424012973767475)
              ·
                refine ⟨36956244879636019460651213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24637496586424012973767475 36956244879636019460651213)
                ·
                  refine ⟨13858591829863507297744205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36956244879636019460651213 13858591829863507297744205)
                  ·
                    refine ⟨5196971936198815236654077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13858591829863507297744205 5196971936198815236654077)
                    ·
                      refine ⟨1948864476074555713745279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5196971936198815236654077 1948864476074555713745279)
                      ·
                        rfl

theorem cell23_3795400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_3795400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795400 prefixEnd_3795400 := by exact prefixLift 3795400
  have htrace : WordTrace (prefixWord ++ tailWord_3795400) baseStart_3795400 baseEnd_3795400 := by
    simpa [prefixWord, tailWord_3795400, baseEnd_3795400] using wordTrace_append hprefix tailTrace_3795400
  have hstable : (prefixWord ++ tailWord_3795400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795400).length < 2 ^ (prefixWord ++ tailWord_3795400).sum := by decide
  have hdescent : baseEnd_3795400 < baseStart_3795400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795404 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3795404 : Nat := 118140960795 + 3795404 * 2 ^ 59
def prefixEnd_3795404 : Nat := 4983230072969 + 3 ^ 40 * 3795404 * 2
def baseEnd_3795404 : Nat := 1948866529997173698095261

theorem tailTrace_3795404 : CollatzResearch.WordTrace tailWord_3795404 prefixEnd_3795404 1948866529997173698095261 := by
  unfold tailWord_3795404
  simp only [CollatzResearch.WordTrace]
  refine ⟨69214878170953493121100633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92286504227937990828134177 69214878170953493121100633)
  ·
    refine ⟨51911158628215119840825475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69214878170953493121100633 51911158628215119840825475)
    ·
      refine ⟨77866737942322679761238213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51911158628215119840825475 77866737942322679761238213)
      ·
        refine ⟨14600013364185502455232165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77866737942322679761238213 14600013364185502455232165)
        ·
          refine ⟨2737502505784781710356031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14600013364185502455232165 2737502505784781710356031)
          ·
            refine ⟨4106253758677172565534047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737502505784781710356031 4106253758677172565534047)
            ·
              refine ⟨6159380638015758848301071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106253758677172565534047 6159380638015758848301071)
              ·
                refine ⟨9239070957023638272451607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6159380638015758848301071 9239070957023638272451607)
                ·
                  refine ⟨13858606435535457408677411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9239070957023638272451607 13858606435535457408677411)
                  ·
                    refine ⟨20787909653303186113016117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13858606435535457408677411 20787909653303186113016117)
                    ·
                      refine ⟨1948866529997173698095261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20787909653303186113016117 1948866529997173698095261)
                      ·
                        rfl

theorem cell23_3795404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3795404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795404 prefixEnd_3795404 := by exact prefixLift 3795404
  have htrace : WordTrace (prefixWord ++ tailWord_3795404) baseStart_3795404 baseEnd_3795404 := by
    simpa [prefixWord, tailWord_3795404, baseEnd_3795404] using wordTrace_append hprefix tailTrace_3795404
  have hstable : (prefixWord ++ tailWord_3795404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795404).length < 2 ^ (prefixWord ++ tailWord_3795404).sum := by decide
  have hdescent : baseEnd_3795404 < baseStart_3795404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795434 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_3795434 : Nat := 118140960795 + 3795434 * 2 ^ 59
def prefixEnd_3795434 : Nat := 4983230072969 + 3 ^ 40 * 3795434 * 2
def baseEnd_3795434 : Nat := 1948881934416808580720123

theorem tailTrace_3795434 : CollatzResearch.WordTrace tailWord_3795434 prefixEnd_3795434 1948881934416808580720123 := by
  unfold tailWord_3795434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34607712632949575341448339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92287233687865534243862237 34607712632949575341448339)
  ·
    refine ⟨51911568949424363012172509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34607712632949575341448339 51911568949424363012172509)
    ·
      refine ⟨19466838356034136129564691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51911568949424363012172509 19466838356034136129564691)
      ·
        refine ⟨29200257534051204194347037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19466838356034136129564691 29200257534051204194347037)
        ·
          refine ⟨10950096575269201572880139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29200257534051204194347037 10950096575269201572880139)
          ·
            refine ⟨16425144862903802359320209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950096575269201572880139 16425144862903802359320209)
            ·
              refine ⟨12318858647177851769490157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16425144862903802359320209 12318858647177851769490157)
              ·
                refine ⟨4619571992691694413558809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12318858647177851769490157 4619571992691694413558809)
                ·
                  refine ⟨3464678994518770810169107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619571992691694413558809 3464678994518770810169107)
                  ·
                    refine ⟨5197018491778156215253661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464678994518770810169107 5197018491778156215253661)
                    ·
                      refine ⟨1948881934416808580720123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197018491778156215253661 1948881934416808580720123)
                      ·
                        rfl

theorem cell23_3795434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_3795434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795434 prefixEnd_3795434 := by exact prefixLift 3795434
  have htrace : WordTrace (prefixWord ++ tailWord_3795434) baseStart_3795434 baseEnd_3795434 := by
    simpa [prefixWord, tailWord_3795434, baseEnd_3795434] using wordTrace_append hprefix tailTrace_3795434
  have hstable : (prefixWord ++ tailWord_3795434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795434).length < 2 ^ (prefixWord ++ tailWord_3795434).sum := by decide
  have hdescent : baseEnd_3795434 < baseStart_3795434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795473 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_3795473 : Nat := 118140960795 + 3795473 * 2 ^ 59
def prefixEnd_3795473 : Nat := 4983230072969 + 3 ^ 40 * 3795473 * 2
def baseEnd_3795473 : Nat := 1948901960162333928132443

theorem tailTrace_3795473 : CollatzResearch.WordTrace tailWord_3795473 prefixEnd_3795473 1948901960162333928132443 := by
  unfold tailWord_3795473
  simp only [CollatzResearch.WordTrace]
  refine ⟨138432272978657011026463073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92288181985771340684308715 138432272978657011026463073)
  ·
    refine ⟨103824204733992758269847305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138432272978657011026463073 103824204733992758269847305)
    ·
      refine ⟨77868153550494568702385479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103824204733992758269847305 77868153550494568702385479)
      ·
        refine ⟨116802230325741853053578219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77868153550494568702385479 116802230325741853053578219)
        ·
          refine ⟨175203345488612779580367329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116802230325741853053578219 175203345488612779580367329)
          ·
            refine ⟨131402509116459584685275497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175203345488612779580367329 131402509116459584685275497)
            ·
              refine ⟨98551881837344688513956623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131402509116459584685275497 98551881837344688513956623)
              ·
                refine ⟨147827822756017032770934935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98551881837344688513956623 147827822756017032770934935)
                ·
                  refine ⟨221741734134025549156402403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147827822756017032770934935 221741734134025549156402403)
                  ·
                    refine ⟨332612601201038323734603605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221741734134025549156402403 332612601201038323734603605)
                    ·
                      refine ⟨1948901960162333928132443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 332612601201038323734603605 1948901960162333928132443)
                      ·
                        rfl

theorem cell23_3795473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3795473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795473 prefixEnd_3795473 := by exact prefixLift 3795473
  have htrace : WordTrace (prefixWord ++ tailWord_3795473) baseStart_3795473 baseEnd_3795473 := by
    simpa [prefixWord, tailWord_3795473, baseEnd_3795473] using wordTrace_append hprefix tailTrace_3795473
  have hstable : (prefixWord ++ tailWord_3795473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795473).length < 2 ^ (prefixWord ++ tailWord_3795473).sum := by decide
  have hdescent : baseEnd_3795473 < baseStart_3795473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795480 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 7]
def baseStart_3795480 : Nat := 118140960795 + 3795480 * 2 ^ 59
def prefixEnd_3795480 : Nat := 4983230072969 + 3 ^ 40 * 3795480 * 2
def baseEnd_3795480 : Nat := 216545061614101711193879

theorem tailTrace_3795480 : CollatzResearch.WordTrace tailWord_3795480 prefixEnd_3795480 216545061614101711193879 := by
  unfold tailWord_3795480
  simp only [CollatzResearch.WordTrace]
  refine ⟨69216264144815825610983947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92288352193087767481311929 69216264144815825610983947)
  ·
    refine ⟨103824396217223738416475921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69216264144815825610983947 103824396217223738416475921)
    ·
      refine ⟨77868297162917803812356941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103824396217223738416475921 77868297162917803812356941)
      ·
        refine ⟨29200611436094176429633853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77868297162917803812356941 29200611436094176429633853)
        ·
          refine ⟨10950229288535316161112695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29200611436094176429633853 10950229288535316161112695)
          ·
            refine ⟨16425343932802974241669043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950229288535316161112695 16425343932802974241669043)
            ·
              refine ⟨24638015899204461362503565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16425343932802974241669043 24638015899204461362503565)
              ·
                refine ⟨9239255962201673010938837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24638015899204461362503565 9239255962201673010938837)
                ·
                  refine ⟨216545061614101711193879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9239255962201673010938837 216545061614101711193879)
                  ·
                    rfl

theorem cell23_3795480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_3795480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795480 prefixEnd_3795480 := by exact prefixLift 3795480
  have htrace : WordTrace (prefixWord ++ tailWord_3795480) baseStart_3795480 baseEnd_3795480 := by
    simpa [prefixWord, tailWord_3795480, baseEnd_3795480] using wordTrace_append hprefix tailTrace_3795480
  have hstable : (prefixWord ++ tailWord_3795480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795480).length < 2 ^ (prefixWord ++ tailWord_3795480).sum := by decide
  have hdescent : baseEnd_3795480 < baseStart_3795480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795514 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_3795514 : Nat := 118140960795 + 3795514 * 2 ^ 59
def prefixEnd_3795514 : Nat := 4983230072969 + 3 ^ 40 * 3795514 * 2
def baseEnd_3795514 : Nat := 216547001429907585302195

theorem tailTrace_3795514 : CollatzResearch.WordTrace tailWord_3795514 prefixEnd_3795514 216547001429907585302195 := by
  unfold tailWord_3795514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34608442092877118757176399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92289178914338983352470397 34608442092877118757176399)
  ·
    refine ⟨51912663139315678135764599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34608442092877118757176399 51912663139315678135764599)
    ·
      refine ⟨77868994708973517203646899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51912663139315678135764599 77868994708973517203646899)
      ·
        refine ⟨116803492063460275805470349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77868994708973517203646899 116803492063460275805470349)
        ·
          refine ⟨43801309523797603427051381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116803492063460275805470349 43801309523797603427051381)
          ·
            refine ⟨4106372767856025321286067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43801309523797603427051381 4106372767856025321286067)
            ·
              refine ⟨6159559151784037981929101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106372767856025321286067 6159559151784037981929101)
              ·
                refine ⟨2309834681919014243223413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6159559151784037981929101 2309834681919014243223413)
                ·
                  refine ⟨216547001429907585302195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2309834681919014243223413 216547001429907585302195)
                  ·
                    rfl

theorem cell23_3795514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_3795514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795514 prefixEnd_3795514 := by exact prefixLift 3795514
  have htrace : WordTrace (prefixWord ++ tailWord_3795514) baseStart_3795514 baseEnd_3795514 := by
    simpa [prefixWord, tailWord_3795514, baseEnd_3795514] using wordTrace_append hprefix tailTrace_3795514
  have hstable : (prefixWord ++ tailWord_3795514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795514).length < 2 ^ (prefixWord ++ tailWord_3795514).sum := by decide
  have hdescent : baseEnd_3795514 < baseStart_3795514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795527 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 2, 5]
def baseStart_3795527 : Nat := 118140960795 + 3795527 * 2 ^ 59
def prefixEnd_3795527 : Nat := 4983230072969 + 3 ^ 40 * 3795527 * 2
def baseEnd_3795527 : Nat := 649643229372558905619065

theorem tailTrace_3795527 : CollatzResearch.WordTrace tailWord_3795527 prefixEnd_3795527 649643229372558905619065 := by
  unfold tailWord_3795527
  simp only [CollatzResearch.WordTrace]
  refine ⟨138434242520461378248928835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92289495013640918832619223 138434242520461378248928835)
  ·
    refine ⟨207651363780692067373393253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138434242520461378248928835 207651363780692067373393253)
    ·
      refine ⟨38934630708879762632511235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207651363780692067373393253 38934630708879762632511235)
      ·
        refine ⟨58401946063319643948766853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38934630708879762632511235 58401946063319643948766853)
        ·
          refine ⟨10950364886872433240393785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58401946063319643948766853 10950364886872433240393785)
          ·
            refine ⟨8212773665154324930295339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10950364886872433240393785 8212773665154324930295339)
            ·
              refine ⟨12319160497731487395443009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212773665154324930295339 12319160497731487395443009)
              ·
                refine ⟨9239370373298615546582257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12319160497731487395443009 9239370373298615546582257)
                ·
                  refine ⟨6929527779973961659936693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9239370373298615546582257 6929527779973961659936693)
                  ·
                    refine ⟨649643229372558905619065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6929527779973961659936693 649643229372558905619065)
                    ·
                      rfl

theorem cell23_3795527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_3795527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795527 prefixEnd_3795527 := by exact prefixLift 3795527
  have htrace : WordTrace (prefixWord ++ tailWord_3795527) baseStart_3795527 baseEnd_3795527 := by
    simpa [prefixWord, tailWord_3795527, baseEnd_3795527] using wordTrace_append hprefix tailTrace_3795527
  have hstable : (prefixWord ++ tailWord_3795527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795527).length < 2 ^ (prefixWord ++ tailWord_3795527).sum := by decide
  have hdescent : baseEnd_3795527 < baseStart_3795527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795567 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_3795567 : Nat := 118140960795 + 3795567 * 2 ^ 59
def prefixEnd_3795567 : Nat := 4983230072969 + 3 ^ 40 * 3795567 * 2
def baseEnd_3795567 : Nat := 1948950227343856560357011

theorem tailTrace_3795567 : CollatzResearch.WordTrace tailWord_3795567 prefixEnd_3795567 1948950227343856560357011 := by
  unfold tailWord_3795567
  simp only [CollatzResearch.WordTrace]
  refine ⟨138435701440316465080384955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92290467626877643386923303 138435701440316465080384955)
  ·
    refine ⟨207653552160474697620577433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138435701440316465080384955 207653552160474697620577433)
    ·
      refine ⟨155740164120356023215433075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207653552160474697620577433 155740164120356023215433075)
      ·
        refine ⟨233610246180534034823149613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155740164120356023215433075 233610246180534034823149613)
        ·
          refine ⟨87603842317700263058681105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233610246180534034823149613 87603842317700263058681105)
          ·
            refine ⟨65702881738275197294010829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87603842317700263058681105 65702881738275197294010829)
            ·
              refine ⟨24638580651853198985254061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65702881738275197294010829 24638580651853198985254061)
              ·
                refine ⟨9239467744444949619470273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24638580651853198985254061 9239467744444949619470273)
                ·
                  refine ⟨6929600808333712214602705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9239467744444949619470273 6929600808333712214602705)
                  ·
                    refine ⟨5197200606250284160952029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6929600808333712214602705 5197200606250284160952029)
                    ·
                      refine ⟨1948950227343856560357011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197200606250284160952029 1948950227343856560357011)
                      ·
                        rfl

theorem cell23_3795567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_3795567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795567 prefixEnd_3795567 := by exact prefixLift 3795567
  have htrace : WordTrace (prefixWord ++ tailWord_3795567) baseStart_3795567 baseEnd_3795567 := by
    simpa [prefixWord, tailWord_3795567, baseEnd_3795567] using wordTrace_append hprefix tailTrace_3795567
  have hstable : (prefixWord ++ tailWord_3795567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795567).length < 2 ^ (prefixWord ++ tailWord_3795567).sum := by decide
  have hdescent : baseEnd_3795567 < baseStart_3795567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795604 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 6]
def baseStart_3795604 : Nat := 118140960795 + 3795604 * 2 ^ 59
def prefixEnd_3795604 : Nat := 4983230072969 + 3 ^ 40 * 3795604 * 2
def baseEnd_3795604 : Nat := 216552136236452546177149

theorem tailTrace_3795604 : CollatzResearch.WordTrace tailWord_3795604 prefixEnd_3795604 216552136236452546177149 := by
  unfold tailWord_3795604
  simp only [CollatzResearch.WordTrace]
  refine ⟨69218525470591210199740933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92291367294121613599654577 69218525470591210199740933)
  ·
    refine ⟨12978473525735851912451425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69218525470591210199740933 12978473525735851912451425)
    ·
      refine ⟨9733855144301888934338569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12978473525735851912451425 9733855144301888934338569)
      ·
        refine ⟨7300391358226416700753927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9733855144301888934338569 7300391358226416700753927)
        ·
          refine ⟨10950587037339625051130891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7300391358226416700753927 10950587037339625051130891)
          ·
            refine ⟨16425880556009437576696337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950587037339625051130891 16425880556009437576696337)
            ·
              refine ⟨12319410417007078182522253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16425880556009437576696337 12319410417007078182522253)
              ·
                refine ⟨4619778906377654318445845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12319410417007078182522253 4619778906377654318445845)
                ·
                  refine ⟨216552136236452546177149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4619778906377654318445845 216552136236452546177149)
                  ·
                    rfl

theorem cell23_3795604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_3795604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795604 prefixEnd_3795604 := by exact prefixLift 3795604
  have htrace : WordTrace (prefixWord ++ tailWord_3795604) baseStart_3795604 baseEnd_3795604 := by
    simpa [prefixWord, tailWord_3795604, baseEnd_3795604] using wordTrace_append hprefix tailTrace_3795604
  have hstable : (prefixWord ++ tailWord_3795604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795604).length < 2 ^ (prefixWord ++ tailWord_3795604).sum := by decide
  have hdescent : baseEnd_3795604 < baseStart_3795604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795631 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 1, 1, 3]
def baseStart_3795631 : Nat := 118140960795 + 3795631 * 2 ^ 59
def prefixEnd_3795631 : Nat := 4983230072969 + 3 ^ 40 * 3795631 * 2
def baseEnd_3795631 : Nat := 1948983090105744309956717

theorem tailTrace_3795631 : CollatzResearch.WordTrace tailWord_3795631 prefixEnd_3795631 1948983090105744309956717 := by
  unfold tailWord_3795631
  simp only [CollatzResearch.WordTrace]
  refine ⟨138438035712084604010714747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92292023808056402673809831 138438035712084604010714747)
  ·
    refine ⟨207657053568126906016072121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138438035712084604010714747 207657053568126906016072121)
    ·
      refine ⟨155742790176095179512054091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207657053568126906016072121 155742790176095179512054091)
      ·
        refine ⟨233614185264142769268081137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155742790176095179512054091 233614185264142769268081137)
        ·
          refine ⟨175210638948107076951060853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233614185264142769268081137 175210638948107076951060853)
          ·
            refine ⟨16425997401385038464161955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175210638948107076951060853 16425997401385038464161955)
            ·
              refine ⟨24638996102077557696242933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16425997401385038464161955 24638996102077557696242933)
              ·
                refine ⟨2309905884569771034022775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24638996102077557696242933 2309905884569771034022775)
                ·
                  refine ⟨3464858826854656551034163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309905884569771034022775 3464858826854656551034163)
                  ·
                    refine ⟨5197288240281984826551245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464858826854656551034163 5197288240281984826551245)
                    ·
                      refine ⟨1948983090105744309956717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197288240281984826551245 1948983090105744309956717)
                      ·
                        rfl

theorem cell23_3795631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 1, 3].length) (baseStart_3795631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795631 prefixEnd_3795631 := by exact prefixLift 3795631
  have htrace : WordTrace (prefixWord ++ tailWord_3795631) baseStart_3795631 baseEnd_3795631 := by
    simpa [prefixWord, tailWord_3795631, baseEnd_3795631] using wordTrace_append hprefix tailTrace_3795631
  have hstable : (prefixWord ++ tailWord_3795631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795631).length < 2 ^ (prefixWord ++ tailWord_3795631).sum := by decide
  have hdescent : baseEnd_3795631 < baseStart_3795631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795638 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_3795638 : Nat := 118140960795 + 3795638 * 2 ^ 59
def prefixEnd_3795638 : Nat := 4983230072969 + 3 ^ 40 * 3795638 * 2
def baseEnd_3795638 : Nat := 216554076052258420285465

theorem tailTrace_3795638 : CollatzResearch.WordTrace tailWord_3795638 prefixEnd_3795638 216554076052258420285465 := by
  unfold tailWord_3795638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652393188941202762888723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92292194015372829470813045 8652393188941202762888723)
  ·
    refine ⟨12978589783411804144333085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8652393188941202762888723 12978589783411804144333085)
    ·
      refine ⟨4866971168779426554124907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12978589783411804144333085 4866971168779426554124907)
      ·
        refine ⟨7300456753169139831187361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866971168779426554124907 7300456753169139831187361)
        ·
          refine ⟨5475342564876854873390521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7300456753169139831187361 5475342564876854873390521)
          ·
            refine ⟨4106506923657641155042891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475342564876854873390521 4106506923657641155042891)
            ·
              refine ⟨6159760385486461732564337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106506923657641155042891 6159760385486461732564337)
              ·
                refine ⟨4619820289114846299423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6159760385486461732564337 4619820289114846299423253)
                ·
                  refine ⟨216554076052258420285465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4619820289114846299423253 216554076052258420285465)
                  ·
                    rfl

theorem cell23_3795638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_3795638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795638 prefixEnd_3795638 := by exact prefixLift 3795638
  have htrace : WordTrace (prefixWord ++ tailWord_3795638) baseStart_3795638 baseEnd_3795638 := by
    simpa [prefixWord, tailWord_3795638, baseEnd_3795638] using wordTrace_append hprefix tailTrace_3795638
  have hstable : (prefixWord ++ tailWord_3795638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795638).length < 2 ^ (prefixWord ++ tailWord_3795638).sum := by decide
  have hdescent : baseEnd_3795638 < baseStart_3795638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795671 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 3, 2, 2]
def baseStart_3795671 : Nat := 118140960795 + 3795671 * 2 ^ 59
def prefixEnd_3795671 : Nat := 4983230072969 + 3 ^ 40 * 3795671 * 2
def baseEnd_3795671 : Nat := 1949003629331924153456533

theorem tailTrace_3795671 : CollatzResearch.WordTrace tailWord_3795671 prefixEnd_3795671 1949003629331924153456533 := by
  unfold tailWord_3795671
  simp only [CollatzResearch.WordTrace]
  refine ⟨138439494631939690842170867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92292996421293127228113911 138439494631939690842170867)
  ·
    refine ⟨207659241947909536263256301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138439494631939690842170867 207659241947909536263256301)
    ·
      refine ⟨77872215730466076098721113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207659241947909536263256301 77872215730466076098721113)
      ·
        refine ⟨58404161797849557074040835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77872215730466076098721113 58404161797849557074040835)
        ·
          refine ⟨87606242696774335611061253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58404161797849557074040835 87606242696774335611061253)
          ·
            refine ⟨16426170505645187927073985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87606242696774335611061253 16426170505645187927073985)
            ·
              refine ⟨12319627879233890945305489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16426170505645187927073985 12319627879233890945305489)
              ·
                refine ⟨9239720909425418208979117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12319627879233890945305489 9239720909425418208979117)
                ·
                  refine ⟨3464895341034531828367169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9239720909425418208979117 3464895341034531828367169)
                  ·
                    refine ⟨2598671505775898871275377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3464895341034531828367169 2598671505775898871275377)
                    ·
                      refine ⟨1949003629331924153456533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598671505775898871275377 1949003629331924153456533)
                      ·
                        rfl

theorem cell23_3795671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_3795671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795671 prefixEnd_3795671 := by exact prefixLift 3795671
  have htrace : WordTrace (prefixWord ++ tailWord_3795671) baseStart_3795671 baseEnd_3795671 := by
    simpa [prefixWord, tailWord_3795671, baseEnd_3795671] using wordTrace_append hprefix tailTrace_3795671
  have hstable : (prefixWord ++ tailWord_3795671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795671).length < 2 ^ (prefixWord ++ tailWord_3795671).sum := by decide
  have hdescent : baseEnd_3795671 < baseStart_3795671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795704 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_3795704 : Nat := 118140960795 + 3795704 * 2 ^ 59
def prefixEnd_3795704 : Nat := 4983230072969 + 3 ^ 40 * 3795704 * 2
def baseEnd_3795704 : Nat := 1949020574193522524343881

theorem tailTrace_3795704 : CollatzResearch.WordTrace tailWord_3795704 prefixEnd_3795704 1949020574193522524343881 := by
  unfold tailWord_3795704
  simp only [CollatzResearch.WordTrace]
  refine ⟨69220349120410068739061083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92293798827213424985414777 69220349120410068739061083)
  ·
    refine ⟨103830523680615103108591625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69220349120410068739061083 103830523680615103108591625)
    ·
      refine ⟨77872892760461327331443719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103830523680615103108591625 77872892760461327331443719)
      ·
        refine ⟨116809339140691990997165579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77872892760461327331443719 116809339140691990997165579)
        ·
          refine ⟨175214008711037986495748369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116809339140691990997165579 175214008711037986495748369)
          ·
            refine ⟨131410506533278489871811277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175214008711037986495748369 131410506533278489871811277)
            ·
              refine ⟨49278939949979433701929229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131410506533278489871811277 49278939949979433701929229)
              ·
                refine ⟨18479602481242287638223461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49278939949979433701929229 18479602481242287638223461)
                ·
                  refine ⟨3464925465232928932166899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18479602481242287638223461 3464925465232928932166899)
                  ·
                    refine ⟨5197388197849393398250349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464925465232928932166899 5197388197849393398250349)
                    ·
                      refine ⟨1949020574193522524343881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197388197849393398250349 1949020574193522524343881)
                      ·
                        rfl

theorem cell23_3795704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_3795704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795704 prefixEnd_3795704 := by exact prefixLift 3795704
  have htrace : WordTrace (prefixWord ++ tailWord_3795704) baseStart_3795704 baseEnd_3795704 := by
    simpa [prefixWord, tailWord_3795704, baseEnd_3795704] using wordTrace_append hprefix tailTrace_3795704
  have hstable : (prefixWord ++ tailWord_3795704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795704).length < 2 ^ (prefixWord ++ tailWord_3795704).sum := by decide
  have hdescent : baseEnd_3795704 < baseStart_3795704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795767 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 7]
def baseStart_3795767 : Nat := 118140960795 + 3795767 * 2 ^ 59
def prefixEnd_3795767 : Nat := 4983230072969 + 3 ^ 40 * 3795767 * 2
def baseEnd_3795767 : Nat := 216561435941639530872899

theorem tailTrace_3795767 : CollatzResearch.WordTrace tailWord_3795767 prefixEnd_3795767 216561435941639530872899 := by
  unfold tailWord_3795767
  simp only [CollatzResearch.WordTrace]
  refine ⟨138442996039591899237665555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92295330693061266158443703 138442996039591899237665555)
  ·
    refine ⟨207664494059387848856498333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138442996039591899237665555 207664494059387848856498333)
    ·
      refine ⟨77874185272270443321186875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207664494059387848856498333 77874185272270443321186875)
      ·
        refine ⟨116811277908405664981780313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77874185272270443321186875 116811277908405664981780313)
        ·
          refine ⟨87608458431304248736335235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116811277908405664981780313 87608458431304248736335235)
          ·
            refine ⟨131412687646956373104502853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87608458431304248736335235 131412687646956373104502853)
            ·
              refine ⟨24639878933804319957094285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131412687646956373104502853 24639878933804319957094285)
              ·
                refine ⟨9239954600176619983910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24639878933804319957094285 9239954600176619983910357)
                ·
                  refine ⟨216561435941639530872899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9239954600176619983910357 216561435941639530872899)
                  ·
                    rfl

theorem cell23_3795767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 7].length) (baseStart_3795767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795767 prefixEnd_3795767 := by exact prefixLift 3795767
  have htrace : WordTrace (prefixWord ++ tailWord_3795767) baseStart_3795767 baseEnd_3795767 := by
    simpa [prefixWord, tailWord_3795767, baseEnd_3795767] using wordTrace_append hprefix tailTrace_3795767
  have hstable : (prefixWord ++ tailWord_3795767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795767).length < 2 ^ (prefixWord ++ tailWord_3795767).sum := by decide
  have hdescent : baseEnd_3795767 < baseStart_3795767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795794 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3795794 : Nat := 118140960795 + 3795794 * 2 ^ 59
def prefixEnd_3795794 : Nat := 4983230072969 + 3 ^ 40 * 3795794 * 2
def baseEnd_3795794 : Nat := 1949066787452427172218467

theorem tailTrace_3795794 : CollatzResearch.WordTrace tailWord_3795794 prefixEnd_3795794 1949066787452427172218467 := by
  unfold tailWord_3795794
  simp only [CollatzResearch.WordTrace]
  refine ⟨34610995202623520712224609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92295987206996055232598957 34610995202623520712224609)
  ·
    refine ⟨25958246401967640534168457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34610995202623520712224609 25958246401967640534168457)
    ·
      refine ⟨19468684801475730400626343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25958246401967640534168457 19468684801475730400626343)
      ·
        refine ⟨29203027202213595600939515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19468684801475730400626343 29203027202213595600939515)
        ·
          refine ⟨43804540803320393401409273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29203027202213595600939515 43804540803320393401409273)
          ·
            refine ⟨32853405602490295051056955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43804540803320393401409273 32853405602490295051056955)
            ·
              refine ⟨49280108403735442576585433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32853405602490295051056955 49280108403735442576585433)
              ·
                refine ⟨36960081302801581932439075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49280108403735442576585433 36960081302801581932439075)
                ·
                  refine ⟨55440121954202372898658613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36960081302801581932439075 55440121954202372898658613)
                  ·
                    refine ⟨5197511433206472459249245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55440121954202372898658613 5197511433206472459249245)
                    ·
                      refine ⟨1949066787452427172218467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197511433206472459249245 1949066787452427172218467)
                      ·
                        rfl

theorem cell23_3795794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3795794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795794 prefixEnd_3795794 := by exact prefixLift 3795794
  have htrace : WordTrace (prefixWord ++ tailWord_3795794) baseStart_3795794 baseEnd_3795794 := by
    simpa [prefixWord, tailWord_3795794, baseEnd_3795794] using wordTrace_append hprefix tailTrace_3795794
  have hstable : (prefixWord ++ tailWord_3795794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795794).length < 2 ^ (prefixWord ++ tailWord_3795794).sum := by decide
  have hdescent : baseEnd_3795794 < baseStart_3795794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795801 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 5]
def baseStart_3795801 : Nat := 118140960795 + 3795801 * 2 ^ 59
def prefixEnd_3795801 : Nat := 4983230072969 + 3 ^ 40 * 3795801 * 2
def baseEnd_3795801 : Nat := 216563375757445404981215

theorem tailTrace_3795801 : CollatzResearch.WordTrace tailWord_3795801 prefixEnd_3795801 216563375757445404981215 := by
  unfold tailWord_3795801
  simp only [CollatzResearch.WordTrace]
  refine ⟨138444236121468723044403257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92296157414312482029602171 138444236121468723044403257)
  ·
    refine ⟨103833177091101542283302443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138444236121468723044403257 103833177091101542283302443)
    ·
      refine ⟨155749765636652313424953665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103833177091101542283302443 155749765636652313424953665)
      ·
        refine ⟨116812324227489235068715249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155749765636652313424953665 116812324227489235068715249)
        ·
          refine ⟨87609243170616926301536437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116812324227489235068715249 87609243170616926301536437)
          ·
            refine ⟨8213366547245336840769041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87609243170616926301536437 8213366547245336840769041)
            ·
              refine ⟨6160024910434002630576781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8213366547245336840769041 6160024910434002630576781)
              ·
                refine ⟨2310009341412750986466293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6160024910434002630576781 2310009341412750986466293)
                ·
                  refine ⟨216563375757445404981215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310009341412750986466293 216563375757445404981215)
                  ·
                    rfl

theorem cell23_3795801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 5].length) (baseStart_3795801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795801 prefixEnd_3795801 := by exact prefixLift 3795801
  have htrace : WordTrace (prefixWord ++ tailWord_3795801) baseStart_3795801 baseEnd_3795801 := by
    simpa [prefixWord, tailWord_3795801, baseEnd_3795801] using wordTrace_append hprefix tailTrace_3795801
  have hstable : (prefixWord ++ tailWord_3795801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795801).length < 2 ^ (prefixWord ++ tailWord_3795801).sum := by decide
  have hdescent : baseEnd_3795801 < baseStart_3795801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795867 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_3795867 : Nat := 118140960795 + 3795867 * 2 ^ 59
def prefixEnd_3795867 : Nat := 4983230072969 + 3 ^ 40 * 3795867 * 2
def baseEnd_3795867 : Nat := 1949104271540205386605631

theorem tailTrace_3795867 : CollatzResearch.WordTrace tailWord_3795867 prefixEnd_3795867 1949104271540205386605631 := by
  unfold tailWord_3795867
  simp only [CollatzResearch.WordTrace]
  refine ⟨138446643339229616316305855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92297762226153077544203903 138446643339229616316305855)
  ·
    refine ⟨207669965008844424474458783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138446643339229616316305855 207669965008844424474458783)
    ·
      refine ⟨311504947513266636711688175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207669965008844424474458783 311504947513266636711688175)
      ·
        refine ⟨467257421269899955067532263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311504947513266636711688175 467257421269899955067532263)
        ·
          refine ⟨700886131904849932601298395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467257421269899955067532263 700886131904849932601298395)
          ·
            refine ⟨1051329197857274898901947593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700886131904849932601298395 1051329197857274898901947593)
            ·
              refine ⟨788496898392956174176460695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051329197857274898901947593 788496898392956174176460695)
              ·
                refine ⟨1182745347589434261264691043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788496898392956174176460695 1182745347589434261264691043)
                ·
                  refine ⟨1774118021384151391897036565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182745347589434261264691043 1774118021384151391897036565)
                  ·
                    refine ⟨83161782252382096495173589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1774118021384151391897036565 83161782252382096495173589)
                    ·
                      refine ⟨1949104271540205386605631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83161782252382096495173589 1949104271540205386605631)
                      ·
                        rfl

theorem cell23_3795867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_3795867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795867 prefixEnd_3795867 := by exact prefixLift 3795867
  have htrace : WordTrace (prefixWord ++ tailWord_3795867) baseStart_3795867 baseEnd_3795867 := by
    simpa [prefixWord, tailWord_3795867, baseEnd_3795867] using wordTrace_append hprefix tailTrace_3795867
  have hstable : (prefixWord ++ tailWord_3795867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795867).length < 2 ^ (prefixWord ++ tailWord_3795867).sum := by decide
  have hdescent : baseEnd_3795867 < baseStart_3795867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795868 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3795868 : Nat := 118140960795 + 3795868 * 2 ^ 59
def prefixEnd_3795868 : Nat := 4983230072969 + 3 ^ 40 * 3795868 * 2
def baseEnd_3795868 : Nat := 1949104785020859882693127

theorem tailTrace_3795868 : CollatzResearch.WordTrace tailWord_3795868 prefixEnd_3795868 1949104785020859882693127 := by
  unfold tailWord_3795868
  simp only [CollatzResearch.WordTrace]
  refine ⟨69223339906112996743546129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92297786541483995658061505 69223339906112996743546129)
  ·
    refine ⟨51917504929584747557659597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69223339906112996743546129 51917504929584747557659597)
    ·
      refine ⟨19469064348594280334122349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51917504929584747557659597 19469064348594280334122349)
      ·
        refine ⟨7300899130722855125295881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19469064348594280334122349 7300899130722855125295881)
        ·
          refine ⟨5475674348042141343971911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7300899130722855125295881 5475674348042141343971911)
          ·
            refine ⟨8213511522063212015957867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475674348042141343971911 8213511522063212015957867)
            ·
              refine ⟨12320267283094818023936801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213511522063212015957867 12320267283094818023936801)
              ·
                refine ⟨9240200462321113517952601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12320267283094818023936801 9240200462321113517952601)
                ·
                  refine ⟨6930150346740835138464451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240200462321113517952601 6930150346740835138464451)
                  ·
                    refine ⟨10395225520111252707696677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930150346740835138464451 10395225520111252707696677)
                    ·
                      refine ⟨1949104785020859882693127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10395225520111252707696677 1949104785020859882693127)
                      ·
                        rfl

theorem cell23_3795868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3795868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795868 prefixEnd_3795868 := by exact prefixLift 3795868
  have htrace : WordTrace (prefixWord ++ tailWord_3795868) baseStart_3795868 baseEnd_3795868 := by
    simpa [prefixWord, tailWord_3795868, baseEnd_3795868] using wordTrace_append hprefix tailTrace_3795868
  have hstable : (prefixWord ++ tailWord_3795868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795868).length < 2 ^ (prefixWord ++ tailWord_3795868).sum := by decide
  have hdescent : baseEnd_3795868 < baseStart_3795868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795871 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3795871 : Nat := 118140960795 + 3795871 * 2 ^ 59
def prefixEnd_3795871 : Nat := 4983230072969 + 3 ^ 40 * 3795871 * 2
def baseEnd_3795871 : Nat := 1949106325462823370955613

theorem tailTrace_3795871 : CollatzResearch.WordTrace tailWord_3795871 prefixEnd_3795871 1949106325462823370955613 := by
  unfold tailWord_3795871
  simp only [CollatzResearch.WordTrace]
  refine ⟨138446789231215124999451467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92297859487476749999634311 138446789231215124999451467)
  ·
    refine ⟨207670183846822687499177201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138446789231215124999451467 207670183846822687499177201)
    ·
      refine ⟨155752637885117015624382901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207670183846822687499177201 155752637885117015624382901)
      ·
        refine ⟨14601809801729720214785897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155752637885117015624382901 14601809801729720214785897)
        ·
          refine ⟨10951357351297290161089423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14601809801729720214785897 10951357351297290161089423)
          ·
            refine ⟨16427036026945935241634135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951357351297290161089423 16427036026945935241634135)
            ·
              refine ⟨24640554040418902862451203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427036026945935241634135 24640554040418902862451203)
              ·
                refine ⟨36960831060628354293676805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24640554040418902862451203 36960831060628354293676805)
                ·
                  refine ⟨6930155823867816430064401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36960831060628354293676805 6930155823867816430064401)
                  ·
                    refine ⟨5197616867900862322548301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6930155823867816430064401 5197616867900862322548301)
                    ·
                      refine ⟨1949106325462823370955613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197616867900862322548301 1949106325462823370955613)
                      ·
                        rfl

theorem cell23_3795871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3795871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795871 prefixEnd_3795871 := by exact prefixLift 3795871
  have htrace : WordTrace (prefixWord ++ tailWord_3795871) baseStart_3795871 baseEnd_3795871 := by
    simpa [prefixWord, tailWord_3795871, baseEnd_3795871] using wordTrace_append hprefix tailTrace_3795871
  have hstable : (prefixWord ++ tailWord_3795871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795871).length < 2 ^ (prefixWord ++ tailWord_3795871).sum := by decide
  have hdescent : baseEnd_3795871 < baseStart_3795871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795911 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_3795911 : Nat := 118140960795 + 3795911 * 2 ^ 59
def prefixEnd_3795911 : Nat := 4983230072969 + 3 ^ 40 * 3795911 * 2
def baseEnd_3795911 : Nat := 1949126864689003214455429

theorem tailTrace_3795911 : CollatzResearch.WordTrace tailWord_3795911 prefixEnd_3795911 1949126864689003214455429 := by
  unfold tailWord_3795911
  simp only [CollatzResearch.WordTrace]
  refine ⟨138448248151070211830907587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92298832100713474553938391 138448248151070211830907587)
  ·
    refine ⟨207672372226605317746361381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138448248151070211830907587 207672372226605317746361381)
    ·
      refine ⟨38938569792488497077442759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207672372226605317746361381 38938569792488497077442759)
      ·
        refine ⟨58407854688732745616164139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38938569792488497077442759 58407854688732745616164139)
        ·
          refine ⟨87611782033099118424246209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58407854688732745616164139 87611782033099118424246209)
          ·
            refine ⟨65708836524824338818184657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87611782033099118424246209 65708836524824338818184657)
            ·
              refine ⟨49281627393618254113638493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65708836524824338818184657 49281627393618254113638493)
              ·
                refine ⟨18480610272606845292614435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49281627393618254113638493 18480610272606845292614435)
                ·
                  refine ⟨27720915408910267938921653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18480610272606845292614435 27720915408910267938921653)
                  ·
                    refine ⟨2598835819585337619273905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27720915408910267938921653 2598835819585337619273905)
                    ·
                      refine ⟨1949126864689003214455429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598835819585337619273905 1949126864689003214455429)
                      ·
                        rfl

theorem cell23_3795911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_3795911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795911 prefixEnd_3795911 := by exact prefixLift 3795911
  have htrace : WordTrace (prefixWord ++ tailWord_3795911) baseStart_3795911 baseEnd_3795911 := by
    simpa [prefixWord, tailWord_3795911, baseEnd_3795911] using wordTrace_append hprefix tailTrace_3795911
  have hstable : (prefixWord ++ tailWord_3795911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795911).length < 2 ^ (prefixWord ++ tailWord_3795911).sum := by decide
  have hdescent : baseEnd_3795911 < baseStart_3795911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795928 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2]
def baseStart_3795928 : Nat := 118140960795 + 3795928 * 2 ^ 59
def prefixEnd_3795928 : Nat := 4983230072969 + 3 ^ 40 * 3795928 * 2
def baseEnd_3795928 : Nat := 1949135593860129647942851

theorem tailTrace_3795928 : CollatzResearch.WordTrace tailWord_3795928 prefixEnd_3795928 1949135593860129647942851 := by
  unfold tailWord_3795928
  simp only [CollatzResearch.WordTrace]
  refine ⟨69224434096004311867138219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92299245461339082489517625 69224434096004311867138219)
  ·
    refine ⟨103836651144006467800707329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69224434096004311867138219 103836651144006467800707329)
    ·
      refine ⟨77877488358004850850530497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103836651144006467800707329 77877488358004850850530497)
      ·
        refine ⟨58408116268503638137897873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77877488358004850850530497 58408116268503638137897873)
        ·
          refine ⟨43806087201377728603423405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58408116268503638137897873 43806087201377728603423405)
          ·
            refine ⟨16427282700516648226283777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43806087201377728603423405 16427282700516648226283777)
            ·
              refine ⟨12320462025387486169712833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16427282700516648226283777 12320462025387486169712833)
              ·
                refine ⟨9240346519040614627284625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12320462025387486169712833 9240346519040614627284625)
                ·
                  refine ⟨6930259889280460970463469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240346519040614627284625 6930259889280460970463469)
                  ·
                    refine ⟨2598847458480172863923801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6930259889280460970463469 2598847458480172863923801)
                    ·
                      refine ⟨1949135593860129647942851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598847458480172863923801 1949135593860129647942851)
                      ·
                        rfl

theorem cell23_3795928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_3795928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795928 prefixEnd_3795928 := by exact prefixLift 3795928
  have htrace : WordTrace (prefixWord ++ tailWord_3795928) baseStart_3795928 baseEnd_3795928 := by
    simpa [prefixWord, tailWord_3795928, baseEnd_3795928] using wordTrace_append hprefix tailTrace_3795928
  have hstable : (prefixWord ++ tailWord_3795928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795928).length < 2 ^ (prefixWord ++ tailWord_3795928).sum := by decide
  have hdescent : baseEnd_3795928 < baseStart_3795928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795938 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3795938 : Nat := 118140960795 + 3795938 * 2 ^ 59
def prefixEnd_3795938 : Nat := 4983230072969 + 3 ^ 40 * 3795938 * 2
def baseEnd_3795938 : Nat := 649713576222224869605935

theorem tailTrace_3795938 : CollatzResearch.WordTrace tailWord_3795938 prefixEnd_3795938 649713576222224869605935 := by
  unfold tailWord_3795938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34612308230493098860535117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92299488614648263628093645 34612308230493098860535117)
  ·
    refine ⟨12979615586434912072700669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34612308230493098860535117 12979615586434912072700669)
    ·
      refine ⟨4867355844913092027262751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12979615586434912072700669 4867355844913092027262751)
      ·
        refine ⟨7301033767369638040894127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867355844913092027262751 7301033767369638040894127)
        ·
          refine ⟨10951550651054457061341191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301033767369638040894127 10951550651054457061341191)
          ·
            refine ⟨16427325976581685592011787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951550651054457061341191 16427325976581685592011787)
            ·
              refine ⟨24640988964872528388017681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427325976581685592011787 24640988964872528388017681)
              ·
                refine ⟨18480741723654396291013261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24640988964872528388017681 18480741723654396291013261)
                ·
                  refine ⟨6930278146370398609129973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18480741723654396291013261 6930278146370398609129973)
                  ·
                    refine ⟨649713576222224869605935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6930278146370398609129973 649713576222224869605935)
                    ·
                      rfl

theorem cell23_3795938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3795938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795938 prefixEnd_3795938 := by exact prefixLift 3795938
  have htrace : WordTrace (prefixWord ++ tailWord_3795938) baseStart_3795938 baseEnd_3795938 := by
    simpa [prefixWord, tailWord_3795938, baseEnd_3795938] using wordTrace_append hprefix tailTrace_3795938
  have hstable : (prefixWord ++ tailWord_3795938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795938).length < 2 ^ (prefixWord ++ tailWord_3795938).sum := by decide
  have hdescent : baseEnd_3795938 < baseStart_3795938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
