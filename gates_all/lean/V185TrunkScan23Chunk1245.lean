import V185TrunkScan23Chunk1244

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7375150 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7375150 : Nat := 118140960795 + 7375150 * 2 ^ 59
def prefixEnd_7375150 : Nat := 4983230072969 + 3 ^ 40 * 7375150 * 2
def baseEnd_7375150 : Nat := 1262332283002308308469103

theorem tailTrace_7375150 : CollatzResearch.WordTrace tailWord_7375150 prefixEnd_7375150 1262332283002308308469103 := by
  unfold tailWord_7375150
  simp only [CollatzResearch.WordTrace]
  refine ⟨33624227403887325023149363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179329212820732400123463269 33624227403887325023149363)
  ·
    refine ⟨50436341105830987534724045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33624227403887325023149363 50436341105830987534724045)
    ·
      refine ⟨18913627914686620325521517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50436341105830987534724045 18913627914686620325521517)
      ·
        refine ⟨7092610468007482622070569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18913627914686620325521517 7092610468007482622070569)
        ·
          refine ⟨5319457851005611966552927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7092610468007482622070569 5319457851005611966552927)
          ·
            refine ⟨7979186776508417949829391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319457851005611966552927 7979186776508417949829391)
            ·
              refine ⟨11968780164762626924744087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979186776508417949829391 11968780164762626924744087)
              ·
                refine ⟨17953170247143940387116131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11968780164762626924744087 17953170247143940387116131)
                ·
                  refine ⟨26929755370715910580674197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17953170247143940387116131 26929755370715910580674197)
                  ·
                    refine ⟨1262332283002308308469103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26929755370715910580674197 1262332283002308308469103)
                    ·
                      rfl

theorem cell23_7375150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7375150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375150 prefixEnd_7375150 := by exact prefixLift 7375150
  have htrace : WordTrace (prefixWord ++ tailWord_7375150) baseStart_7375150 baseEnd_7375150 := by
    simpa [prefixWord, tailWord_7375150, baseEnd_7375150] using wordTrace_append hprefix tailTrace_7375150
  have hstable : (prefixWord ++ tailWord_7375150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375150).length < 2 ^ (prefixWord ++ tailWord_7375150).sum := by decide
  have hdescent : baseEnd_7375150 < baseStart_7375150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375153 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 1, 2, 4]
def baseStart_7375153 : Nat := 118140960795 + 7375153 * 2 ^ 59
def prefixEnd_7375153 : Nat := 4983230072969 + 3 ^ 40 * 7375153 * 2
def baseEnd_7375153 : Nat := 3786998389448888413669795

theorem tailTrace_7375153 : CollatzResearch.WordTrace tailWord_7375153 prefixEnd_7375153 3786998389448888413669795 := by
  unfold tailWord_7375153
  simp only [CollatzResearch.WordTrace]
  refine ⟨268993928650087731697554113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179329285766725154465036075 268993928650087731697554113)
  ·
    refine ⟨201745446487565798773165585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268993928650087731697554113 201745446487565798773165585)
    ·
      refine ⟨151309084865674349079874189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201745446487565798773165585 151309084865674349079874189)
      ·
        refine ⟨56740906824627880904952821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151309084865674349079874189 56740906824627880904952821)
        ·
          refine ⟨5319460014808863834839327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56740906824627880904952821 5319460014808863834839327)
          ·
            refine ⟨7979190022213295752258991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319460014808863834839327 7979190022213295752258991)
            ·
              refine ⟨11968785033319943628388487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979190022213295752258991 11968785033319943628388487)
              ·
                refine ⟨17953177549979915442582731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11968785033319943628388487 17953177549979915442582731)
                ·
                  refine ⟨26929766324969873163874097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17953177549979915442582731 26929766324969873163874097)
                  ·
                    refine ⟨20197324743727404872905573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26929766324969873163874097 20197324743727404872905573)
                    ·
                      refine ⟨3786998389448888413669795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20197324743727404872905573 3786998389448888413669795)
                      ·
                        rfl

theorem cell23_7375153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_7375153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375153 prefixEnd_7375153 := by exact prefixLift 7375153
  have htrace : WordTrace (prefixWord ++ tailWord_7375153) baseStart_7375153 baseEnd_7375153 := by
    simpa [prefixWord, tailWord_7375153, baseEnd_7375153] using wordTrace_append hprefix tailTrace_7375153
  have hstable : (prefixWord ++ tailWord_7375153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375153).length < 2 ^ (prefixWord ++ tailWord_7375153).sum := by decide
  have hdescent : baseEnd_7375153 < baseStart_7375153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375192 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_7375192 : Nat := 118140960795 + 7375192 * 2 ^ 59
def prefixEnd_7375192 : Nat := 4983230072969 + 3 ^ 40 * 7375192 * 2
def baseEnd_7375192 : Nat := 3787018415194413761082115

theorem tailTrace_7375192 : CollatzResearch.WordTrace tailWord_7375192 prefixEnd_7375192 3787018415194413761082115 := by
  unfold tailWord_7375192
  simp only [CollatzResearch.WordTrace]
  refine ⟨134497675548473220679111915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179330234064630960905482553 134497675548473220679111915)
  ·
    refine ⟨201746513322709831018667873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134497675548473220679111915 201746513322709831018667873)
    ·
      refine ⟨151309884992032373264000905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201746513322709831018667873 151309884992032373264000905)
      ·
        refine ⟨113482413744024279948000679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151309884992032373264000905 113482413744024279948000679)
        ·
          refine ⟨170223620616036419922001019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113482413744024279948000679 170223620616036419922001019)
          ·
            refine ⟨255335430924054629883001529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170223620616036419922001019 255335430924054629883001529)
            ·
              refine ⟨191501573193040972412251147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255335430924054629883001529 191501573193040972412251147)
              ·
                refine ⟨287252359789561458618376721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191501573193040972412251147 287252359789561458618376721)
                ·
                  refine ⟨215439269842171093963782541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287252359789561458618376721 215439269842171093963782541)
                  ·
                    refine ⟨80789726190814160236418453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215439269842171093963782541 80789726190814160236418453)
                    ·
                      refine ⟨3787018415194413761082115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80789726190814160236418453 3787018415194413761082115)
                      ·
                        rfl

theorem cell23_7375192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_7375192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375192 prefixEnd_7375192 := by exact prefixLift 7375192
  have htrace : WordTrace (prefixWord ++ tailWord_7375192) baseStart_7375192 baseEnd_7375192 := by
    simpa [prefixWord, tailWord_7375192, baseEnd_7375192] using wordTrace_append hprefix tailTrace_7375192
  have hstable : (prefixWord ++ tailWord_7375192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375192).length < 2 ^ (prefixWord ++ tailWord_7375192).sum := by decide
  have hdescent : baseEnd_7375192 < baseStart_7375192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375234 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7375234 : Nat := 118140960795 + 7375234 * 2 ^ 59
def prefixEnd_7375234 : Nat := 4983230072969 + 3 ^ 40 * 7375234 * 2
def baseEnd_7375234 : Nat := 3787039981381902596756923

theorem tailTrace_7375234 : CollatzResearch.WordTrace tailWord_7375234 prefixEnd_7375234 3787039981381902596756923 := by
  unfold tailWord_7375234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67249220740698570632813189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179331255308529521687501837 67249220740698570632813189)
  ·
    refine ⟨12609228888880981993652473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67249220740698570632813189 12609228888880981993652473)
    ·
      refine ⟨9456921666660736495239355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12609228888880981993652473 9456921666660736495239355)
      ·
        refine ⟨14185382499991104742859033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9456921666660736495239355 14185382499991104742859033)
        ·
          refine ⟨10639036874993328557144275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14185382499991104742859033 10639036874993328557144275)
          ·
            refine ⟨15958555312489992835716413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10639036874993328557144275 15958555312489992835716413)
            ·
              refine ⟨5984458242183747313393655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15958555312489992835716413 5984458242183747313393655)
              ·
                refine ⟨8976687363275620970090483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984458242183747313393655 8976687363275620970090483)
                ·
                  refine ⟨13465031044913431455135725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8976687363275620970090483 13465031044913431455135725)
                  ·
                    refine ⟨5049386641842536795675897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13465031044913431455135725 5049386641842536795675897)
                    ·
                      refine ⟨3787039981381902596756923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049386641842536795675897 3787039981381902596756923)
                      ·
                        rfl

theorem cell23_7375234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7375234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375234 prefixEnd_7375234 := by exact prefixLift 7375234
  have htrace : WordTrace (prefixWord ++ tailWord_7375234) baseStart_7375234 baseEnd_7375234 := by
    simpa [prefixWord, tailWord_7375234, baseEnd_7375234] using wordTrace_append hprefix tailTrace_7375234
  have hstable : (prefixWord ++ tailWord_7375234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375234).length < 2 ^ (prefixWord ++ tailWord_7375234).sum := by decide
  have hdescent : baseEnd_7375234 < baseStart_7375234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375236 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 5]
def baseStart_7375236 : Nat := 118140960795 + 7375236 * 2 ^ 59
def prefixEnd_7375236 : Nat := 4983230072969 + 3 ^ 40 * 7375236 * 2
def baseEnd_7375236 : Nat := 420782334260356843214657

theorem tailTrace_7375236 : CollatzResearch.WordTrace tailWord_7375236 prefixEnd_7375236 420782334260356843214657 := by
  unfold tailWord_7375236
  simp only [CollatzResearch.WordTrace]
  refine ⟨134498477954393518436412781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179331303939191357915217041 134498477954393518436412781)
  ·
    refine ⟨50436929232897569413654793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134498477954393518436412781 50436929232897569413654793)
    ·
      refine ⟨37827696924673177060241095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50436929232897569413654793 37827696924673177060241095)
      ·
        refine ⟨56741545387009765590361643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37827696924673177060241095 56741545387009765590361643)
        ·
          refine ⟨85112318080514648385542465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56741545387009765590361643 85112318080514648385542465)
          ·
            refine ⟨63834238560385986289156849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85112318080514648385542465 63834238560385986289156849)
            ·
              refine ⟨47875678920289489716867637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63834238560385986289156849 47875678920289489716867637)
              ·
                refine ⟨4488344898777139660956341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47875678920289489716867637 4488344898777139660956341)
                ·
                  refine ⟨420782334260356843214657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488344898777139660956341 420782334260356843214657)
                  ·
                    rfl

theorem cell23_7375236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_7375236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375236 prefixEnd_7375236 := by exact prefixLift 7375236
  have htrace : WordTrace (prefixWord ++ tailWord_7375236) baseStart_7375236 baseEnd_7375236 := by
    simpa [prefixWord, tailWord_7375236, baseEnd_7375236] using wordTrace_append hprefix tailTrace_7375236
  have hstable : (prefixWord ++ tailWord_7375236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375236).length < 2 ^ (prefixWord ++ tailWord_7375236).sum := by decide
  have hdescent : baseEnd_7375236 < baseStart_7375236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375269 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_7375269 : Nat := 118140960795 + 7375269 * 2 ^ 59
def prefixEnd_7375269 : Nat := 4983230072969 + 3 ^ 40 * 7375269 * 2
def baseEnd_7375269 : Nat := 3787057953204809959819261

theorem tailTrace_7375269 : CollatzResearch.WordTrace tailWord_7375269 prefixEnd_7375269 3787057953204809959819261 := by
  unfold tailWord_7375269
  simp only [CollatzResearch.WordTrace]
  refine ⟨268998159517667483508776861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179332106345111655672517907 268998159517667483508776861)
  ·
    refine ⟨100874309819125306315791323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268998159517667483508776861 100874309819125306315791323)
    ·
      refine ⟨151311464728687959473686985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100874309819125306315791323 151311464728687959473686985)
      ·
        refine ⟨113483598546515969605265239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151311464728687959473686985 113483598546515969605265239)
        ·
          refine ⟨170225397819773954407897859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113483598546515969605265239 170225397819773954407897859)
          ·
            refine ⟨255338096729660931611846789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170225397819773954407897859 255338096729660931611846789)
            ·
              refine ⟨47875893136811424677221273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255338096729660931611846789 47875893136811424677221273)
              ·
                refine ⟨35906919852608568507915955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47875893136811424677221273 35906919852608568507915955)
                ·
                  refine ⟨53860379778912852761873933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35906919852608568507915955 53860379778912852761873933)
                  ·
                    refine ⟨20197642417092319785702725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53860379778912852761873933 20197642417092319785702725)
                    ·
                      refine ⟨3787057953204809959819261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20197642417092319785702725 3787057953204809959819261)
                      ·
                        rfl

theorem cell23_7375269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_7375269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375269 prefixEnd_7375269 := by exact prefixLift 7375269
  have htrace : WordTrace (prefixWord ++ tailWord_7375269) baseStart_7375269 baseEnd_7375269 := by
    simpa [prefixWord, tailWord_7375269, baseEnd_7375269] using wordTrace_append hprefix tailTrace_7375269
  have hstable : (prefixWord ++ tailWord_7375269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375269).length < 2 ^ (prefixWord ++ tailWord_7375269).sum := by decide
  have hdescent : baseEnd_7375269 < baseStart_7375269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375306 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_7375306 : Nat := 118140960795 + 7375306 * 2 ^ 59
def prefixEnd_7375306 : Nat := 4983230072969 + 3 ^ 40 * 7375306 * 2
def baseEnd_7375306 : Nat := 3787076951989026315056591

theorem tailTrace_7375306 : CollatzResearch.WordTrace tailWord_7375306 prefixEnd_7375306 3787076951989026315056591 := by
  unfold tailWord_7375306
  simp only [CollatzResearch.WordTrace]
  refine ⟨67249877254633359706968443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179333006012355625885249181 67249877254633359706968443)
  ·
    refine ⟨100874815881950039560452665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67249877254633359706968443 100874815881950039560452665)
    ·
      refine ⟨75656111911462529670339499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100874815881950039560452665 75656111911462529670339499)
      ·
        refine ⟨113484167867193794505509249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75656111911462529670339499 113484167867193794505509249)
        ·
          refine ⟨85113125900395345879131937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113484167867193794505509249 85113125900395345879131937)
          ·
            refine ⟨63834844425296509409348953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85113125900395345879131937 63834844425296509409348953)
            ·
              refine ⟨47876133318972382057011715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63834844425296509409348953 47876133318972382057011715)
              ·
                refine ⟨71814199978458573085517573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47876133318972382057011715 71814199978458573085517573)
                ·
                  refine ⟨13465162495960982453534545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71814199978458573085517573 13465162495960982453534545)
                  ·
                    refine ⟨10098871871970736840150909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13465162495960982453534545 10098871871970736840150909)
                    ·
                      refine ⟨3787076951989026315056591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10098871871970736840150909 3787076951989026315056591)
                      ·
                        rfl

theorem cell23_7375306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_7375306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375306 prefixEnd_7375306 := by exact prefixLift 7375306
  have htrace : WordTrace (prefixWord ++ tailWord_7375306) baseStart_7375306 baseEnd_7375306 := by
    simpa [prefixWord, tailWord_7375306, baseEnd_7375306] using wordTrace_append hprefix tailTrace_7375306
  have hstable : (prefixWord ++ tailWord_7375306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375306).length < 2 ^ (prefixWord ++ tailWord_7375306).sum := by decide
  have hdescent : baseEnd_7375306 < baseStart_7375306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375329 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_7375329 : Nat := 118140960795 + 7375329 * 2 ^ 59
def prefixEnd_7375329 : Nat := 4983230072969 + 3 ^ 40 * 7375329 * 2
def baseEnd_7375329 : Nat := 3787088762044079725068985

theorem tailTrace_7375329 : CollatzResearch.WordTrace tailWord_7375329 prefixEnd_7375329 3787088762044079725068985 := by
  unfold tailWord_7375329
  simp only [CollatzResearch.WordTrace]
  refine ⟨269000347897450113755961041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179333565264966742503974027 269000347897450113755961041)
  ·
    refine ⟨201750260923087585316970781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269000347897450113755961041 201750260923087585316970781)
    ·
      refine ⟨75656347846157844493864043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201750260923087585316970781 75656347846157844493864043)
      ·
        refine ⟨113484521769236766740796065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75656347846157844493864043 113484521769236766740796065)
        ·
          refine ⟨85113391326927575055597049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113484521769236766740796065 85113391326927575055597049)
          ·
            refine ⟨63835043495195681291697787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85113391326927575055597049 63835043495195681291697787)
            ·
              refine ⟨95752565242793521937546681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63835043495195681291697787 95752565242793521937546681)
              ·
                refine ⟨71814423932095141453160011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95752565242793521937546681 71814423932095141453160011)
                ·
                  refine ⟨107721635898142712179740017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71814423932095141453160011 107721635898142712179740017)
                  ·
                    refine ⟨80791226923607034134805013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107721635898142712179740017 80791226923607034134805013)
                    ·
                      refine ⟨3787088762044079725068985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80791226923607034134805013 3787088762044079725068985)
                      ·
                        rfl

theorem cell23_7375329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_7375329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375329 prefixEnd_7375329 := by exact prefixLift 7375329
  have htrace : WordTrace (prefixWord ++ tailWord_7375329) baseStart_7375329 baseEnd_7375329 := by
    simpa [prefixWord, tailWord_7375329, baseEnd_7375329] using wordTrace_append hprefix tailTrace_7375329
  have hstable : (prefixWord ++ tailWord_7375329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375329).length < 2 ^ (prefixWord ++ tailWord_7375329).sum := by decide
  have hdescent : baseEnd_7375329 < baseStart_7375329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375363 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 2, 3, 2]
def baseStart_7375363 : Nat := 118140960795 + 7375363 * 2 ^ 59
def prefixEnd_7375363 : Nat := 4983230072969 + 3 ^ 40 * 7375363 * 2
def baseEnd_7375363 : Nat := 3787106220386332592043829

theorem tailTrace_7375363 : CollatzResearch.WordTrace tailWord_7375363 prefixEnd_7375363 3787106220386332592043829 := by
  unfold tailWord_7375363
  simp only [CollatzResearch.WordTrace]
  refine ⟨269001587979326937562698743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179334391986217958375132495 269001587979326937562698743)
  ·
    refine ⟨403502381968990406344048115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269001587979326937562698743 403502381968990406344048115)
    ·
      refine ⟨605253572953485609516072173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403502381968990406344048115 605253572953485609516072173)
      ·
        refine ⟨226970089857557103568527065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605253572953485609516072173 226970089857557103568527065)
        ·
          refine ⟨170227567393167827676395299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226970089857557103568527065 170227567393167827676395299)
          ·
            refine ⟨255341351089751741514592949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170227567393167827676395299 255341351089751741514592949)
            ·
              refine ⟨23938251664664225766993089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255341351089751741514592949 23938251664664225766993089)
              ·
                refine ⟨17953688748498169325244817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23938251664664225766993089 17953688748498169325244817)
                ·
                  refine ⟨13465266561373626993933613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17953688748498169325244817 13465266561373626993933613)
                  ·
                    refine ⟨5049474960515110122725105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13465266561373626993933613 5049474960515110122725105)
                    ·
                      refine ⟨3787106220386332592043829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049474960515110122725105 3787106220386332592043829)
                      ·
                        rfl

theorem cell23_7375363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_7375363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375363 prefixEnd_7375363 := by exact prefixLift 7375363
  have htrace : WordTrace (prefixWord ++ tailWord_7375363) baseStart_7375363 baseEnd_7375363 := by
    simpa [prefixWord, tailWord_7375363, baseEnd_7375363] using wordTrace_append hprefix tailTrace_7375363
  have hstable : (prefixWord ++ tailWord_7375363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375363).length < 2 ^ (prefixWord ++ tailWord_7375363).sum := by decide
  have hdescent : baseEnd_7375363 < baseStart_7375363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375369 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_7375369 : Nat := 118140960795 + 7375369 * 2 ^ 59
def prefixEnd_7375369 : Nat := 4983230072969 + 3 ^ 40 * 7375369 * 2
def baseEnd_7375369 : Nat := 1262369767090086522856267

theorem tailTrace_7375369 : CollatzResearch.WordTrace tailWord_7375369 prefixEnd_7375369 1262369767090086522856267 := by
  unfold tailWord_7375369
  simp only [CollatzResearch.WordTrace]
  refine ⟨269001806817305200587417161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179334537878203467058278107 269001806817305200587417161)
  ·
    refine ⟨201751355112978900440562871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269001806817305200587417161 201751355112978900440562871)
    ·
      refine ⟨302627032669468350660844307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201751355112978900440562871 302627032669468350660844307)
      ·
        refine ⟨453940549004202525991266461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302627032669468350660844307 453940549004202525991266461)
        ·
          refine ⟨170227705876575947246724923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453940549004202525991266461 170227705876575947246724923)
          ·
            refine ⟨255341558814863920870087385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170227705876575947246724923 255341558814863920870087385)
            ·
              refine ⟨191506169111147940652565539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255341558814863920870087385 191506169111147940652565539)
              ·
                refine ⟨287259253666721910978848309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191506169111147940652565539 287259253666721910978848309)
                ·
                  refine ⟨26930555031255179154267029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287259253666721910978848309 26930555031255179154267029)
                  ·
                    refine ⟨1262369767090086522856267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26930555031255179154267029 1262369767090086522856267)
                    ·
                      rfl

theorem cell23_7375369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_7375369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375369 prefixEnd_7375369 := by exact prefixLift 7375369
  have htrace : WordTrace (prefixWord ++ tailWord_7375369) baseStart_7375369 baseEnd_7375369 := by
    simpa [prefixWord, tailWord_7375369, baseEnd_7375369] using wordTrace_append hprefix tailTrace_7375369
  have hstable : (prefixWord ++ tailWord_7375369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375369).length < 2 ^ (prefixWord ++ tailWord_7375369).sum := by decide
  have hdescent : baseEnd_7375369 < baseStart_7375369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375376 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 8, 2]
def baseStart_7375376 : Nat := 118140960795 + 7375376 * 2 ^ 59
def prefixEnd_7375376 : Nat := 4983230072969 + 3 ^ 40 * 7375376 * 2
def baseEnd_7375376 : Nat := 3787112895634841041181269

theorem tailTrace_7375376 : CollatzResearch.WordTrace tailWord_7375376 prefixEnd_7375376 3787112895634841041181269 := by
  unfold tailWord_7375376
  simp only [CollatzResearch.WordTrace]
  refine ⟨134501031064139920391460991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179334708085519893855281321 134501031064139920391460991)
  ·
    refine ⟨201751546596209880587191487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134501031064139920391460991 201751546596209880587191487)
    ·
      refine ⟨302627319894314820880787231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201751546596209880587191487 302627319894314820880787231)
      ·
        refine ⟨453940979841472231321180847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302627319894314820880787231 453940979841472231321180847)
        ·
          refine ⟨680911469762208346981771271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453940979841472231321180847 680911469762208346981771271)
          ·
            refine ⟨1021367204643312520472656907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680911469762208346981771271 1021367204643312520472656907)
            ·
              refine ⟨1532050806964968780708985361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021367204643312520472656907 1532050806964968780708985361)
              ·
                refine ⟨1149038105223726585531739021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532050806964968780708985361 1149038105223726585531739021)
                ·
                  refine ⟨430889289458897469574402133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149038105223726585531739021 430889289458897469574402133)
                  ·
                    refine ⟨5049483860846454721575025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 430889289458897469574402133 5049483860846454721575025)
                    ·
                      refine ⟨3787112895634841041181269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049483860846454721575025 3787112895634841041181269)
                      ·
                        rfl

theorem cell23_7375376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 8, 2].length) (baseStart_7375376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375376 prefixEnd_7375376 := by exact prefixLift 7375376
  have htrace : WordTrace (prefixWord ++ tailWord_7375376) baseStart_7375376 baseEnd_7375376 := by
    simpa [prefixWord, tailWord_7375376, baseEnd_7375376] using wordTrace_append hprefix tailTrace_7375376
  have hstable : (prefixWord ++ tailWord_7375376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375376).length < 2 ^ (prefixWord ++ tailWord_7375376).sum := by decide
  have hdescent : baseEnd_7375376 < baseStart_7375376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375419 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_7375419 : Nat := 118140960795 + 7375419 * 2 ^ 59
def prefixEnd_7375419 : Nat := 4983230072969 + 3 ^ 40 * 7375419 * 2
def baseEnd_7375419 : Nat := 3787134975302984372943571

theorem tailTrace_7375419 : CollatzResearch.WordTrace tailWord_7375419 prefixEnd_7375419 3787134975302984372943571 := by
  unfold tailWord_7375419
  simp only [CollatzResearch.WordTrace]
  refine ⟨269003630467124059126737311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179335753644749372751158207 269003630467124059126737311)
  ·
    refine ⟨403505445700686088690105967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269003630467124059126737311 403505445700686088690105967)
    ·
      refine ⟨605258168551029133035158951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403505445700686088690105967 605258168551029133035158951)
      ·
        refine ⟨907887252826543699552738427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605258168551029133035158951 907887252826543699552738427)
        ·
          refine ⟨1361830879239815549329107641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907887252826543699552738427 1361830879239815549329107641)
          ·
            refine ⟨1021373159429861661996830731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361830879239815549329107641 1021373159429861661996830731)
            ·
              refine ⟨1532059739144792492995246097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021373159429861661996830731 1532059739144792492995246097)
              ·
                refine ⟨1149044804358594369746434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532059739144792492995246097 1149044804358594369746434573)
                ·
                  refine ⟨430891801634472888654912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149044804358594369746434573 430891801634472888654912965)
                  ·
                    refine ⟨80792212806463666622796181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430891801634472888654912965 80792212806463666622796181)
                    ·
                      refine ⟨3787134975302984372943571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80792212806463666622796181 3787134975302984372943571)
                      ·
                        rfl

theorem cell23_7375419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_7375419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375419 prefixEnd_7375419 := by exact prefixLift 7375419
  have htrace : WordTrace (prefixWord ++ tailWord_7375419) baseStart_7375419 baseEnd_7375419 := by
    simpa [prefixWord, tailWord_7375419, baseEnd_7375419] using wordTrace_append hprefix tailTrace_7375419
  have hstable : (prefixWord ++ tailWord_7375419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375419).length < 2 ^ (prefixWord ++ tailWord_7375419).sum := by decide
  have hdescent : baseEnd_7375419 < baseStart_7375419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375420 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_7375420 : Nat := 118140960795 + 7375420 * 2 ^ 59
def prefixEnd_7375420 : Nat := 4983230072969 + 3 ^ 40 * 7375420 * 2
def baseEnd_7375420 : Nat := 1262378496261212956343689

theorem tailTrace_7375420 : CollatzResearch.WordTrace tailWord_7375420 prefixEnd_7375420 1262378496261212956343689 := by
  unfold tailWord_7375420
  simp only [CollatzResearch.WordTrace]
  refine ⟨134501833470060218148761857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179335777960080290865015809 134501833470060218148761857)
  ·
    refine ⟨100876375102545163611571393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134501833470060218148761857 100876375102545163611571393)
    ·
      refine ⟨75657281326908872708678545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100876375102545163611571393 75657281326908872708678545)
      ·
        refine ⟨56742960995181654531508909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75657281326908872708678545 56742960995181654531508909)
        ·
          refine ⟨21278610373193120449315841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56742960995181654531508909 21278610373193120449315841)
          ·
            refine ⟨15958957779894840336986881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21278610373193120449315841 15958957779894840336986881)
            ·
              refine ⟨11969218334921130252740161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15958957779894840336986881 11969218334921130252740161)
              ·
                refine ⟨8976913751190847689555121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11969218334921130252740161 8976913751190847689555121)
                ·
                  refine ⟨6732685313393135767166341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8976913751190847689555121 6732685313393135767166341)
                  ·
                    refine ⟨1262378496261212956343689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6732685313393135767166341 1262378496261212956343689)
                    ·
                      rfl

theorem cell23_7375420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_7375420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375420 prefixEnd_7375420 := by exact prefixLift 7375420
  have htrace : WordTrace (prefixWord ++ tailWord_7375420) baseStart_7375420 baseEnd_7375420 := by
    simpa [prefixWord, tailWord_7375420, baseEnd_7375420] using wordTrace_append hprefix tailTrace_7375420
  have hstable : (prefixWord ++ tailWord_7375420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375420).length < 2 ^ (prefixWord ++ tailWord_7375420).sum := by decide
  have hdescent : baseEnd_7375420 < baseStart_7375420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375464 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7375464 : Nat := 118140960795 + 7375464 * 2 ^ 59
def prefixEnd_7375464 : Nat := 4983230072969 + 3 ^ 40 * 7375464 * 2
def baseEnd_7375464 : Nat := 3787158081932436696880865

theorem tailTrace_7375464 : CollatzResearch.WordTrace tailWord_7375464 prefixEnd_7375464 3787158081932436696880865 := by
  unfold tailWord_7375464
  simp only [CollatzResearch.WordTrace]
  refine ⟨134502635875980515906062723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179336847834640687874750297 134502635875980515906062723)
  ·
    refine ⟨201753953813970773859094085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134502635875980515906062723 201753953813970773859094085)
    ·
      refine ⟨37828866340119520098580141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201753953813970773859094085 37828866340119520098580141)
      ·
        refine ⟨14185824877544820036967553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37828866340119520098580141 14185824877544820036967553)
        ·
          refine ⟨10639368658158615027725665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14185824877544820036967553 10639368658158615027725665)
          ·
            refine ⟨7979526493618961270794249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10639368658158615027725665 7979526493618961270794249)
            ·
              refine ⟨5984644870214220953095687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7979526493618961270794249 5984644870214220953095687)
              ·
                refine ⟨8976967305321331429643531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984644870214220953095687 8976967305321331429643531)
                ·
                  refine ⟨13465450957981997144465297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8976967305321331429643531 13465450957981997144465297)
                  ·
                    refine ⟨10099088218486497858348973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13465450957981997144465297 10099088218486497858348973)
                    ·
                      refine ⟨3787158081932436696880865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099088218486497858348973 3787158081932436696880865)
                      ·
                        rfl

theorem cell23_7375464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7375464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375464 prefixEnd_7375464 := by exact prefixLift 7375464
  have htrace : WordTrace (prefixWord ++ tailWord_7375464) baseStart_7375464 baseEnd_7375464 := by
    simpa [prefixWord, tailWord_7375464, baseEnd_7375464] using wordTrace_append hprefix tailTrace_7375464
  have hstable : (prefixWord ++ tailWord_7375464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375464).length < 2 ^ (prefixWord ++ tailWord_7375464).sum := by decide
  have hdescent : baseEnd_7375464 < baseStart_7375464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375477 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7375477 : Nat := 118140960795 + 7375477 * 2 ^ 59
def prefixEnd_7375477 : Nat := 4983230072969 + 3 ^ 40 * 7375477 * 2
def baseEnd_7375477 : Nat := 3787164757180945146018305

theorem tailTrace_7375477 : CollatzResearch.WordTrace tailWord_7375477 prefixEnd_7375477 3787164757180945146018305 := by
  unfold tailWord_7375477
  simp only [CollatzResearch.WordTrace]
  refine ⟨269005745900913935032348685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179337163933942623354899123 269005745900913935032348685)
  ·
    refine ⟨100877154712842725637130757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269005745900913935032348685 100877154712842725637130757)
    ·
      refine ⟨18914466508658011056962017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100877154712842725637130757 18914466508658011056962017)
      ·
        refine ⟨14185849881493508292721513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18914466508658011056962017 14185849881493508292721513)
        ·
          refine ⟨10639387411120131219541135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14185849881493508292721513 10639387411120131219541135)
          ·
            refine ⟨15959081116680196829311703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10639387411120131219541135 15959081116680196829311703)
            ·
              refine ⟨23938621675020295243967555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15959081116680196829311703 23938621675020295243967555)
              ·
                refine ⟨35907932512530442865951333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23938621675020295243967555 35907932512530442865951333)
                ·
                  refine ⟨6732737346099458037365875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35907932512530442865951333 6732737346099458037365875)
                  ·
                    refine ⟨10099106019149187056048813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6732737346099458037365875 10099106019149187056048813)
                    ·
                      refine ⟨3787164757180945146018305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099106019149187056048813 3787164757180945146018305)
                      ·
                        rfl

theorem cell23_7375477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7375477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375477 prefixEnd_7375477 := by exact prefixLift 7375477
  have htrace : WordTrace (prefixWord ++ tailWord_7375477) baseStart_7375477 baseEnd_7375477 := by
    simpa [prefixWord, tailWord_7375477, baseEnd_7375477] using wordTrace_append hprefix tailTrace_7375477
  have hstable : (prefixWord ++ tailWord_7375477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375477).length < 2 ^ (prefixWord ++ tailWord_7375477).sum := by decide
  have hdescent : baseEnd_7375477 < baseStart_7375477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375523 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 5]
def baseStart_7375523 : Nat := 118140960795 + 7375523 * 2 ^ 59
def prefixEnd_7375523 : Nat := 4983230072969 + 3 ^ 40 * 7375523 * 2
def baseEnd_7375523 : Nat := 420798708587894662893677

theorem tailTrace_7375523 : CollatzResearch.WordTrace tailWord_7375523 prefixEnd_7375523 420798708587894662893677 := by
  unfold tailWord_7375523
  simp only [CollatzResearch.WordTrace]
  refine ⟨269007423658747284888523223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179338282439164856592348815 269007423658747284888523223)
  ·
    refine ⟨403511135488120927332784835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269007423658747284888523223 403511135488120927332784835)
    ·
      refine ⟨605266703232181390999177253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403511135488120927332784835 605266703232181390999177253)
      ·
        refine ⟨113487506856034010812345735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605266703232181390999177253 113487506856034010812345735)
        ·
          refine ⟨170231260284051016218518603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113487506856034010812345735 170231260284051016218518603)
          ·
            refine ⟨255346890426076524327777905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170231260284051016218518603 255346890426076524327777905)
            ·
              refine ⟨191510167819557393245833429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255346890426076524327777905 191510167819557393245833429)
              ·
                refine ⟨4488519558270876404199221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191510167819557393245833429 4488519558270876404199221)
                ·
                  refine ⟨420798708587894662893677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488519558270876404199221 420798708587894662893677)
                  ·
                    rfl

theorem cell23_7375523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 5].length) (baseStart_7375523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375523 prefixEnd_7375523 := by exact prefixLift 7375523
  have htrace : WordTrace (prefixWord ++ tailWord_7375523) baseStart_7375523 baseEnd_7375523 := by
    simpa [prefixWord, tailWord_7375523, baseEnd_7375523] using wordTrace_append hprefix tailTrace_7375523
  have hstable : (prefixWord ++ tailWord_7375523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375523).length < 2 ^ (prefixWord ++ tailWord_7375523).sum := by decide
  have hdescent : baseEnd_7375523 < baseStart_7375523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375534 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7375534 : Nat := 118140960795 + 7375534 * 2 ^ 59
def prefixEnd_7375534 : Nat := 4983230072969 + 3 ^ 40 * 7375534 * 2
def baseEnd_7375534 : Nat := 3787194025578251423005543

theorem tailTrace_7375534 : CollatzResearch.WordTrace tailWord_7375534 prefixEnd_7375534 3787194025578251423005543 := by
  unfold tailWord_7375534
  simp only [CollatzResearch.WordTrace]
  refine ⟨33625978107713429220896707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179338549907804955844782437 33625978107713429220896707)
  ·
    refine ⟨50438967161570143831345061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33625978107713429220896707 50438967161570143831345061)
    ·
      refine ⟨9457306342794401968377199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50438967161570143831345061 9457306342794401968377199)
      ·
        refine ⟨14185959514191602952565799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9457306342794401968377199 14185959514191602952565799)
        ·
          refine ⟨21278939271287404428848699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14185959514191602952565799 21278939271287404428848699)
          ·
            refine ⟨31918408906931106643273049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21278939271287404428848699 31918408906931106643273049)
            ·
              refine ⟨23938806680198329982454787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31918408906931106643273049 23938806680198329982454787)
              ·
                refine ⟨35908210020297494973682181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23938806680198329982454787 35908210020297494973682181)
                ·
                  refine ⟨6732789378805780307565409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35908210020297494973682181 6732789378805780307565409)
                  ·
                    refine ⟨5049592034104335230674057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6732789378805780307565409 5049592034104335230674057)
                    ·
                      refine ⟨3787194025578251423005543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049592034104335230674057 3787194025578251423005543)
                      ·
                        rfl

theorem cell23_7375534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7375534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375534 prefixEnd_7375534 := by exact prefixLift 7375534
  have htrace : WordTrace (prefixWord ++ tailWord_7375534) baseStart_7375534 baseEnd_7375534 := by
    simpa [prefixWord, tailWord_7375534, baseEnd_7375534] using wordTrace_append hprefix tailTrace_7375534
  have hstable : (prefixWord ++ tailWord_7375534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375534).length < 2 ^ (prefixWord ++ tailWord_7375534).sum := by decide
  have hdescent : baseEnd_7375534 < baseStart_7375534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375580 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7375580 : Nat := 118140960795 + 7375580 * 2 ^ 59
def prefixEnd_7375580 : Nat := 4983230072969 + 3 ^ 40 * 7375580 * 2
def baseEnd_7375580 : Nat := 3787217645688358243030331

theorem tailTrace_7375580 : CollatzResearch.WordTrace tailWord_7375580 prefixEnd_7375580 3787217645688358243030331 := by
  unfold tailWord_7375580
  simp only [CollatzResearch.WordTrace]
  refine ⟨134504751309770391811674097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179339668413027189082232129 134504751309770391811674097)
  ·
    refine ⟨100878563482327793858755573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134504751309770391811674097 100878563482327793858755573)
    ·
      refine ⟨9457365326468230674258335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100878563482327793858755573 9457365326468230674258335)
      ·
        refine ⟨14186047989702346011387503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9457365326468230674258335 14186047989702346011387503)
        ·
          refine ⟨21279071984553519017081255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186047989702346011387503 21279071984553519017081255)
          ·
            refine ⟨31918607976830278525621883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21279071984553519017081255 31918607976830278525621883)
            ·
              refine ⟨47877911965245417788432825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31918607976830278525621883 47877911965245417788432825)
              ·
                refine ⟨35908433973934063341324619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47877911965245417788432825 35908433973934063341324619)
                ·
                  refine ⟨53862650960901095011986929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35908433973934063341324619 53862650960901095011986929)
                  ·
                    refine ⟨40396988220675821258990197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53862650960901095011986929 40396988220675821258990197)
                    ·
                      refine ⟨3787217645688358243030331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40396988220675821258990197 3787217645688358243030331)
                      ·
                        rfl

theorem cell23_7375580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7375580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375580 prefixEnd_7375580 := by exact prefixLift 7375580
  have htrace : WordTrace (prefixWord ++ tailWord_7375580) baseStart_7375580 baseEnd_7375580 := by
    simpa [prefixWord, tailWord_7375580, baseEnd_7375580] using wordTrace_append hprefix tailTrace_7375580
  have hstable : (prefixWord ++ tailWord_7375580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375580).length < 2 ^ (prefixWord ++ tailWord_7375580).sum := by decide
  have hdescent : baseEnd_7375580 < baseStart_7375580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375613 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 6]
def baseStart_7375613 : Nat := 118140960795 + 7375613 * 2 ^ 59
def prefixEnd_7375613 : Nat := 4983230072969 + 3 ^ 40 * 7375613 * 2
def baseEnd_7375613 : Nat := 420803843394439623768631

theorem tailTrace_7375613 : CollatzResearch.WordTrace tailWord_7375613 prefixEnd_7375613 420803843394439623768631 := by
  unfold tailWord_7375613
  simp only [CollatzResearch.WordTrace]
  refine ⟨269010706228421230259299493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179340470818947486839532995 269010706228421230259299493)
  ·
    refine ⟨50439507417828980673618655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269010706228421230259299493 50439507417828980673618655)
    ·
      refine ⟨75659261126743471010427983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50439507417828980673618655 75659261126743471010427983)
      ·
        refine ⟨113488891690115206515641975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75659261126743471010427983 113488891690115206515641975)
        ·
          refine ⟨170233337535172809773462963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113488891690115206515641975 170233337535172809773462963)
          ·
            refine ⟨255350006302759214660194445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170233337535172809773462963 255350006302759214660194445)
            ·
              refine ⟨95756252363534705497572917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255350006302759214660194445 95756252363534705497572917)
              ·
                refine ⟨8977148659081378640397461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95756252363534705497572917 8977148659081378640397461)
                ·
                  refine ⟨420803843394439623768631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8977148659081378640397461 420803843394439623768631)
                  ·
                    rfl

theorem cell23_7375613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_7375613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375613 prefixEnd_7375613 := by exact prefixLift 7375613
  have htrace : WordTrace (prefixWord ++ tailWord_7375613) baseStart_7375613 baseEnd_7375613 := by
    simpa [prefixWord, tailWord_7375613, baseEnd_7375613] using wordTrace_append hprefix tailTrace_7375613
  have hstable : (prefixWord ++ tailWord_7375613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375613).length < 2 ^ (prefixWord ++ tailWord_7375613).sum := by decide
  have hdescent : baseEnd_7375613 < baseStart_7375613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375640 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_7375640 : Nat := 118140960795 + 7375640 * 2 ^ 59
def prefixEnd_7375640 : Nat := 4983230072969 + 3 ^ 40 * 7375640 * 2
def baseEnd_7375640 : Nat := 3787248454527628008280055

theorem tailTrace_7375640 : CollatzResearch.WordTrace tailWord_7375640 prefixEnd_7375640 3787248454527628008280055 := by
  unfold tailWord_7375640
  simp only [CollatzResearch.WordTrace]
  refine ⟨134505845499661706935266187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179341127332882275913688249 134505845499661706935266187)
  ·
    refine ⟨201758768249492560402899281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134505845499661706935266187 201758768249492560402899281)
    ·
      refine ⟨151319076187119420302174461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201758768249492560402899281 151319076187119420302174461)
      ·
        refine ⟨56744653570169782613315423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151319076187119420302174461 56744653570169782613315423)
        ·
          refine ⟨85116980355254673919973135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56744653570169782613315423 85116980355254673919973135)
          ·
            refine ⟨127675470532882010879959703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85116980355254673919973135 127675470532882010879959703)
            ·
              refine ⟨191513205799323016319939555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127675470532882010879959703 191513205799323016319939555)
              ·
                refine ⟨287269808698984524479909333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191513205799323016319939555 287269808698984524479909333)
                ·
                  refine ⟨6732886141382449792497875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 287269808698984524479909333 6732886141382449792497875)
                  ·
                    refine ⟨10099329212073674688746813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6732886141382449792497875 10099329212073674688746813)
                    ·
                      refine ⟨3787248454527628008280055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099329212073674688746813 3787248454527628008280055)
                      ·
                        rfl

theorem cell23_7375640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_7375640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375640 prefixEnd_7375640 := by exact prefixLift 7375640
  have htrace : WordTrace (prefixWord ++ tailWord_7375640) baseStart_7375640 baseEnd_7375640 := by
    simpa [prefixWord, tailWord_7375640, baseEnd_7375640] using wordTrace_append hprefix tailTrace_7375640
  have hstable : (prefixWord ++ tailWord_7375640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375640).length < 2 ^ (prefixWord ++ tailWord_7375640).sum := by decide
  have hdescent : baseEnd_7375640 < baseStart_7375640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375683 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5]
def baseStart_7375683 : Nat := 118140960795 + 7375683 * 2 ^ 59
def prefixEnd_7375683 : Nat := 4983230072969 + 3 ^ 40 * 7375683 * 2
def baseEnd_7375683 : Nat := 3787270534195771340042357

theorem tailTrace_7375683 : CollatzResearch.WordTrace tailWord_7375683 prefixEnd_7375683 3787270534195771340042357 := by
  unfold tailWord_7375683
  simp only [CollatzResearch.WordTrace]
  refine ⟨269013259338167632214347703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179342172892111754809565135 269013259338167632214347703)
  ·
    refine ⟨403519889007251448321521555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269013259338167632214347703 403519889007251448321521555)
    ·
      refine ⟨605279833510877172482282333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403519889007251448321521555 605279833510877172482282333)
      ·
        refine ⟨226979937566578939680855875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605279833510877172482282333 226979937566578939680855875)
        ·
          refine ⟨340469906349868409521283813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226979937566578939680855875 340469906349868409521283813)
          ·
            refine ⟨63838107440600326785240715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340469906349868409521283813 63838107440600326785240715)
            ·
              refine ⟨95757161160900490177861073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63838107440600326785240715 95757161160900490177861073)
              ·
                refine ⟨71817870870675367633395805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95757161160900490177861073 71817870870675367633395805)
                ·
                  refine ⟨26931701576503262862523427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71817870870675367633395805 26931701576503262862523427)
                  ·
                    refine ⟨40397552364754894293785141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26931701576503262862523427 40397552364754894293785141)
                    ·
                      refine ⟨3787270534195771340042357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40397552364754894293785141 3787270534195771340042357)
                      ·
                        rfl

theorem cell23_7375683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_7375683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375683 prefixEnd_7375683 := by exact prefixLift 7375683
  have htrace : WordTrace (prefixWord ++ tailWord_7375683) baseStart_7375683 baseEnd_7375683 := by
    simpa [prefixWord, tailWord_7375683, baseEnd_7375683] using wordTrace_append hprefix tailTrace_7375683
  have hstable : (prefixWord ++ tailWord_7375683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375683).length < 2 ^ (prefixWord ++ tailWord_7375683).sum := by decide
  have hdescent : baseEnd_7375683 < baseStart_7375683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375703 : List Nat := [1, 1, 3, 2, 4, 1, 11]
def baseStart_7375703 : Nat := 118140960795 + 7375703 * 2 ^ 59
def prefixEnd_7375703 : Nat := 4983230072969 + 3 ^ 40 * 7375703 * 2
def baseEnd_7375703 : Nat := 46756553133442731627065

theorem tailTrace_7375703 : CollatzResearch.WordTrace tailWord_7375703 prefixEnd_7375703 46756553133442731627065 := by
  unfold tailWord_7375703
  simp only [CollatzResearch.WordTrace]
  refine ⟨269013988798095175630075763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179342659198730117086717175 269013988798095175630075763)
  ·
    refine ⟨403520983197142763445113645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269013988798095175630075763 403520983197142763445113645)
    ·
      refine ⟨151320368698928536291917617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403520983197142763445113645 151320368698928536291917617)
      ·
        refine ⟨113490276524196402218938213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151320368698928536291917617 113490276524196402218938213)
        ·
          refine ⟨21279426848286825416050915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113490276524196402218938213 21279426848286825416050915)
          ·
            refine ⟨31919140272430238124076373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21279426848286825416050915 31919140272430238124076373)
            ·
              refine ⟨46756553133442731627065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31919140272430238124076373 46756553133442731627065)
              ·
                rfl

theorem cell23_7375703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 11].length) (baseStart_7375703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375703 prefixEnd_7375703 := by exact prefixLift 7375703
  have htrace : WordTrace (prefixWord ++ tailWord_7375703) baseStart_7375703 baseEnd_7375703 := by
    simpa [prefixWord, tailWord_7375703, baseEnd_7375703] using wordTrace_append hprefix tailTrace_7375703
  have hstable : (prefixWord ++ tailWord_7375703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375703).length < 2 ^ (prefixWord ++ tailWord_7375703).sum := by decide
  have hdescent : baseEnd_7375703 < baseStart_7375703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375708 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7375708 : Nat := 118140960795 + 7375708 * 2 ^ 59
def prefixEnd_7375708 : Nat := 4983230072969 + 3 ^ 40 * 7375708 * 2
def baseEnd_7375708 : Nat := 3787283371212133742229743

theorem tailTrace_7375708 : CollatzResearch.WordTrace tailWord_7375708 prefixEnd_7375708 3787283371212133742229743 := by
  unfold tailWord_7375708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134507085581538530742003889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179342780775384707656005185 134507085581538530742003889)
  ·
    refine ⟨100880314186153898056502917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134507085581538530742003889 100880314186153898056502917)
    ·
      refine ⟨18915058909903855885594297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100880314186153898056502917 18915058909903855885594297)
      ·
        refine ⟨14186294182427891914195723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18915058909903855885594297 14186294182427891914195723)
        ·
          refine ⟨21279441273641837871293585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186294182427891914195723 21279441273641837871293585)
          ·
            refine ⟨15959580955231378403470189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21279441273641837871293585 15959580955231378403470189)
            ·
              refine ⟨5984842858211766901301321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15959580955231378403470189 5984842858211766901301321)
              ·
                refine ⟨4488632143658825175975991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5984842858211766901301321 4488632143658825175975991)
                ·
                  refine ⟨6732948215488237763963987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488632143658825175975991 6732948215488237763963987)
                  ·
                    refine ⟨10099422323232356645945981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6732948215488237763963987 10099422323232356645945981)
                    ·
                      refine ⟨3787283371212133742229743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099422323232356645945981 3787283371212133742229743)
                      ·
                        rfl

theorem cell23_7375708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7375708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375708 prefixEnd_7375708 := by exact prefixLift 7375708
  have htrace : WordTrace (prefixWord ++ tailWord_7375708) baseStart_7375708 baseEnd_7375708 := by
    simpa [prefixWord, tailWord_7375708, baseEnd_7375708] using wordTrace_append hprefix tailTrace_7375708
  have hstable : (prefixWord ++ tailWord_7375708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375708).length < 2 ^ (prefixWord ++ tailWord_7375708).sum := by decide
  have hdescent : baseEnd_7375708 < baseStart_7375708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375720 : List Nat := [2, 1, 4, 2, 1, 3, 2, 8]
def baseStart_7375720 : Nat := 118140960795 + 7375720 * 2 ^ 59
def prefixEnd_7375720 : Nat := 4983230072969 + 3 ^ 40 * 7375720 * 2
def baseEnd_7375720 : Nat := 140269982702962507232581

theorem tailTrace_7375720 : CollatzResearch.WordTrace tailWord_7375720 prefixEnd_7375720 140269982702962507232581 := by
  unfold tailWord_7375720
  simp only [CollatzResearch.WordTrace]
  refine ⟨134507304419516793766722307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179343072559355725022296409 134507304419516793766722307)
  ·
    refine ⟨201760956629275190650083461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134507304419516793766722307 201760956629275190650083461)
    ·
      refine ⟨37830179367989098246890649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201760956629275190650083461 37830179367989098246890649)
      ·
        refine ⟨28372634525991823685167987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37830179367989098246890649 28372634525991823685167987)
        ·
          refine ⟨42558951788987735527751981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28372634525991823685167987 42558951788987735527751981)
          ·
            refine ⟨15959606920870400822906993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42558951788987735527751981 15959606920870400822906993)
            ·
              refine ⟨11969705190652800617180245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15959606920870400822906993 11969705190652800617180245)
              ·
                refine ⟨140269982702962507232581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11969705190652800617180245 140269982702962507232581)
                ·
                  rfl

theorem cell23_7375720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 8].length) (baseStart_7375720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375720 prefixEnd_7375720 := by exact prefixLift 7375720
  have htrace : WordTrace (prefixWord ++ tailWord_7375720) baseStart_7375720 baseEnd_7375720 := by
    simpa [prefixWord, tailWord_7375720, baseEnd_7375720] using wordTrace_append hprefix tailTrace_7375720
  have hstable : (prefixWord ++ tailWord_7375720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375720).length < 2 ^ (prefixWord ++ tailWord_7375720).sum := by decide
  have hdescent : baseEnd_7375720 < baseStart_7375720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375734 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7375734 : Nat := 118140960795 + 7375734 * 2 ^ 59
def prefixEnd_7375734 : Nat := 4983230072969 + 3 ^ 40 * 7375734 * 2
def baseEnd_7375734 : Nat := 3787296721709150640504623

theorem tailTrace_7375734 : CollatzResearch.WordTrace tailWord_7375734 prefixEnd_7375734 3787296721709150640504623 := by
  unfold tailWord_7375734
  simp only [CollatzResearch.WordTrace]
  refine ⟨16813444966311429245278391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179343412973988578616302837 16813444966311429245278391)
  ·
    refine ⟨25220167449467143867917587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16813444966311429245278391 25220167449467143867917587)
    ·
      refine ⟨37830251174200715801876381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25220167449467143867917587 37830251174200715801876381)
      ·
        refine ⟨14186344190325268425703643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37830251174200715801876381 14186344190325268425703643)
        ·
          refine ⟨21279516285487902638555465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186344190325268425703643 21279516285487902638555465)
          ·
            refine ⟨15959637214115926978916599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21279516285487902638555465 15959637214115926978916599)
            ·
              refine ⟨23939455821173890468374899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15959637214115926978916599 23939455821173890468374899)
              ·
                refine ⟨35909183731760835702562349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23939455821173890468374899 35909183731760835702562349)
                ·
                  refine ⟨13465943899410313388460881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35909183731760835702562349 13465943899410313388460881)
                  ·
                    refine ⟨10099457924557735041345661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13465943899410313388460881 10099457924557735041345661)
                    ·
                      refine ⟨3787296721709150640504623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099457924557735041345661 3787296721709150640504623)
                      ·
                        rfl

theorem cell23_7375734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7375734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375734 prefixEnd_7375734 := by exact prefixLift 7375734
  have htrace : WordTrace (prefixWord ++ tailWord_7375734) baseStart_7375734 baseEnd_7375734 := by
    simpa [prefixWord, tailWord_7375734, baseEnd_7375734] using wordTrace_append hprefix tailTrace_7375734
  have hstable : (prefixWord ++ tailWord_7375734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375734).length < 2 ^ (prefixWord ++ tailWord_7375734).sum := by decide
  have hdescent : baseEnd_7375734 < baseStart_7375734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375743 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_7375743 : Nat := 118140960795 + 7375743 * 2 ^ 59
def prefixEnd_7375743 : Nat := 4983230072969 + 3 ^ 40 * 7375743 * 2
def baseEnd_7375743 : Nat := 3787301343035041105292081

theorem tailTrace_7375743 : CollatzResearch.WordTrace tailWord_7375743 prefixEnd_7375743 3787301343035041105292081 := by
  unfold tailWord_7375743
  simp only [CollatzResearch.WordTrace]
  refine ⟨269015447717950262461531883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179343631811966841641021255 269015447717950262461531883)
  ·
    refine ⟨403523171576925393692297825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269015447717950262461531883 403523171576925393692297825)
    ·
      refine ⟨302642378682694045269223369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403523171576925393692297825 302642378682694045269223369)
      ·
        refine ⟨226981784012020533951917527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302642378682694045269223369 226981784012020533951917527)
        ·
          refine ⟨340472676018030800927876291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226981784012020533951917527 340472676018030800927876291)
          ·
            refine ⟨510709014027046201391814437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340472676018030800927876291 510709014027046201391814437)
            ·
              refine ⟨95757940130071162760965207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510709014027046201391814437 95757940130071162760965207)
              ·
                refine ⟨143636910195106744141447811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95757940130071162760965207 143636910195106744141447811)
                ·
                  refine ⟨215455365292660116212171717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143636910195106744141447811 215455365292660116212171717)
                  ·
                    refine ⟨40397880992373771789782197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215455365292660116212171717 40397880992373771789782197)
                    ·
                      refine ⟨3787301343035041105292081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40397880992373771789782197 3787301343035041105292081)
                      ·
                        rfl

theorem cell23_7375743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_7375743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375743 prefixEnd_7375743 := by exact prefixLift 7375743
  have htrace : WordTrace (prefixWord ++ tailWord_7375743) baseStart_7375743 baseEnd_7375743 := by
    simpa [prefixWord, tailWord_7375743, baseEnd_7375743] using wordTrace_append hprefix tailTrace_7375743
  have hstable : (prefixWord ++ tailWord_7375743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375743).length < 2 ^ (prefixWord ++ tailWord_7375743).sum := by decide
  have hdescent : baseEnd_7375743 < baseStart_7375743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375780 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_7375780 : Nat := 118140960795 + 7375780 * 2 ^ 59
def prefixEnd_7375780 : Nat := 4983230072969 + 3 ^ 40 * 7375780 * 2
def baseEnd_7375780 : Nat := 1262440113939752486843137

theorem tailTrace_7375780 : CollatzResearch.WordTrace tailWord_7375780 prefixEnd_7375780 1262440113939752486843137 := by
  unfold tailWord_7375780
  simp only [CollatzResearch.WordTrace]
  refine ⟨134508398609408108890314397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179344531479210811853752529 134508398609408108890314397)
  ·
    refine ⟨50440649478528040833867899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134508398609408108890314397 50440649478528040833867899)
    ·
      refine ⟨75660974217792061250801849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50440649478528040833867899 75660974217792061250801849)
      ·
        refine ⟨56745730663344045938101387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75660974217792061250801849 56745730663344045938101387)
        ·
          refine ⟨85118595995016068907152081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56745730663344045938101387 85118595995016068907152081)
          ·
            refine ⟨63838946996262051680364061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85118595995016068907152081 63838946996262051680364061)
            ·
              refine ⟨23939605123598269380136523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63838946996262051680364061 23939605123598269380136523)
              ·
                refine ⟨35909407685397404070204785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23939605123598269380136523 35909407685397404070204785)
                ·
                  refine ⟨26932055764048053052653589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35909407685397404070204785 26932055764048053052653589)
                  ·
                    refine ⟨1262440113939752486843137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26932055764048053052653589 1262440113939752486843137)
                    ·
                      rfl

theorem cell23_7375780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_7375780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375780 prefixEnd_7375780 := by exact prefixLift 7375780
  have htrace : WordTrace (prefixWord ++ tailWord_7375780) baseStart_7375780 baseEnd_7375780 := by
    simpa [prefixWord, tailWord_7375780, baseEnd_7375780] using wordTrace_append hprefix tailTrace_7375780
  have hstable : (prefixWord ++ tailWord_7375780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375780).length < 2 ^ (prefixWord ++ tailWord_7375780).sum := by decide
  have hdescent : baseEnd_7375780 < baseStart_7375780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375877 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_7375877 : Nat := 118140960795 + 7375877 * 2 ^ 59
def prefixEnd_7375877 : Nat := 4983230072969 + 3 ^ 40 * 7375877 * 2
def baseEnd_7375877 : Nat := 3787370149442743581016465

theorem tailTrace_7375877 : CollatzResearch.WordTrace tailWord_7375877 prefixEnd_7375877 3787370149442743581016465 := by
  unfold tailWord_7375877
  simp only [CollatzResearch.WordTrace]
  refine ⟨269020335099464803346909885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179346890066309868897939923 269020335099464803346909885)
  ·
    refine ⟨100882625662299301255091207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269020335099464803346909885 100882625662299301255091207)
    ·
      refine ⟨151323938493448951882636811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100882625662299301255091207 151323938493448951882636811)
      ·
        refine ⟨226985907740173427823955217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151323938493448951882636811 226985907740173427823955217)
        ·
          refine ⟨170239430805130070867966413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226985907740173427823955217 170239430805130070867966413)
          ·
            refine ⟨63839786551923776575487405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170239430805130070867966413 63839786551923776575487405)
            ·
              refine ⟨23939919956971416215807777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63839786551923776575487405 23939919956971416215807777)
              ·
                refine ⟨17954939967728562161855833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23939919956971416215807777 17954939967728562161855833)
                ·
                  refine ⟨13466204975796421621391875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17954939967728562161855833 13466204975796421621391875)
                  ·
                    refine ⟨20199307463694632432087813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13466204975796421621391875 20199307463694632432087813)
                    ·
                      refine ⟨3787370149442743581016465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20199307463694632432087813 3787370149442743581016465)
                      ·
                        rfl

theorem cell23_7375877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_7375877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375877 prefixEnd_7375877 := by exact prefixLift 7375877
  have htrace : WordTrace (prefixWord ++ tailWord_7375877) baseStart_7375877 baseEnd_7375877 := by
    simpa [prefixWord, tailWord_7375877, baseEnd_7375877] using wordTrace_append hprefix tailTrace_7375877
  have hstable : (prefixWord ++ tailWord_7375877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375877).length < 2 ^ (prefixWord ++ tailWord_7375877).sum := by decide
  have hdescent : baseEnd_7375877 < baseStart_7375877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375911 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7375911 : Nat := 118140960795 + 7375911 * 2 ^ 59
def prefixEnd_7375911 : Nat := 4983230072969 + 3 ^ 40 * 7375911 * 2
def baseEnd_7375911 : Nat := 3787387607784996447991309

theorem tailTrace_7375911 : CollatzResearch.WordTrace tailWord_7375911 prefixEnd_7375911 3787387607784996447991309 := by
  unfold tailWord_7375911
  simp only [CollatzResearch.WordTrace]
  refine ⟨269021575181341627153647587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179347716787561084769098391 269021575181341627153647587)
  ·
    refine ⟨403532362772012440730471381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269021575181341627153647587 403532362772012440730471381)
    ·
      refine ⟨9457789752469041579620423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 403532362772012440730471381 9457789752469041579620423)
      ·
        refine ⟨14186684628703562369430635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9457789752469041579620423 14186684628703562369430635)
        ·
          refine ⟨21280026943055343554145953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186684628703562369430635 21280026943055343554145953)
          ·
            refine ⟨15960020207291507665609465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21280026943055343554145953 15960020207291507665609465)
            ·
              refine ⟨11970015155468630749207099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15960020207291507665609465 11970015155468630749207099)
              ·
                refine ⟨17955022733202946123810649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11970015155468630749207099 17955022733202946123810649)
                ·
                  refine ⟨13466267049902209592857987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17955022733202946123810649 13466267049902209592857987)
                  ·
                    refine ⟨20199400574853314389286981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13466267049902209592857987 20199400574853314389286981)
                    ·
                      refine ⟨3787387607784996447991309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20199400574853314389286981 3787387607784996447991309)
                      ·
                        rfl

theorem cell23_7375911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7375911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375911 prefixEnd_7375911 := by exact prefixLift 7375911
  have htrace : WordTrace (prefixWord ++ tailWord_7375911) baseStart_7375911 baseEnd_7375911 := by
    simpa [prefixWord, tailWord_7375911, baseEnd_7375911] using wordTrace_append hprefix tailTrace_7375911
  have hstable : (prefixWord ++ tailWord_7375911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375911).length < 2 ^ (prefixWord ++ tailWord_7375911).sum := by decide
  have hdescent : baseEnd_7375911 < baseStart_7375911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375934 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_7375934 : Nat := 118140960795 + 7375934 * 2 ^ 59
def prefixEnd_7375934 : Nat := 4983230072969 + 3 ^ 40 * 7375934 * 2
def baseEnd_7375934 : Nat := 420822157537783317555967

theorem tailTrace_7375934 : CollatzResearch.WordTrace tailWord_7375934 prefixEnd_7375934 420822157537783317555967 := by
  unfold tailWord_7375934
  simp only [CollatzResearch.WordTrace]
  refine ⟨33627801757532287760216857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179348276040172201387823237 33627801757532287760216857)
  ·
    refine ⟨25220851318149215820162643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33627801757532287760216857 25220851318149215820162643)
    ·
      refine ⟨37831276977223823730243965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25220851318149215820162643 37831276977223823730243965)
      ·
        refine ⟨14186728866458933898841487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37831276977223823730243965 14186728866458933898841487)
        ·
          refine ⟨21280093299688400848262231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186728866458933898841487 21280093299688400848262231)
          ·
            refine ⟨31920139949532601272393347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21280093299688400848262231 31920139949532601272393347)
            ·
              refine ⟨47880209924298901908590021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31920139949532601272393347 47880209924298901908590021)
              ·
                refine ⟨8977539360806044107860629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47880209924298901908590021 8977539360806044107860629)
                ·
                  refine ⟨420822157537783317555967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8977539360806044107860629 420822157537783317555967)
                  ·
                    rfl

theorem cell23_7375934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_7375934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375934 prefixEnd_7375934 := by exact prefixLift 7375934
  have htrace : WordTrace (prefixWord ++ tailWord_7375934) baseStart_7375934 baseEnd_7375934 := by
    simpa [prefixWord, tailWord_7375934, baseEnd_7375934] using wordTrace_append hprefix tailTrace_7375934
  have hstable : (prefixWord ++ tailWord_7375934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375934).length < 2 ^ (prefixWord ++ tailWord_7375934).sum := by decide
  have hdescent : baseEnd_7375934 < baseStart_7375934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375944 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_7375944 : Nat := 118140960795 + 7375944 * 2 ^ 59
def prefixEnd_7375944 : Nat := 4983230072969 + 3 ^ 40 * 7375944 * 2
def baseEnd_7375944 : Nat := 3787404552646594818878657

theorem tailTrace_7375944 : CollatzResearch.WordTrace tailWord_7375944 prefixEnd_7375944 3787404552646594818878657 := by
  unfold tailWord_7375944
  simp only [CollatzResearch.WordTrace]
  refine ⟨134511389395111036894799443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179348519193481382526399257 134511389395111036894799443)
  ·
    refine ⟨201767084092666555342199165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134511389395111036894799443 201767084092666555342199165)
    ·
      refine ⟨75662656534749958253324687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201767084092666555342199165 75662656534749958253324687)
      ·
        refine ⟨113493984802124937379987031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75662656534749958253324687 113493984802124937379987031)
        ·
          refine ⟨170240977203187406069980547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113493984802124937379987031 170240977203187406069980547)
          ·
            refine ⟨255361465804781109104970821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170240977203187406069980547 255361465804781109104970821)
            ·
              refine ⟨47880274838396457957182029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255361465804781109104970821 47880274838396457957182029)
              ·
                refine ⟨17955103064398671733943261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47880274838396457957182029 17955103064398671733943261)
                ·
                  refine ⟨6733163649149501900228723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17955103064398671733943261 6733163649149501900228723)
                  ·
                    refine ⟨10099745473724252850343085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6733163649149501900228723 10099745473724252850343085)
                    ·
                      refine ⟨3787404552646594818878657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099745473724252850343085 3787404552646594818878657)
                      ·
                        rfl

theorem cell23_7375944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_7375944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375944 prefixEnd_7375944 := by exact prefixLift 7375944
  have htrace : WordTrace (prefixWord ++ tailWord_7375944) baseStart_7375944 baseEnd_7375944 := by
    simpa [prefixWord, tailWord_7375944, baseEnd_7375944] using wordTrace_append hprefix tailTrace_7375944
  have hstable : (prefixWord ++ tailWord_7375944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375944).length < 2 ^ (prefixWord ++ tailWord_7375944).sum := by decide
  have hdescent : baseEnd_7375944 < baseStart_7375944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375964 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_7375964 : Nat := 118140960795 + 7375964 * 2 ^ 59
def prefixEnd_7375964 : Nat := 4983230072969 + 3 ^ 40 * 7375964 * 2
def baseEnd_7375964 : Nat := 1262471607419894913542855

theorem tailTrace_7375964 : CollatzResearch.WordTrace tailWord_7375964 prefixEnd_7375964 1262471607419894913542855 := by
  unfold tailWord_7375964
  simp only [CollatzResearch.WordTrace]
  refine ⟨134511754125074808602663473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179349005500099744803551297 134511754125074808602663473)
  ·
    refine ⟨100883815593806106451997605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134511754125074808602663473 100883815593806106451997605)
    ·
      refine ⟨18915715423838644959749551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100883815593806106451997605 18915715423838644959749551)
      ·
        refine ⟨28373573135757967439624327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18915715423838644959749551 28373573135757967439624327)
        ·
          refine ⟨42560359703636951159436491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28373573135757967439624327 42560359703636951159436491)
          ·
            refine ⟨63840539555455426739154737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42560359703636951159436491 63840539555455426739154737)
            ·
              refine ⟨47880404666591570054366053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63840539555455426739154737 47880404666591570054366053)
              ·
                refine ⟨8977575874985919385193635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47880404666591570054366053 8977575874985919385193635)
                ·
                  refine ⟨13466363812478879077790453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977575874985919385193635 13466363812478879077790453)
                  ·
                    refine ⟨1262471607419894913542855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13466363812478879077790453 1262471607419894913542855)
                    ·
                      rfl

theorem cell23_7375964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_7375964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375964 prefixEnd_7375964 := by exact prefixLift 7375964
  have htrace : WordTrace (prefixWord ++ tailWord_7375964) baseStart_7375964 baseEnd_7375964 := by
    simpa [prefixWord, tailWord_7375964, baseEnd_7375964] using wordTrace_append hprefix tailTrace_7375964
  have hstable : (prefixWord ++ tailWord_7375964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375964).length < 2 ^ (prefixWord ++ tailWord_7375964).sum := by decide
  have hdescent : baseEnd_7375964 < baseStart_7375964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375965 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7375965 : Nat := 118140960795 + 7375965 * 2 ^ 59
def prefixEnd_7375965 : Nat := 4983230072969 + 3 ^ 40 * 7375965 * 2
def baseEnd_7375965 : Nat := 3787415335740339236716061

theorem tailTrace_7375965 : CollatzResearch.WordTrace tailWord_7375965 prefixEnd_7375965 3787415335740339236716061 := by
  unfold tailWord_7375965
  simp only [CollatzResearch.WordTrace]
  refine ⟨269023544723145994376113349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179349029815430662917408899 269023544723145994376113349)
  ·
    refine ⟨50441914635589873945521253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269023544723145994376113349 50441914635589873945521253)
    ·
      refine ⟨9457858994173101364785235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50441914635589873945521253 9457858994173101364785235)
      ·
        refine ⟨14186788491259652047177853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9457858994173101364785235 14186788491259652047177853)
        ·
          refine ⟨5320045684222369517691695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14186788491259652047177853 5320045684222369517691695)
          ·
            refine ⟨7980068526333554276537543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320045684222369517691695 7980068526333554276537543)
            ·
              refine ⟨11970102789500331414806315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980068526333554276537543 11970102789500331414806315)
              ·
                refine ⟨17955154184250497122209473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11970102789500331414806315 17955154184250497122209473)
                ·
                  refine ⟨13466365638187872841657105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17955154184250497122209473 13466365638187872841657105)
                  ·
                    refine ⟨10099774228640904631242829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13466365638187872841657105 10099774228640904631242829)
                    ·
                      refine ⟨3787415335740339236716061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099774228640904631242829 3787415335740339236716061)
                      ·
                        rfl

theorem cell23_7375965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7375965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375965 prefixEnd_7375965 := by exact prefixLift 7375965
  have htrace : WordTrace (prefixWord ++ tailWord_7375965) baseStart_7375965 baseEnd_7375965 := by
    simpa [prefixWord, tailWord_7375965, baseEnd_7375965] using wordTrace_append hprefix tailTrace_7375965
  have hstable : (prefixWord ++ tailWord_7375965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375965).length < 2 ^ (prefixWord ++ tailWord_7375965).sum := by decide
  have hdescent : baseEnd_7375965 < baseStart_7375965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375967 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_7375967 : Nat := 118140960795 + 7375967 * 2 ^ 59
def prefixEnd_7375967 : Nat := 4983230072969 + 3 ^ 40 * 7375967 * 2
def baseEnd_7375967 : Nat := 3787416362701648228891051

theorem tailTrace_7375967 : CollatzResearch.WordTrace tailWord_7375967 prefixEnd_7375967 3787416362701648228891051 := by
  unfold tailWord_7375967
  simp only [CollatzResearch.WordTrace]
  refine ⟨269023617669138748717686155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179349078446092499145124103 269023617669138748717686155)
  ·
    refine ⟨403535426503708123076529233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269023617669138748717686155 403535426503708123076529233)
    ·
      refine ⟨302651569877781092307396925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403535426503708123076529233 302651569877781092307396925)
      ·
        refine ⟨113494338704167909615273847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302651569877781092307396925 113494338704167909615273847)
        ·
          refine ⟨170241508056251864422910771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113494338704167909615273847 170241508056251864422910771)
          ·
            refine ⟨255362262084377796634366157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170241508056251864422910771 255362262084377796634366157)
            ·
              refine ⟨95760848281641673737887309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255362262084377796634366157 95760848281641673737887309)
              ·
                refine ⟨35910318105615627651707741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95760848281641673737887309 35910318105615627651707741)
                ·
                  refine ⟨13466369289605860369390403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35910318105615627651707741 13466369289605860369390403)
                  ·
                    refine ⟨20199553934408790554085605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13466369289605860369390403 20199553934408790554085605)
                    ·
                      refine ⟨3787416362701648228891051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20199553934408790554085605 3787416362701648228891051)
                      ·
                        rfl

theorem cell23_7375967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_7375967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375967 prefixEnd_7375967 := by exact prefixLift 7375967
  have htrace : WordTrace (prefixWord ++ tailWord_7375967) baseStart_7375967 baseEnd_7375967 := by
    simpa [prefixWord, tailWord_7375967, baseEnd_7375967] using wordTrace_append hprefix tailTrace_7375967
  have hstable : (prefixWord ++ tailWord_7375967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375967).length < 2 ^ (prefixWord ++ tailWord_7375967).sum := by decide
  have hdescent : baseEnd_7375967 < baseStart_7375967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375977 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_7375977 : Nat := 118140960795 + 7375977 * 2 ^ 59
def prefixEnd_7375977 : Nat := 4983230072969 + 3 ^ 40 * 7375977 * 2
def baseEnd_7375977 : Nat := 1262473832502731063255335

theorem tailTrace_7375977 : CollatzResearch.WordTrace tailWord_7375977 prefixEnd_7375977 1262473832502731063255335 := by
  unfold tailWord_7375977
  simp only [CollatzResearch.WordTrace]
  refine ⟨269023982399102520425550185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179349321599401680283700123 269023982399102520425550185)
  ·
    refine ⟨201767986799326890319162639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269023982399102520425550185 201767986799326890319162639)
    ·
      refine ⟨302651980198990335478743959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201767986799326890319162639 302651980198990335478743959)
      ·
        refine ⟨453977970298485503218115939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302651980198990335478743959 453977970298485503218115939)
        ·
          refine ⟨680966955447728254827173909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453977970298485503218115939 680966955447728254827173909)
          ·
            refine ⟨31920326036612261945023777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 680966955447728254827173909 31920326036612261945023777)
            ·
              refine ⟨23940244527459196458767833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31920326036612261945023777 23940244527459196458767833)
              ·
                refine ⟨17955183395594397344075875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23940244527459196458767833 17955183395594397344075875)
                ·
                  refine ⟨26932775093391596016113813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17955183395594397344075875 26932775093391596016113813)
                  ·
                    refine ⟨1262473832502731063255335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26932775093391596016113813 1262473832502731063255335)
                    ·
                      rfl

theorem cell23_7375977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_7375977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375977 prefixEnd_7375977 := by exact prefixLift 7375977
  have htrace : WordTrace (prefixWord ++ tailWord_7375977) baseStart_7375977 baseEnd_7375977 := by
    simpa [prefixWord, tailWord_7375977, baseEnd_7375977] using wordTrace_append hprefix tailTrace_7375977
  have hstable : (prefixWord ++ tailWord_7375977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375977).length < 2 ^ (prefixWord ++ tailWord_7375977).sum := by decide
  have hdescent : baseEnd_7375977 < baseStart_7375977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375978 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_7375978 : Nat := 118140960795 + 7375978 * 2 ^ 59
def prefixEnd_7375978 : Nat := 4983230072969 + 3 ^ 40 * 7375978 * 2
def baseEnd_7375978 : Nat := 3787422010988847685853501

theorem tailTrace_7375978 : CollatzResearch.WordTrace tailWord_7375978 prefixEnd_7375978 3787422010988847685853501 := by
  unfold tailWord_7375978
  simp only [CollatzResearch.WordTrace]
  refine ⟨67256004718024724399084147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179349345914732598397557725 67256004718024724399084147)
  ·
    refine ⟨100884007077037086598626221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67256004718024724399084147 100884007077037086598626221)
    ·
      refine ⟨37831502653888907474484833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100884007077037086598626221 37831502653888907474484833)
      ·
        refine ⟨28373626990416680605863625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37831502653888907474484833 28373626990416680605863625)
        ·
          refine ⟨21280220242812510454397719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28373626990416680605863625 21280220242812510454397719)
          ·
            refine ⟨31920330364218765681596579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21280220242812510454397719 31920330364218765681596579)
            ·
              refine ⟨47880495546328148522394869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31920330364218765681596579 47880495546328148522394869)
              ·
                refine ⟨4488796457468263923974519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47880495546328148522394869 4488796457468263923974519)
                ·
                  refine ⟨6733194686202395885961779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488796457468263923974519 6733194686202395885961779)
                  ·
                    refine ⟨10099792029303593828942669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6733194686202395885961779 10099792029303593828942669)
                    ·
                      refine ⟨3787422010988847685853501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10099792029303593828942669 3787422010988847685853501)
                      ·
                        rfl

theorem cell23_7375978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_7375978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375978 prefixEnd_7375978 := by exact prefixLift 7375978
  have htrace : WordTrace (prefixWord ++ tailWord_7375978) baseStart_7375978 baseEnd_7375978 := by
    simpa [prefixWord, tailWord_7375978, baseEnd_7375978] using wordTrace_append hprefix tailTrace_7375978
  have hstable : (prefixWord ++ tailWord_7375978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375978).length < 2 ^ (prefixWord ++ tailWord_7375978).sum := by decide
  have hdescent : baseEnd_7375978 < baseStart_7375978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375981 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_7375981 : Nat := 118140960795 + 7375981 * 2 ^ 59
def prefixEnd_7375981 : Nat := 4983230072969 + 3 ^ 40 * 7375981 * 2
def baseEnd_7375981 : Nat := 1262474517143603724705329

theorem tailTrace_7375981 : CollatzResearch.WordTrace tailWord_7375981 prefixEnd_7375981 1262474517143603724705329 := by
  unfold tailWord_7375981
  simp only [CollatzResearch.WordTrace]
  refine ⟨269024128291088029108695797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179349418860725352739130531 269024128291088029108695797)
  ·
    refine ⟨25221012027289502728940231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269024128291088029108695797 25221012027289502728940231)
    ·
      refine ⟨37831518040934254093410347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25221012027289502728940231 37831518040934254093410347)
      ·
        refine ⟨56747277061401381140115521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37831518040934254093410347 56747277061401381140115521)
        ·
          refine ⟨42560457796051035855086641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56747277061401381140115521 42560457796051035855086641)
          ·
            refine ⟨31920343347038276891314981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42560457796051035855086641 31920343347038276891314981)
            ·
              refine ⟨5985064377569676917121559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31920343347038276891314981 5985064377569676917121559)
              ·
                refine ⟨8977596566354515375682339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985064377569676917121559 8977596566354515375682339)
                ·
                  refine ⟨13466394849531773063523509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977596566354515375682339 13466394849531773063523509)
                  ·
                    refine ⟨1262474517143603724705329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13466394849531773063523509 1262474517143603724705329)
                    ·
                      rfl

theorem cell23_7375981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_7375981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375981 prefixEnd_7375981 := by exact prefixLift 7375981
  have htrace : WordTrace (prefixWord ++ tailWord_7375981) baseStart_7375981 baseEnd_7375981 := by
    simpa [prefixWord, tailWord_7375981, baseEnd_7375981] using wordTrace_append hprefix tailTrace_7375981
  have hstable : (prefixWord ++ tailWord_7375981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375981).length < 2 ^ (prefixWord ++ tailWord_7375981).sum := by decide
  have hdescent : baseEnd_7375981 < baseStart_7375981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375984 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4]
def baseStart_7375984 : Nat := 118140960795 + 7375984 * 2 ^ 59
def prefixEnd_7375984 : Nat := 4983230072969 + 3 ^ 40 * 7375984 * 2
def baseEnd_7375984 : Nat := 3787425091872774662378473

theorem tailTrace_7375984 : CollatzResearch.WordTrace tailWord_7375984 prefixEnd_7375984 3787425091872774662378473 := by
  unfold tailWord_7375984
  simp only [CollatzResearch.WordTrace]
  refine ⟨134512118855038580310527503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179349491806718107080703337 134512118855038580310527503)
  ·
    refine ⟨201768178282557870465791255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134512118855038580310527503 201768178282557870465791255)
    ·
      refine ⟨302652267423836805698686883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201768178282557870465791255 302652267423836805698686883)
      ·
        refine ⟨453978401135755208548030325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302652267423836805698686883 453978401135755208548030325)
        ·
          refine ⟨42560475106477050801377843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 453978401135755208548030325 42560475106477050801377843)
          ·
            refine ⟨63840712659715576202066765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42560475106477050801377843 63840712659715576202066765)
            ·
              refine ⟨23940267247393341075775037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63840712659715576202066765 23940267247393341075775037)
              ·
                refine ⟨8977600217772502903415639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23940267247393341075775037 8977600217772502903415639)
                ·
                  refine ⟨13466400326658754355123459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977600217772502903415639 13466400326658754355123459)
                  ·
                    refine ⟨20199600489988131532685189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13466400326658754355123459 20199600489988131532685189)
                    ·
                      refine ⟨3787425091872774662378473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20199600489988131532685189 3787425091872774662378473)
                      ·
                        rfl

theorem cell23_7375984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_7375984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375984 prefixEnd_7375984 := by exact prefixLift 7375984
  have htrace : WordTrace (prefixWord ++ tailWord_7375984) baseStart_7375984 baseEnd_7375984 := by
    simpa [prefixWord, tailWord_7375984, baseEnd_7375984] using wordTrace_append hprefix tailTrace_7375984
  have hstable : (prefixWord ++ tailWord_7375984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375984).length < 2 ^ (prefixWord ++ tailWord_7375984).sum := by decide
  have hdescent : baseEnd_7375984 < baseStart_7375984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375997 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_7375997 : Nat := 118140960795 + 7375997 * 2 ^ 59
def prefixEnd_7375997 : Nat := 4983230072969 + 3 ^ 40 * 7375997 * 2
def baseEnd_7375997 : Nat := 3787431767121283111515913

theorem tailTrace_7375997 : CollatzResearch.WordTrace tailWord_7375997 prefixEnd_7375997 3787431767121283111515913 := by
  unfold tailWord_7375997
  simp only [CollatzResearch.WordTrace]
  refine ⟨269024711859030063841278245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179349807906020042560852163 269024711859030063841278245)
  ·
    refine ⟨50442133473568136970239671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269024711859030063841278245 50442133473568136970239671)
    ·
      refine ⟨75663200210352205455359507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50442133473568136970239671 75663200210352205455359507)
      ·
        refine ⟨113494800315528308183039261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75663200210352205455359507 113494800315528308183039261)
        ·
          refine ⟨42560550118323115568639723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113494800315528308183039261 42560550118323115568639723)
          ·
            refine ⟨63840825177484673352959585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42560550118323115568639723 63840825177484673352959585)
            ·
              refine ⟨47880618883113505014719689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63840825177484673352959585 47880618883113505014719689)
              ·
                refine ⟨35910464162335128761039767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47880618883113505014719689 35910464162335128761039767)
                ·
                  refine ⟨53865696243502693141559651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35910464162335128761039767 53865696243502693141559651)
                  ·
                    refine ⟨80798544365254039712339477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53865696243502693141559651 80798544365254039712339477)
                    ·
                      refine ⟨3787431767121283111515913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80798544365254039712339477 3787431767121283111515913)
                      ·
                        rfl

theorem cell23_7375997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_7375997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375997 prefixEnd_7375997 := by exact prefixLift 7375997
  have htrace : WordTrace (prefixWord ++ tailWord_7375997) baseStart_7375997 baseEnd_7375997 := by
    simpa [prefixWord, tailWord_7375997, baseEnd_7375997] using wordTrace_append hprefix tailTrace_7375997
  have hstable : (prefixWord ++ tailWord_7375997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375997).length < 2 ^ (prefixWord ++ tailWord_7375997).sum := by decide
  have hdescent : baseEnd_7375997 < baseStart_7375997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376004 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7376004 : Nat := 118140960795 + 7376004 * 2 ^ 59
def prefixEnd_7376004 : Nat := 4983230072969 + 3 ^ 40 * 7376004 * 2
def baseEnd_7376004 : Nat := 3787435361485864584128381

theorem tailTrace_7376004 : CollatzResearch.WordTrace tailWord_7376004 prefixEnd_7376004 3787435361485864584128381 := by
  unfold tailWord_7376004
  simp only [CollatzResearch.WordTrace]
  refine ⟨134512483585002352018391533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179349978113336469357855377 134512483585002352018391533)
  ·
    refine ⟨50442181344375882006896825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134512483585002352018391533 50442181344375882006896825)
    ·
      refine ⟨37831636008281911505172619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50442181344375882006896825 37831636008281911505172619)
      ·
        refine ⟨56747454012422867257758929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37831636008281911505172619 56747454012422867257758929)
        ·
          refine ⟨42560590509317150443319197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56747454012422867257758929 42560590509317150443319197)
          ·
            refine ⟨15960221440993931416244699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42560590509317150443319197 15960221440993931416244699)
            ·
              refine ⟨23940332161490897124367049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15960221440993931416244699 23940332161490897124367049)
              ·
                refine ⟨17955249121118172843275287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23940332161490897124367049 17955249121118172843275287)
                ·
                  refine ⟨26932873681677259264912931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17955249121118172843275287 26932873681677259264912931)
                  ·
                    refine ⟨40399310522515888897369397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26932873681677259264912931 40399310522515888897369397)
                    ·
                      refine ⟨3787435361485864584128381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40399310522515888897369397 3787435361485864584128381)
                      ·
                        rfl

theorem cell23_7376004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7376004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376004 prefixEnd_7376004 := by exact prefixLift 7376004
  have htrace : WordTrace (prefixWord ++ tailWord_7376004) baseStart_7376004 baseEnd_7376004 := by
    simpa [prefixWord, tailWord_7376004, baseEnd_7376004] using wordTrace_append hprefix tailTrace_7376004
  have hstable : (prefixWord ++ tailWord_7376004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376004).length < 2 ^ (prefixWord ++ tailWord_7376004).sum := by decide
  have hdescent : baseEnd_7376004 < baseStart_7376004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376014 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7376014 : Nat := 118140960795 + 7376014 * 2 ^ 59
def prefixEnd_7376014 : Nat := 4983230072969 + 3 ^ 40 * 7376014 * 2
def baseEnd_7376014 : Nat := 3787440496292409545003335

theorem tailTrace_7376014 : CollatzResearch.WordTrace tailWord_7376014 prefixEnd_7376014 3787440496292409545003335 := by
  unfold tailWord_7376014
  simp only [CollatzResearch.WordTrace]
  refine ⟨33628166487496059468080887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179350221266645650496431397 33628166487496059468080887)
  ·
    refine ⟨50442249731244089202121331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33628166487496059468080887 50442249731244089202121331)
    ·
      refine ⟨75663374596866133803181997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50442249731244089202121331 75663374596866133803181997)
      ·
        refine ⟨28373765473824800176193249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75663374596866133803181997 28373765473824800176193249)
        ·
          refine ⟨21280324105368600132144937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28373765473824800176193249 21280324105368600132144937)
          ·
            refine ⟨15960243079026450099108703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21280324105368600132144937 15960243079026450099108703)
            ·
              refine ⟨23940364618539675148663055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15960243079026450099108703 23940364618539675148663055)
              ·
                refine ⟨35910546927809512722994583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23940364618539675148663055 35910546927809512722994583)
                ·
                  refine ⟨53865820391714269084491875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35910546927809512722994583 53865820391714269084491875)
                  ·
                    refine ⟨80798730587571403626737813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53865820391714269084491875 80798730587571403626737813)
                    ·
                      refine ⟨3787440496292409545003335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80798730587571403626737813 3787440496292409545003335)
                      ·
                        rfl

theorem cell23_7376014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7376014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376014 prefixEnd_7376014 := by exact prefixLift 7376014
  have htrace : WordTrace (prefixWord ++ tailWord_7376014) baseStart_7376014 baseEnd_7376014 := by
    simpa [prefixWord, tailWord_7376014, baseEnd_7376014] using wordTrace_append hprefix tailTrace_7376014
  have hstable : (prefixWord ++ tailWord_7376014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376014).length < 2 ^ (prefixWord ++ tailWord_7376014).sum := by decide
  have hdescent : baseEnd_7376014 < baseStart_7376014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376018 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_7376018 : Nat := 118140960795 + 7376018 * 2 ^ 59
def prefixEnd_7376018 : Nat := 4983230072969 + 3 ^ 40 * 7376018 * 2
def baseEnd_7376018 : Nat := 3787442550215027529353317

theorem tailTrace_7376018 : CollatzResearch.WordTrace tailWord_7376018 prefixEnd_7376018 3787442550215027529353317 := by
  unfold tailWord_7376018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67256369447988496106948177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179350318527969322951861805 67256369447988496106948177)
  ·
    refine ⟨50442277085991372080211133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67256369447988496106948177 50442277085991372080211133)
    ·
      refine ⟨18915853907246764530079175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50442277085991372080211133 18915853907246764530079175)
      ·
        refine ⟨28373780860870146795118763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18915853907246764530079175 28373780860870146795118763)
        ·
          refine ⟨42560671291305220192678145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28373780860870146795118763 42560671291305220192678145)
          ·
            refine ⟨31920503468478915144508609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42560671291305220192678145 31920503468478915144508609)
            ·
              refine ⟨23940377601359186358381457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31920503468478915144508609 23940377601359186358381457)
              ·
                refine ⟨17955283201019389768786093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23940377601359186358381457 17955283201019389768786093)
                ·
                  refine ⟨6733231200382271163294785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17955283201019389768786093 6733231200382271163294785)
                  ·
                    refine ⟨5049923400286703372471089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733231200382271163294785 5049923400286703372471089)
                    ·
                      refine ⟨3787442550215027529353317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049923400286703372471089 3787442550215027529353317)
                      ·
                        rfl

theorem cell23_7376018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_7376018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376018 prefixEnd_7376018 := by exact prefixLift 7376018
  have htrace : WordTrace (prefixWord ++ tailWord_7376018) baseStart_7376018 baseEnd_7376018 := by
    simpa [prefixWord, tailWord_7376018, baseEnd_7376018] using wordTrace_append hprefix tailTrace_7376018
  have hstable : (prefixWord ++ tailWord_7376018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376018).length < 2 ^ (prefixWord ++ tailWord_7376018).sum := by decide
  have hdescent : baseEnd_7376018 < baseStart_7376018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376024 : List Nat := [2, 1, 2, 4, 2, 1, 4, 7]
def baseStart_7376024 : Nat := 118140960795 + 7376024 * 2 ^ 59
def prefixEnd_7376024 : Nat := 4983230072969 + 3 ^ 40 * 7376024 * 2
def baseEnd_7376024 : Nat := 140275764114776092810307

theorem tailTrace_7376024 : CollatzResearch.WordTrace tailWord_7376024 prefixEnd_7376024 140275764114776092810307 := by
  unfold tailWord_7376024
  simp only [CollatzResearch.WordTrace]
  refine ⟨134512848314966123726255563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179350464419954831635007417 134512848314966123726255563)
  ·
    refine ⟨201769272472449185589383345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134512848314966123726255563 201769272472449185589383345)
    ·
      refine ⟨151326954354336889192037509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201769272472449185589383345 151326954354336889192037509)
      ·
        refine ⟨28373803941438166723507033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151326954354336889192037509 28373803941438166723507033)
        ·
          refine ⟨21280352956078625042630275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28373803941438166723507033 21280352956078625042630275)
          ·
            refine ⟨31920529434117937563945413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21280352956078625042630275 31920529434117937563945413)
            ·
              refine ⟨5985099268897113293239765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31920529434117937563945413 5985099268897113293239765)
              ·
                refine ⟨140275764114776092810307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5985099268897113293239765 140275764114776092810307)
                ·
                  rfl

theorem cell23_7376024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 7].length) (baseStart_7376024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376024 prefixEnd_7376024 := by exact prefixLift 7376024
  have htrace : WordTrace (prefixWord ++ tailWord_7376024) baseStart_7376024 baseEnd_7376024 := by
    simpa [prefixWord, tailWord_7376024, baseEnd_7376024] using wordTrace_append hprefix tailTrace_7376024
  have hstable : (prefixWord ++ tailWord_7376024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376024).length < 2 ^ (prefixWord ++ tailWord_7376024).sum := by decide
  have hdescent : baseEnd_7376024 < baseStart_7376024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376078 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_7376078 : Nat := 118140960795 + 7376078 * 2 ^ 59
def prefixEnd_7376078 : Nat := 4983230072969 + 3 ^ 40 * 7376078 * 2
def baseEnd_7376078 : Nat := 3787473359054297294603041

theorem tailTrace_7376078 : CollatzResearch.WordTrace tailWord_7376078 prefixEnd_7376078 3787473359054297294603041 := by
  unfold tailWord_7376078
  simp only [CollatzResearch.WordTrace]
  refine ⟨33628458271467076834372111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179351777447824409783317925 33628458271467076834372111)
  ·
    refine ⟨50442687407200615251558167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33628458271467076834372111 50442687407200615251558167)
    ·
      refine ⟨75664031110800922877337251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50442687407200615251558167 75664031110800922877337251)
      ·
        refine ⟨113496046666201384316005877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75664031110800922877337251 113496046666201384316005877)
        ·
          refine ⟨10640254374956379779625551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113496046666201384316005877 10640254374956379779625551)
          ·
            refine ⟨15960381562434569669438327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10640254374956379779625551 15960381562434569669438327)
            ·
              refine ⟨23940572343651854504157491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15960381562434569669438327 23940572343651854504157491)
              ·
                refine ⟨35910858515477781756236237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23940572343651854504157491 35910858515477781756236237)
                ·
                  refine ⟨13466571943304168158588589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35910858515477781756236237 13466571943304168158588589)
                  ·
                    refine ⟨5049964478739063059470721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13466571943304168158588589 5049964478739063059470721)
                    ·
                      refine ⟨3787473359054297294603041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049964478739063059470721 3787473359054297294603041)
                      ·
                        rfl

theorem cell23_7376078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_7376078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376078 prefixEnd_7376078 := by exact prefixLift 7376078
  have htrace : WordTrace (prefixWord ++ tailWord_7376078) baseStart_7376078 baseEnd_7376078 := by
    simpa [prefixWord, tailWord_7376078, baseEnd_7376078] using wordTrace_append hprefix tailTrace_7376078
  have hstable : (prefixWord ++ tailWord_7376078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376078).length < 2 ^ (prefixWord ++ tailWord_7376078).sum := by decide
  have hdescent : baseEnd_7376078 < baseStart_7376078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376104 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7376104 : Nat := 118140960795 + 7376104 * 2 ^ 59
def prefixEnd_7376104 : Nat := 4983230072969 + 3 ^ 40 * 7376104 * 2
def baseEnd_7376104 : Nat := 3787486709551314192877921

theorem tailTrace_7376104 : CollatzResearch.WordTrace tailWord_7376104 prefixEnd_7376104 3787486709551314192877921 := by
  unfold tailWord_7376104
  simp only [CollatzResearch.WordTrace]
  refine ⟨134514307234821210557711683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179352409646428280743615577 134514307234821210557711683)
  ·
    refine ⟨201771460852231815836567525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134514307234821210557711683 201771460852231815836567525)
    ·
      refine ⟨37832148909793465469356411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201771460852231815836567525 37832148909793465469356411)
      ·
        refine ⟨56748223364690198204034617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37832148909793465469356411 56748223364690198204034617)
        ·
          refine ⟨42561167523517648653025963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56748223364690198204034617 42561167523517648653025963)
          ·
            refine ⟨63841751285276472979538945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42561167523517648653025963 63841751285276472979538945)
            ·
              refine ⟨47881313463957354734654209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63841751285276472979538945 47881313463957354734654209)
              ·
                refine ⟨35910985097968016050990657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47881313463957354734654209 35910985097968016050990657)
                ·
                  refine ⟨26933238823476012038242993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35910985097968016050990657 26933238823476012038242993)
                  ·
                    refine ⟨20199929117607009028682245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26933238823476012038242993 20199929117607009028682245)
                    ·
                      refine ⟨3787486709551314192877921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20199929117607009028682245 3787486709551314192877921)
                      ·
                        rfl

theorem cell23_7376104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7376104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376104 prefixEnd_7376104 := by exact prefixLift 7376104
  have htrace : WordTrace (prefixWord ++ tailWord_7376104) baseStart_7376104 baseEnd_7376104 := by
    simpa [prefixWord, tailWord_7376104, baseEnd_7376104] using wordTrace_append hprefix tailTrace_7376104
  have hstable : (prefixWord ++ tailWord_7376104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376104).length < 2 ^ (prefixWord ++ tailWord_7376104).sum := by decide
  have hdescent : baseEnd_7376104 < baseStart_7376104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376108 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 2, 2, 2]
def baseStart_7376108 : Nat := 118140960795 + 7376108 * 2 ^ 59
def prefixEnd_7376108 : Nat := 4983230072969 + 3 ^ 40 * 7376108 * 2
def baseEnd_7376108 : Nat := 3787488763473932177227903

theorem tailTrace_7376108 : CollatzResearch.WordTrace tailWord_7376108 prefixEnd_7376108 3787488763473932177227903 := by
  unfold tailWord_7376108
  simp only [CollatzResearch.WordTrace]
  refine ⟨134514380180813964899284489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179352506907751953199045985 134514380180813964899284489)
  ·
    refine ⟨100885785135610473674463367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134514380180813964899284489 100885785135610473674463367)
    ·
      refine ⟨151328677703415710511695051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100885785135610473674463367 151328677703415710511695051)
      ·
        refine ⟨226993016555123565767542577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151328677703415710511695051 226993016555123565767542577)
        ·
          refine ⟨170244762416342674325656933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226993016555123565767542577 170244762416342674325656933)
          ·
            refine ⟨31920892953064251436060675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170244762416342674325656933 31920892953064251436060675)
            ·
              refine ⟨47881339429596377154091013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31920892953064251436060675 47881339429596377154091013)
              ·
                refine ⟨8977751143049320716392065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47881339429596377154091013 8977751143049320716392065)
                ·
                  refine ⟨6733313357286990537294049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8977751143049320716392065 6733313357286990537294049)
                  ·
                    refine ⟨5049985017965242902970537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733313357286990537294049 5049985017965242902970537)
                    ·
                      refine ⟨3787488763473932177227903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049985017965242902970537 3787488763473932177227903)
                      ·
                        rfl

theorem cell23_7376108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_7376108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376108 prefixEnd_7376108 := by exact prefixLift 7376108
  have htrace : WordTrace (prefixWord ++ tailWord_7376108) baseStart_7376108 baseEnd_7376108 := by
    simpa [prefixWord, tailWord_7376108, baseEnd_7376108] using wordTrace_append hprefix tailTrace_7376108
  have hstable : (prefixWord ++ tailWord_7376108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376108).length < 2 ^ (prefixWord ++ tailWord_7376108).sum := by decide
  have hdescent : baseEnd_7376108 < baseStart_7376108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376146 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7376146 : Nat := 118140960795 + 7376146 * 2 ^ 59
def prefixEnd_7376146 : Nat := 4983230072969 + 3 ^ 40 * 7376146 * 2
def baseEnd_7376146 : Nat := 3787508275738803028552729

theorem tailTrace_7376146 : CollatzResearch.WordTrace tailWord_7376146 prefixEnd_7376146 3787508275738803028552729 := by
  unfold tailWord_7376146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67257536583872565572113073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179353430890326841525634861 67257536583872565572113073)
  ·
    refine ⟨50443152437904424179084805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67257536583872565572113073 50443152437904424179084805)
    ·
      refine ⟨9458091082107079533578401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50443152437904424179084805 9458091082107079533578401)
      ·
        refine ⟨7093568311580309650183801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9458091082107079533578401 7093568311580309650183801)
        ·
          refine ⟨5320176233685232237637851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7093568311580309650183801 5320176233685232237637851)
          ·
            refine ⟨7980264350527848356456777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320176233685232237637851 7980264350527848356456777)
            ·
              refine ⟨5985198262895886267342583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980264350527848356456777 5985198262895886267342583)
              ·
                refine ⟨8977797394343829401013875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985198262895886267342583 8977797394343829401013875)
                ·
                  refine ⟨13466696091515744101520813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977797394343829401013875 13466696091515744101520813)
                  ·
                    refine ⟨5050011034318404038070305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13466696091515744101520813 5050011034318404038070305)
                    ·
                      refine ⟨3787508275738803028552729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050011034318404038070305 3787508275738803028552729)
                      ·
                        rfl

theorem cell23_7376146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7376146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376146 prefixEnd_7376146 := by exact prefixLift 7376146
  have htrace : WordTrace (prefixWord ++ tailWord_7376146) baseStart_7376146 baseEnd_7376146 := by
    simpa [prefixWord, tailWord_7376146, baseEnd_7376146] using wordTrace_append hprefix tailTrace_7376146
  have hstable : (prefixWord ++ tailWord_7376146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376146).length < 2 ^ (prefixWord ++ tailWord_7376146).sum := by decide
  have hdescent : baseEnd_7376146 < baseStart_7376146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376191 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 3, 4]
def baseStart_7376191 : Nat := 118140960795 + 7376191 * 2 ^ 59
def prefixEnd_7376191 : Nat := 4983230072969 + 3 ^ 40 * 7376191 * 2
def baseEnd_7376191 : Nat := 1262510460789418450830007

theorem tailTrace_7376191 : CollatzResearch.WordTrace tailWord_7376191 prefixEnd_7376191 1262510460789418450830007 := by
  unfold tailWord_7376191
  simp only [CollatzResearch.WordTrace]
  refine ⟨269031787620327234973840427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179354525080218156649226951 269031787620327234973840427)
  ·
    refine ⟨403547681430490852460760641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269031787620327234973840427 403547681430490852460760641)
    ·
      refine ⟨302660761072868139345570481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403547681430490852460760641 302660761072868139345570481)
      ·
        refine ⟨226995570804651104509177861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302660761072868139345570481 226995570804651104509177861)
        ·
          refine ⟨42561669525872082095470849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226995570804651104509177861 42561669525872082095470849)
          ·
            refine ⟨31921252144404061571603137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42561669525872082095470849 31921252144404061571603137)
            ·
              refine ⟨23940939108303046178702353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31921252144404061571603137 23940939108303046178702353)
              ·
                refine ⟨17955704331227284634026765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23940939108303046178702353 17955704331227284634026765)
                ·
                  refine ⟨6733389124210231737760037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17955704331227284634026765 6733389124210231737760037)
                  ·
                    refine ⟨1262510460789418450830007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6733389124210231737760037 1262510460789418450830007)
                    ·
                      rfl

theorem cell23_7376191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_7376191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376191 prefixEnd_7376191 := by exact prefixLift 7376191
  have htrace : WordTrace (prefixWord ++ tailWord_7376191) baseStart_7376191 baseEnd_7376191 := by
    simpa [prefixWord, tailWord_7376191, baseEnd_7376191] using wordTrace_append hprefix tailTrace_7376191
  have hstable : (prefixWord ++ tailWord_7376191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376191).length < 2 ^ (prefixWord ++ tailWord_7376191).sum := by decide
  have hdescent : baseEnd_7376191 < baseStart_7376191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376204 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 8]
def baseStart_7376204 : Nat := 118140960795 + 7376204 * 2 ^ 59
def prefixEnd_7376204 : Nat := 4983230072969 + 3 ^ 40 * 7376204 * 2
def baseEnd_7376204 : Nat := 420837561957418200180829

theorem tailTrace_7376204 : CollatzResearch.WordTrace tailWord_7376204 prefixEnd_7376204 420837561957418200180829 := by
  unfold tailWord_7376204
  simp only [CollatzResearch.WordTrace]
  refine ⟨134516130884640069097031833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179354841179520092129375777 134516130884640069097031833)
  ·
    refine ⟨100887098163480051822773875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134516130884640069097031833 100887098163480051822773875)
    ·
      refine ⟨151330647245220077734160813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100887098163480051822773875 151330647245220077734160813)
      ·
        refine ⟨56748992716957529150310305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151330647245220077734160813 56748992716957529150310305)
        ·
          refine ⟨42561744537718146862732729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56748992716957529150310305 42561744537718146862732729)
          ·
            refine ⟨31921308403288610147049547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42561744537718146862732729 31921308403288610147049547)
            ·
              refine ⟨47881962604932915220574321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31921308403288610147049547 47881962604932915220574321)
              ·
                refine ⟨35911471953699686415430741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47881962604932915220574321 35911471953699686415430741)
                ·
                  refine ⟨420837561957418200180829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35911471953699686415430741 420837561957418200180829)
                  ·
                    rfl

theorem cell23_7376204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_7376204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376204 prefixEnd_7376204 := by exact prefixLift 7376204
  have htrace : WordTrace (prefixWord ++ tailWord_7376204) baseStart_7376204 baseEnd_7376204 := by
    simpa [prefixWord, tailWord_7376204, baseEnd_7376204] using wordTrace_append hprefix tailTrace_7376204
  have hstable : (prefixWord ++ tailWord_7376204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376204).length < 2 ^ (prefixWord ++ tailWord_7376204).sum := by decide
  have hdescent : baseEnd_7376204 < baseStart_7376204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376241 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 3, 5, 2]
def baseStart_7376241 : Nat := 118140960795 + 7376241 * 2 ^ 59
def prefixEnd_7376241 : Nat := 4983230072969 + 3 ^ 40 * 7376241 * 2
def baseEnd_7376241 : Nat := 3787557056400980156864791

theorem tailTrace_7376241 : CollatzResearch.WordTrace tailWord_7376241 prefixEnd_7376241 3787557056400980156864791 := by
  unfold tailWord_7376241
  simp only [CollatzResearch.WordTrace]
  refine ⟨269033611270146093513160577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179355740846764062342107051 269033611270146093513160577)
  ·
    refine ⟨201775208452609570134870433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269033611270146093513160577 201775208452609570134870433)
    ·
      refine ⟨151331406339457177601152825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201775208452609570134870433 151331406339457177601152825)
      ·
        refine ⟨113498554754592883200864619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151331406339457177601152825 113498554754592883200864619)
        ·
          refine ⟨170247832131889324801296929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113498554754592883200864619 170247832131889324801296929)
          ·
            refine ⟨127685874098916993600972697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170247832131889324801296929 127685874098916993600972697)
            ·
              refine ⟨95764405574187745200729523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127685874098916993600972697 95764405574187745200729523)
              ·
                refine ⟨143646608361281617801094285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95764405574187745200729523 143646608361281617801094285)
                ·
                  refine ⟨53867478135480606675410357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143646608361281617801094285 53867478135480606675410357)
                  ·
                    refine ⟨5050076075201306875819721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53867478135480606675410357 5050076075201306875819721)
                    ·
                      refine ⟨3787557056400980156864791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050076075201306875819721 3787557056400980156864791)
                      ·
                        rfl

theorem cell23_7376241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_7376241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376241 prefixEnd_7376241 := by exact prefixLift 7376241
  have htrace : WordTrace (prefixWord ++ tailWord_7376241) baseStart_7376241 baseEnd_7376241 := by
    simpa [prefixWord, tailWord_7376241, baseEnd_7376241] using wordTrace_append hprefix tailTrace_7376241
  have hstable : (prefixWord ++ tailWord_7376241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376241).length < 2 ^ (prefixWord ++ tailWord_7376241).sum := by decide
  have hdescent : baseEnd_7376241 < baseStart_7376241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376268 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_7376268 : Nat := 118140960795 + 7376268 * 2 ^ 59
def prefixEnd_7376268 : Nat := 4983230072969 + 3 ^ 40 * 7376268 * 2
def baseEnd_7376268 : Nat := 1262523640126217183742389

theorem tailTrace_7376268 : CollatzResearch.WordTrace tailWord_7376268 prefixEnd_7376268 1262523640126217183742389 := by
  unfold tailWord_7376268
  simp only [CollatzResearch.WordTrace]
  refine ⟨134517298020524138562196729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179356397360698851416262305 134517298020524138562196729)
  ·
    refine ⟨100887973515393103921647547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134517298020524138562196729 100887973515393103921647547)
    ·
      refine ⟨151331960273089655882471321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100887973515393103921647547 151331960273089655882471321)
      ·
        refine ⟨113498970204817241911853491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151331960273089655882471321 113498970204817241911853491)
        ·
          refine ⟨170248455307225862867780237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113498970204817241911853491 170248455307225862867780237)
          ·
            refine ⟨63843170740209698575417589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170248455307225862867780237 63843170740209698575417589)
            ·
              refine ⟨5985297256894659241445399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63843170740209698575417589 5985297256894659241445399)
              ·
                refine ⟨8977945885341988862168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985297256894659241445399 8977945885341988862168099)
                ·
                  refine ⟨13466918828012983293252149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977945885341988862168099 13466918828012983293252149)
                  ·
                    refine ⟨1262523640126217183742389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13466918828012983293252149 1262523640126217183742389)
                    ·
                      rfl

theorem cell23_7376268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_7376268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376268 prefixEnd_7376268 := by exact prefixLift 7376268
  have htrace : WordTrace (prefixWord ++ tailWord_7376268) baseStart_7376268 baseEnd_7376268 := by
    simpa [prefixWord, tailWord_7376268, baseEnd_7376268] using wordTrace_append hprefix tailTrace_7376268
  have hstable : (prefixWord ++ tailWord_7376268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376268).length < 2 ^ (prefixWord ++ tailWord_7376268).sum := by decide
  have hdescent : baseEnd_7376268 < baseStart_7376268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376291 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 3]
def baseStart_7376291 : Nat := 118140960795 + 7376291 * 2 ^ 59
def prefixEnd_7376291 : Nat := 4983230072969 + 3 ^ 40 * 7376291 * 2
def baseEnd_7376291 : Nat := 3787582730433704961239561

theorem tailTrace_7376291 : CollatzResearch.WordTrace tailWord_7376291 prefixEnd_7376291 3787582730433704961239561 := by
  unfold tailWord_7376291
  simp only [CollatzResearch.WordTrace]
  refine ⟨269035434919964952052480727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179356956613309968034987151 269035434919964952052480727)
  ·
    refine ⟨403553152379947428078721091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269035434919964952052480727 403553152379947428078721091)
    ·
      refine ⟨605329728569921142118081637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403553152379947428078721091 605329728569921142118081637)
      ·
        refine ⟨113499324106860214147140307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605329728569921142118081637 113499324106860214147140307)
        ·
          refine ⟨170248986160290321220710461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113499324106860214147140307 170248986160290321220710461)
          ·
            refine ⟨63843369810108870457766423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170248986160290321220710461 63843369810108870457766423)
            ·
              refine ⟨95765054715163305686649635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63843369810108870457766423 95765054715163305686649635)
              ·
                refine ⟨143647582072744958529974453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95765054715163305686649635 143647582072744958529974453)
                ·
                  refine ⟨13466960819319839862185105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143647582072744958529974453 13466960819319839862185105)
                  ·
                    refine ⟨10100220614489879896638829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13466960819319839862185105 10100220614489879896638829)
                    ·
                      refine ⟨3787582730433704961239561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10100220614489879896638829 3787582730433704961239561)
                      ·
                        rfl

theorem cell23_7376291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_7376291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376291 prefixEnd_7376291 := by exact prefixLift 7376291
  have htrace : WordTrace (prefixWord ++ tailWord_7376291) baseStart_7376291 baseEnd_7376291 := by
    simpa [prefixWord, tailWord_7376291, baseEnd_7376291] using wordTrace_append hprefix tailTrace_7376291
  have hstable : (prefixWord ++ tailWord_7376291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376291).length < 2 ^ (prefixWord ++ tailWord_7376291).sum := by decide
  have hdescent : baseEnd_7376291 < baseStart_7376291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376305 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7376305 : Nat := 118140960795 + 7376305 * 2 ^ 59
def prefixEnd_7376305 : Nat := 4983230072969 + 3 ^ 40 * 7376305 * 2
def baseEnd_7376305 : Nat := 3787589919162867906464497

theorem tailTrace_7376305 : CollatzResearch.WordTrace tailWord_7376305 prefixEnd_7376305 3787589919162867906464497 := by
  unfold tailWord_7376305
  simp only [CollatzResearch.WordTrace]
  refine ⟨269035945541914232443490369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179357297027942821628993579 269035945541914232443490369)
  ·
    refine ⟨201776959156435674332617777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269035945541914232443490369 201776959156435674332617777)
    ·
      refine ⟨151332719367326755749463333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201776959156435674332617777 151332719367326755749463333)
      ·
        refine ⟨28374884881373766703024375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151332719367326755749463333 28374884881373766703024375)
        ·
          refine ⟨42562327322060650054536563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28374884881373766703024375 42562327322060650054536563)
          ·
            refine ⟨63843490983090975081804845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42562327322060650054536563 63843490983090975081804845)
            ·
              refine ⟨23941309118659115655676817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63843490983090975081804845 23941309118659115655676817)
              ·
                refine ⟨17955981838994336741757613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23941309118659115655676817 17955981838994336741757613)
                ·
                  refine ⟨6733493189622876278159105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17955981838994336741757613 6733493189622876278159105)
                  ·
                    refine ⟨5050119892217157208619329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733493189622876278159105 5050119892217157208619329)
                    ·
                      refine ⟨3787589919162867906464497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050119892217157208619329 3787589919162867906464497)
                      ·
                        rfl

theorem cell23_7376305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7376305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376305 prefixEnd_7376305 := by exact prefixLift 7376305
  have htrace : WordTrace (prefixWord ++ tailWord_7376305) baseStart_7376305 baseEnd_7376305 := by
    simpa [prefixWord, tailWord_7376305, baseEnd_7376305] using wordTrace_append hprefix tailTrace_7376305
  have hstable : (prefixWord ++ tailWord_7376305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376305).length < 2 ^ (prefixWord ++ tailWord_7376305).sum := by decide
  have hdescent : baseEnd_7376305 < baseStart_7376305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376311 : List Nat := [1, 1, 3, 1, 3, 2, 5, 7]
def baseStart_7376311 : Nat := 118140960795 + 7376311 * 2 ^ 59
def prefixEnd_7376311 : Nat := 4983230072969 + 3 ^ 40 * 7376311 * 2
def baseEnd_7376311 : Nat := 140281222223955366036647

theorem tailTrace_7376311 : CollatzResearch.WordTrace tailWord_7376311 prefixEnd_7376311 140281222223955366036647 := by
  unfold tailWord_7376311
  simp only [CollatzResearch.WordTrace]
  refine ⟨269036164379892495468208787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179357442919928330312139191 269036164379892495468208787)
  ·
    refine ⟨403554246569838743202313181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269036164379892495468208787 403554246569838743202313181)
    ·
      refine ⟨151332842463689528700867443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403554246569838743202313181 151332842463689528700867443)
      ·
        refine ⟨226999263695534293051301165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151332842463689528700867443 226999263695534293051301165)
        ·
          refine ⟨85124723885825359894237937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226999263695534293051301165 85124723885825359894237937)
          ·
            refine ⟨63843542914369019920678453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85124723885825359894237937 63843542914369019920678453)
            ·
              refine ⟨5985332148222095617563605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63843542914369019920678453 5985332148222095617563605)
              ·
                refine ⟨140281222223955366036647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5985332148222095617563605 140281222223955366036647)
                ·
                  rfl

theorem cell23_7376311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 7].length) (baseStart_7376311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376311 prefixEnd_7376311 := by exact prefixLift 7376311
  have htrace : WordTrace (prefixWord ++ tailWord_7376311) baseStart_7376311 baseEnd_7376311 := by
    simpa [prefixWord, tailWord_7376311, baseEnd_7376311] using wordTrace_append hprefix tailTrace_7376311
  have hstable : (prefixWord ++ tailWord_7376311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376311).length < 2 ^ (prefixWord ++ tailWord_7376311).sum := by decide
  have hdescent : baseEnd_7376311 < baseStart_7376311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376355 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 3]
def baseStart_7376355 : Nat := 118140960795 + 7376355 * 2 ^ 59
def prefixEnd_7376355 : Nat := 4983230072969 + 3 ^ 40 * 7376355 * 2
def baseEnd_7376355 : Nat := 3787615593195592710839267

theorem tailTrace_7376355 : CollatzResearch.WordTrace tailWord_7376355 prefixEnd_7376355 3787615593195592710839267 := by
  unfold tailWord_7376355
  simp only [CollatzResearch.WordTrace]
  refine ⟨269037769191733090982810519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179358512794488727321873679 269037769191733090982810519)
  ·
    refine ⟨403556653787599636474215779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269037769191733090982810519 403556653787599636474215779)
    ·
      refine ⟨605334980681399454711323669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403556653787599636474215779 605334980681399454711323669)
      ·
        refine ⟨28375077219440599439593297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 605334980681399454711323669 28375077219440599439593297)
        ·
          refine ⟨21281307914580449579694973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28375077219440599439593297 21281307914580449579694973)
          ·
            refine ⟨7980490467967668592385615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21281307914580449579694973 7980490467967668592385615)
            ·
              refine ⟨11970735701951502888578423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980490467967668592385615 11970735701951502888578423)
              ·
                refine ⟨17956103552927254332867635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11970735701951502888578423 17956103552927254332867635)
                ·
                  refine ⟨26934155329390881499301453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17956103552927254332867635 26934155329390881499301453)
                  ·
                    refine ⟨10100308248521580562238045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26934155329390881499301453 10100308248521580562238045)
                    ·
                      refine ⟨3787615593195592710839267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10100308248521580562238045 3787615593195592710839267)
                      ·
                        rfl

theorem cell23_7376355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_7376355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376355 prefixEnd_7376355 := by exact prefixLift 7376355
  have htrace : WordTrace (prefixWord ++ tailWord_7376355) baseStart_7376355 baseEnd_7376355 := by
    simpa [prefixWord, tailWord_7376355, baseEnd_7376355] using wordTrace_append hprefix tailTrace_7376355
  have hstable : (prefixWord ++ tailWord_7376355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376355).length < 2 ^ (prefixWord ++ tailWord_7376355).sum := by decide
  have hdescent : baseEnd_7376355 < baseStart_7376355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376378 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2]
def baseStart_7376378 : Nat := 118140960795 + 7376378 * 2 ^ 59
def prefixEnd_7376378 : Nat := 4983230072969 + 3 ^ 40 * 7376378 * 2
def baseEnd_7376378 : Nat := 3787627403250646120851661

theorem tailTrace_7376378 : CollatzResearch.WordTrace tailWord_7376378 prefixEnd_7376378 3787627403250646120851661 := by
  unfold tailWord_7376378
  simp only [CollatzResearch.WordTrace]
  refine ⟨67259652017662441477724447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179359072047099843940598525 67259652017662441477724447)
  ·
    refine ⟨100889478026493662216586671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67259652017662441477724447 100889478026493662216586671)
    ·
      refine ⟨151334217039740493324880007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100889478026493662216586671 151334217039740493324880007)
      ·
        refine ⟨227001325559610739987320011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151334217039740493324880007 227001325559610739987320011)
        ·
          refine ⟨340501988339416109980980017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227001325559610739987320011 340501988339416109980980017)
          ·
            refine ⟨255376491254562082485735013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340501988339416109980980017 255376491254562082485735013)
            ·
              refine ⟨47883092110230390466075315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255376491254562082485735013 47883092110230390466075315)
              ·
                refine ⟨71824638165345585699112973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47883092110230390466075315 71824638165345585699112973)
                ·
                  refine ⟨26934239312004594637167365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71824638165345585699112973 26934239312004594637167365)
                  ·
                    refine ⟨5050169871000861494468881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26934239312004594637167365 5050169871000861494468881)
                    ·
                      refine ⟨3787627403250646120851661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050169871000861494468881 3787627403250646120851661)
                      ·
                        rfl

theorem cell23_7376378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_7376378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376378 prefixEnd_7376378 := by exact prefixLift 7376378
  have htrace : WordTrace (prefixWord ++ tailWord_7376378) baseStart_7376378 baseEnd_7376378 := by
    simpa [prefixWord, tailWord_7376378, baseEnd_7376378] using wordTrace_append hprefix tailTrace_7376378
  have hstable : (prefixWord ++ tailWord_7376378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376378).length < 2 ^ (prefixWord ++ tailWord_7376378).sum := by decide
  have hdescent : baseEnd_7376378 < baseStart_7376378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376381 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_7376381 : Nat := 118140960795 + 7376381 * 2 ^ 59
def prefixEnd_7376381 : Nat := 4983230072969 + 3 ^ 40 * 7376381 * 2
def baseEnd_7376381 : Nat := 3787628943692609609114147

theorem tailTrace_7376381 : CollatzResearch.WordTrace tailWord_7376381 prefixEnd_7376381 3787628943692609609114147 := by
  unfold tailWord_7376381
  simp only [CollatzResearch.WordTrace]
  refine ⟨269038717489638897423256997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179359144993092598282171331 269038717489638897423256997)
  ·
    refine ⟨50444759529307293266860687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269038717489638897423256997 50444759529307293266860687)
    ·
      refine ⟨75667139293960939900291031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50444759529307293266860687 75667139293960939900291031)
      ·
        refine ⟨113500708940941409850436547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75667139293960939900291031 113500708940941409850436547)
        ·
          refine ⟨170251063411412114775654821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113500708940941409850436547 170251063411412114775654821)
          ·
            refine ⟨31922074389639771520435279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170251063411412114775654821 31922074389639771520435279)
            ·
              refine ⟨47883111584459657280652919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31922074389639771520435279 47883111584459657280652919)
              ·
                refine ⟨71824667376689485920979379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47883111584459657280652919 71824667376689485920979379)
                ·
                  refine ⟨107737001065034228881469069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71824667376689485920979379 107737001065034228881469069)
                  ·
                    refine ⟨40401375399387835830550901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107737001065034228881469069 40401375399387835830550901)
                    ·
                      refine ⟨3787628943692609609114147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40401375399387835830550901 3787628943692609609114147)
                      ·
                        rfl

theorem cell23_7376381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_7376381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376381 prefixEnd_7376381 := by exact prefixLift 7376381
  have htrace : WordTrace (prefixWord ++ tailWord_7376381) baseStart_7376381 baseEnd_7376381 := by
    simpa [prefixWord, tailWord_7376381, baseEnd_7376381] using wordTrace_append hprefix tailTrace_7376381
  have hstable : (prefixWord ++ tailWord_7376381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376381).length < 2 ^ (prefixWord ++ tailWord_7376381).sum := by decide
  have hdescent : baseEnd_7376381 < baseStart_7376381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376390 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7376390 : Nat := 118140960795 + 7376390 * 2 ^ 59
def prefixEnd_7376390 : Nat := 4983230072969 + 3 ^ 40 * 7376390 * 2
def baseEnd_7376390 : Nat := 3787633565018500073901607

theorem tailTrace_7376390 : CollatzResearch.WordTrace tailWord_7376390 prefixEnd_7376390 3787633565018500073901607 := by
  unfold tailWord_7376390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407470179581446623760457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179359363831070861306889749 8407470179581446623760457)
  ·
    refine ⟨6305602634686084967820343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8407470179581446623760457 6305602634686084967820343)
    ·
      refine ⟨9458403952029127451730515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6305602634686084967820343 9458403952029127451730515)
      ·
        refine ⟨14187605928043691177595773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9458403952029127451730515 14187605928043691177595773)
        ·
          refine ⟨5320352223016384191598415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14187605928043691177595773 5320352223016384191598415)
          ·
            refine ⟨7980528334524576287397623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320352223016384191598415 7980528334524576287397623)
            ·
              refine ⟨11970792501786864431096435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980528334524576287397623 11970792501786864431096435)
              ·
                refine ⟨17956188752680296646644653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11970792501786864431096435 17956188752680296646644653)
                ·
                  refine ⟨6733570782255111242491745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17956188752680296646644653 6733570782255111242491745)
                  ·
                    refine ⟨5050178086691333431868809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733570782255111242491745 5050178086691333431868809)
                    ·
                      refine ⟨3787633565018500073901607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050178086691333431868809 3787633565018500073901607)
                      ·
                        rfl

theorem cell23_7376390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7376390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376390 prefixEnd_7376390 := by exact prefixLift 7376390
  have htrace : WordTrace (prefixWord ++ tailWord_7376390) baseStart_7376390 baseEnd_7376390 := by
    simpa [prefixWord, tailWord_7376390, baseEnd_7376390] using wordTrace_append hprefix tailTrace_7376390
  have hstable : (prefixWord ++ tailWord_7376390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376390).length < 2 ^ (prefixWord ++ tailWord_7376390).sum := by decide
  have hdescent : baseEnd_7376390 < baseStart_7376390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376412 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_7376412 : Nat := 118140960795 + 7376412 * 2 ^ 59
def prefixEnd_7376412 : Nat := 4983230072969 + 3 ^ 40 * 7376412 * 2
def baseEnd_7376412 : Nat := 3787644861592898987826505

theorem tailTrace_7376412 : CollatzResearch.WordTrace tailWord_7376412 prefixEnd_7376412 3787644861592898987826505 := by
  unfold tailWord_7376412
  simp only [CollatzResearch.WordTrace]
  refine ⟨134519924076263294858817745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179359898768351059811756993 134519924076263294858817745)
  ·
    refine ⟨100889943057197471144113309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134519924076263294858817745 100889943057197471144113309)
    ·
      refine ⟨37833728646449051679042491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100889943057197471144113309 37833728646449051679042491)
      ·
        refine ⟨56750592969673577518563737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37833728646449051679042491 56750592969673577518563737)
        ·
          refine ⟨42562944727255183138922803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56750592969673577518563737 42562944727255183138922803)
          ·
            refine ⟨63844417090882774708384205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42562944727255183138922803 63844417090882774708384205)
            ·
              refine ⟨23941656409081040515644077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63844417090882774708384205 23941656409081040515644077)
              ·
                refine ⟨8978121153405390193366529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23941656409081040515644077 8978121153405390193366529)
                ·
                  refine ⟨6733590865054042645024897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8978121153405390193366529 6733590865054042645024897)
                  ·
                    refine ⟨5050193148790531983768673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733590865054042645024897 5050193148790531983768673)
                    ·
                      refine ⟨3787644861592898987826505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050193148790531983768673 3787644861592898987826505)
                      ·
                        rfl

theorem cell23_7376412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_7376412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376412 prefixEnd_7376412 := by exact prefixLift 7376412
  have htrace : WordTrace (prefixWord ++ tailWord_7376412) baseStart_7376412 baseEnd_7376412 := by
    simpa [prefixWord, tailWord_7376412, baseEnd_7376412] using wordTrace_append hprefix tailTrace_7376412
  have hstable : (prefixWord ++ tailWord_7376412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376412).length < 2 ^ (prefixWord ++ tailWord_7376412).sum := by decide
  have hdescent : baseEnd_7376412 < baseStart_7376412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376451 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4]
def baseStart_7376451 : Nat := 118140960795 + 7376451 * 2 ^ 59
def prefixEnd_7376451 : Nat := 4983230072969 + 3 ^ 40 * 7376451 * 2
def baseEnd_7376451 : Nat := 3787664887338424335238825

theorem tailTrace_7376451 : CollatzResearch.WordTrace tailWord_7376451 prefixEnd_7376451 3787664887338424335238825 := by
  unfold tailWord_7376451
  simp only [CollatzResearch.WordTrace]
  refine ⟨269041270599385299378305207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179360847066256866252203471 269041270599385299378305207)
  ·
    refine ⟨403561905899077949067457811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269041270599385299378305207 403561905899077949067457811)
    ·
      refine ⟨605342858848616923601186717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403561905899077949067457811 605342858848616923601186717)
      ·
        refine ⟨227003572068231346350445019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605342858848616923601186717 227003572068231346350445019)
        ·
          refine ⟨340505358102347019525667529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227003572068231346350445019 340505358102347019525667529)
          ·
            refine ⟨255379018576760264644250647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340505358102347019525667529 255379018576760264644250647)
            ·
              refine ⟨383068527865140396966375971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255379018576760264644250647 383068527865140396966375971)
              ·
                refine ⟨574602791797710595449563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383068527865140396966375971 574602791797710595449563957)
                ·
                  refine ⟨53869011731035368323396621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 574602791797710595449563957 53869011731035368323396621)
                  ·
                    refine ⟨20200879399138263121273733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53869011731035368323396621 20200879399138263121273733)
                    ·
                      refine ⟨3787664887338424335238825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20200879399138263121273733 3787664887338424335238825)
                      ·
                        rfl

theorem cell23_7376451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_7376451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376451 prefixEnd_7376451 := by exact prefixLift 7376451
  have htrace : WordTrace (prefixWord ++ tailWord_7376451) baseStart_7376451 baseEnd_7376451 := by
    simpa [prefixWord, tailWord_7376451, baseEnd_7376451] using wordTrace_append hprefix tailTrace_7376451
  have hstable : (prefixWord ++ tailWord_7376451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376451).length < 2 ^ (prefixWord ++ tailWord_7376451).sum := by decide
  have hdescent : baseEnd_7376451 < baseStart_7376451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376468 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_7376468 : Nat := 118140960795 + 7376468 * 2 ^ 59
def prefixEnd_7376468 : Nat := 4983230072969 + 3 ^ 40 * 7376468 * 2
def baseEnd_7376468 : Nat := 3787673616509550768726247

theorem tailTrace_7376468 : CollatzResearch.WordTrace tailWord_7376468 prefixEnd_7376468 3787673616509550768726247 := by
  unfold tailWord_7376468
  simp only [CollatzResearch.WordTrace]
  refine ⟨134520945320161855640837029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179361260426882474187782705 134520945320161855640837029)
  ·
    refine ⟨25222677247530347932656943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134520945320161855640837029 25222677247530347932656943)
    ·
      refine ⟨37834015871295521898985415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25222677247530347932656943 37834015871295521898985415)
      ·
        refine ⟨56751023806943282848478123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37834015871295521898985415 56751023806943282848478123)
        ·
          refine ⟨85126535710414924272717185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56751023806943282848478123 85126535710414924272717185)
          ·
            refine ⟨63844901782811193204537889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85126535710414924272717185 63844901782811193204537889)
            ·
              refine ⟨47883676337108394903403417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63844901782811193204537889 47883676337108394903403417)
              ·
                refine ⟨35912757252831296177552563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47883676337108394903403417 35912757252831296177552563)
                ·
                  refine ⟨53869135879246944266328845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35912757252831296177552563 53869135879246944266328845)
                  ·
                    refine ⟨20200925954717604099873317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53869135879246944266328845 20200925954717604099873317)
                    ·
                      refine ⟨3787673616509550768726247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20200925954717604099873317 3787673616509550768726247)
                      ·
                        rfl

theorem cell23_7376468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_7376468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376468 prefixEnd_7376468 := by exact prefixLift 7376468
  have htrace : WordTrace (prefixWord ++ tailWord_7376468) baseStart_7376468 baseEnd_7376468 := by
    simpa [prefixWord, tailWord_7376468, baseEnd_7376468] using wordTrace_append hprefix tailTrace_7376468
  have hstable : (prefixWord ++ tailWord_7376468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376468).length < 2 ^ (prefixWord ++ tailWord_7376468).sum := by decide
  have hdescent : baseEnd_7376468 < baseStart_7376468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376485 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_7376485 : Nat := 118140960795 + 7376485 * 2 ^ 59
def prefixEnd_7376485 : Nat := 4983230072969 + 3 ^ 40 * 7376485 * 2
def baseEnd_7376485 : Nat := 3787682345680677202213669

theorem tailTrace_7376485 : CollatzResearch.WordTrace tailWord_7376485 prefixEnd_7376485 3787682345680677202213669 := by
  unfold tailWord_7376485
  simp only [CollatzResearch.WordTrace]
  refine ⟨269042510681262123185042909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179361673787508082123361939 269042510681262123185042909)
  ·
    refine ⟨100890941505473296194391091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269042510681262123185042909 100890941505473296194391091)
    ·
      refine ⟨151336412258209944291586637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100890941505473296194391091 151336412258209944291586637)
      ·
        refine ⟨56751154596828729109344989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151336412258209944291586637 56751154596828729109344989)
        ·
          refine ⟨21281682973810773416004371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56751154596828729109344989 21281682973810773416004371)
          ·
            refine ⟨31922524460716160124006557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21281682973810773416004371 31922524460716160124006557)
            ·
              refine ⟨11970946672768560046502459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31922524460716160124006557 11970946672768560046502459)
              ·
                refine ⟨17956420009152840069753689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11970946672768560046502459 17956420009152840069753689)
                ·
                  refine ⟨13467315006864630052315267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17956420009152840069753689 13467315006864630052315267)
                  ·
                    refine ⟨20200972510296945078472901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13467315006864630052315267 20200972510296945078472901)
                    ·
                      refine ⟨3787682345680677202213669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20200972510296945078472901 3787682345680677202213669)
                      ·
                        rfl

theorem cell23_7376485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_7376485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376485 prefixEnd_7376485 := by exact prefixLift 7376485
  have htrace : WordTrace (prefixWord ++ tailWord_7376485) baseStart_7376485 baseEnd_7376485 := by
    simpa [prefixWord, tailWord_7376485, baseEnd_7376485] using wordTrace_append hprefix tailTrace_7376485
  have hstable : (prefixWord ++ tailWord_7376485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376485).length < 2 ^ (prefixWord ++ tailWord_7376485).sum := by decide
  have hdescent : baseEnd_7376485 < baseStart_7376485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376498 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_7376498 : Nat := 118140960795 + 7376498 * 2 ^ 59
def prefixEnd_7376498 : Nat := 4983230072969 + 3 ^ 40 * 7376498 * 2
def baseEnd_7376498 : Nat := 3787689020929185651351109

theorem tailTrace_7376498 : CollatzResearch.WordTrace tailWord_7376498 prefixEnd_7376498 3787689020929185651351109 := by
  unfold tailWord_7376498
  simp only [CollatzResearch.WordTrace]
  refine ⟨67260746207553756601316537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179361989886810017603510765 67260746207553756601316537)
  ·
    refine ⟨50445559655665317450987403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67260746207553756601316537 50445559655665317450987403)
    ·
      refine ⟨75668339483497976176481105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50445559655665317450987403 75668339483497976176481105)
      ·
        refine ⟨56751254612623482132360829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75668339483497976176481105 56751254612623482132360829)
        ·
          refine ⟨21281720479733805799635311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56751254612623482132360829 21281720479733805799635311)
          ·
            refine ⟨31922580719600708699452967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21281720479733805799635311 31922580719600708699452967)
            ·
              refine ⟨47883871079401063049179451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31922580719600708699452967 47883871079401063049179451)
              ·
                refine ⟨71825806619101594573769177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47883871079401063049179451 71825806619101594573769177)
                ·
                  refine ⟨53869354964326195930326883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71825806619101594573769177 53869354964326195930326883)
                  ·
                    refine ⟨80804032446489293895490325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53869354964326195930326883 80804032446489293895490325)
                    ·
                      refine ⟨3787689020929185651351109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80804032446489293895490325 3787689020929185651351109)
                      ·
                        rfl

theorem cell23_7376498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_7376498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376498 prefixEnd_7376498 := by exact prefixLift 7376498
  have htrace : WordTrace (prefixWord ++ tailWord_7376498) baseStart_7376498 baseEnd_7376498 := by
    simpa [prefixWord, tailWord_7376498, baseEnd_7376498] using wordTrace_append hprefix tailTrace_7376498
  have hstable : (prefixWord ++ tailWord_7376498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376498).length < 2 ^ (prefixWord ++ tailWord_7376498).sum := by decide
  have hdescent : baseEnd_7376498 < baseStart_7376498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376502 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7376502 : Nat := 118140960795 + 7376502 * 2 ^ 59
def prefixEnd_7376502 : Nat := 4983230072969 + 3 ^ 40 * 7376502 * 2
def baseEnd_7376502 : Nat := 3787691074851803635701091

theorem tailTrace_7376502 : CollatzResearch.WordTrace tailWord_7376502 prefixEnd_7376502 3787691074851803635701091 := by
  unfold tailWord_7376502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16815195670137533443025735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179362087148133690058941173 16815195670137533443025735)
  ·
    refine ⟨25222793505206300164538603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16815195670137533443025735 25222793505206300164538603)
    ·
      refine ⟨37834190257809450246807905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25222793505206300164538603 37834190257809450246807905)
      ·
        refine ⟨28375642693357087685105929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37834190257809450246807905 28375642693357087685105929)
        ·
          refine ⟨21281732020017815763829447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28375642693357087685105929 21281732020017815763829447)
          ·
            refine ⟨31922598030026723645744171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21281732020017815763829447 31922598030026723645744171)
            ·
              refine ⟨47883897045040085468616257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31922598030026723645744171 47883897045040085468616257)
              ·
                refine ⟨35912922783780064101462193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47883897045040085468616257 35912922783780064101462193)
                ·
                  refine ⟨26934692087835048076096645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35912922783780064101462193 26934692087835048076096645)
                  ·
                    refine ⟨5050254766469071514268121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26934692087835048076096645 5050254766469071514268121)
                    ·
                      refine ⟨3787691074851803635701091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050254766469071514268121 3787691074851803635701091)
                      ·
                        rfl

theorem cell23_7376502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7376502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376502 prefixEnd_7376502 := by exact prefixLift 7376502
  have htrace : WordTrace (prefixWord ++ tailWord_7376502) baseStart_7376502 baseEnd_7376502 := by
    simpa [prefixWord, tailWord_7376502, baseEnd_7376502] using wordTrace_append hprefix tailTrace_7376502
  have hstable : (prefixWord ++ tailWord_7376502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376502).length < 2 ^ (prefixWord ++ tailWord_7376502).sum := by decide
  have hdescent : baseEnd_7376502 < baseStart_7376502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376589 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7376589 : Nat := 118140960795 + 7376589 * 2 ^ 59
def prefixEnd_7376589 : Nat := 4983230072969 + 3 ^ 40 * 7376589 * 2
def baseEnd_7376589 : Nat := 1262578582556248265104397

theorem tailTrace_7376589 : CollatzResearch.WordTrace tailWord_7376589 prefixEnd_7376589 1262578582556248265104397 := by
  unfold tailWord_7376589
  simp only [CollatzResearch.WordTrace]
  refine ⟨269046303872885348946828821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179364202581923565964552547 269046303872885348946828821)
  ·
    refine ⟨12611545494041500731882601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269046303872885348946828821 12611545494041500731882601)
    ·
      refine ⟨9458659120531125548911951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12611545494041500731882601 9458659120531125548911951)
      ·
        refine ⟨14187988680796688323367927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9458659120531125548911951 14187988680796688323367927)
        ·
          refine ⟨21281983021195032485051891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14187988680796688323367927 21281983021195032485051891)
          ·
            refine ⟨31922974531792548727577837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21281983021195032485051891 31922974531792548727577837)
            ·
              refine ⟨11971115449422205772841689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31922974531792548727577837 11971115449422205772841689)
              ·
                refine ⟨8978336587066654329631267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971115449422205772841689 8978336587066654329631267)
                ·
                  refine ⟨13467504880599981494446901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978336587066654329631267 13467504880599981494446901)
                  ·
                    refine ⟨1262578582556248265104397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13467504880599981494446901 1262578582556248265104397)
                    ·
                      rfl

theorem cell23_7376589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7376589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376589 prefixEnd_7376589 := by exact prefixLift 7376589
  have htrace : WordTrace (prefixWord ++ tailWord_7376589) baseStart_7376589 baseEnd_7376589 := by
    simpa [prefixWord, tailWord_7376589, baseEnd_7376589] using wordTrace_append hprefix tailTrace_7376589
  have hstable : (prefixWord ++ tailWord_7376589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376589).length < 2 ^ (prefixWord ++ tailWord_7376589).sum := by decide
  have hdescent : baseEnd_7376589 < baseStart_7376589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376609 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_7376609 : Nat := 118140960795 + 7376609 * 2 ^ 59
def prefixEnd_7376609 : Nat := 4983230072969 + 3 ^ 40 * 7376609 * 2
def baseEnd_7376609 : Nat := 3787746017281834717063099

theorem tailTrace_7376609 : CollatzResearch.WordTrace tailWord_7376609 prefixEnd_7376609 3787746017281834717063099 := by
  unfold tailWord_7376609
  simp only [CollatzResearch.WordTrace]
  refine ⟨269047033332812892362556881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179364688888541928241704587 269047033332812892362556881)
  ·
    refine ⟨201785274999609669271917661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269047033332812892362556881 201785274999609669271917661)
    ·
      refine ⟨75669478124853625976969123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201785274999609669271917661 75669478124853625976969123)
      ·
        refine ⟨113504217187280438965453685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75669478124853625976969123 113504217187280438965453685)
        ·
          refine ⟨10641020361307541153011283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113504217187280438965453685 10641020361307541153011283)
          ·
            refine ⟨15961530541961311729516925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641020361307541153011283 15961530541961311729516925)
            ·
              refine ⟨5985573953235491898568847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15961530541961311729516925 5985573953235491898568847)
              ·
                refine ⟨8978360929853237847853271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985573953235491898568847 8978360929853237847853271)
                ·
                  refine ⟨13467541394779856771779907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978360929853237847853271 13467541394779856771779907)
                  ·
                    refine ⟨20201312092169785157669861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13467541394779856771779907 20201312092169785157669861)
                    ·
                      refine ⟨3787746017281834717063099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20201312092169785157669861 3787746017281834717063099)
                      ·
                        rfl

theorem cell23_7376609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_7376609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376609 prefixEnd_7376609 := by exact prefixLift 7376609
  have htrace : WordTrace (prefixWord ++ tailWord_7376609) baseStart_7376609 baseEnd_7376609 := by
    simpa [prefixWord, tailWord_7376609, baseEnd_7376609] using wordTrace_append hprefix tailTrace_7376609
  have hstable : (prefixWord ++ tailWord_7376609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376609).length < 2 ^ (prefixWord ++ tailWord_7376609).sum := by decide
  have hdescent : baseEnd_7376609 < baseStart_7376609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376615 : List Nat := [1, 1, 5, 4, 1, 11]
def baseStart_7376615 : Nat := 118140960795 + 7376615 * 2 ^ 59
def prefixEnd_7376615 : Nat := 4983230072969 + 3 ^ 40 * 7376615 * 2
def baseEnd_7376615 : Nat := 15587444848418772401597

theorem tailTrace_7376615 : CollatzResearch.WordTrace tailWord_7376615 prefixEnd_7376615 15587444848418772401597 := by
  unfold tailWord_7376615
  simp only [CollatzResearch.WordTrace]
  refine ⟨269047252170791155387275299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179364834780527436924850199 269047252170791155387275299)
  ·
    refine ⟨403570878256186733080912949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269047252170791155387275299 403570878256186733080912949)
    ·
      refine ⟨37834769836517506226335589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403570878256186733080912949 37834769836517506226335589)
      ·
        refine ⟨7094019344347032417437923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37834769836517506226335589 7094019344347032417437923)
        ·
          refine ⟨10641029016520548626156885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094019344347032417437923 10641029016520548626156885)
          ·
            refine ⟨15587444848418772401597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10641029016520548626156885 15587444848418772401597)
            ·
              rfl

theorem cell23_7376615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 11].length) (baseStart_7376615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376615 prefixEnd_7376615 := by exact prefixLift 7376615
  have htrace : WordTrace (prefixWord ++ tailWord_7376615) baseStart_7376615 baseEnd_7376615 := by
    simpa [prefixWord, tailWord_7376615, baseEnd_7376615] using wordTrace_append hprefix tailTrace_7376615
  have hstable : (prefixWord ++ tailWord_7376615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376615).length < 2 ^ (prefixWord ++ tailWord_7376615).sum := by decide
  have hdescent : baseEnd_7376615 < baseStart_7376615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376626 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7376626 : Nat := 118140960795 + 7376626 * 2 ^ 59
def prefixEnd_7376626 : Nat := 4983230072969 + 3 ^ 40 * 7376626 * 2
def baseEnd_7376626 : Nat := 3787754746452961150550521

theorem tailTrace_7376626 : CollatzResearch.WordTrace tailWord_7376626 prefixEnd_7376626 3787754746452961150550521 := by
  unfold tailWord_7376626
  simp only [CollatzResearch.WordTrace]
  refine ⟨67261913343437826066481433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179365102249167536177283821 67261913343437826066481433)
  ·
    refine ⟨50446435007578369549861075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67261913343437826066481433 50446435007578369549861075)
    ·
      refine ⟨75669652511367554324791613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50446435007578369549861075 75669652511367554324791613)
      ·
        refine ⟨28376119691762832871796855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75669652511367554324791613 28376119691762832871796855)
        ·
          refine ⟨42564179537644249307695283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28376119691762832871796855 42564179537644249307695283)
          ·
            refine ⟨63846269306466373961542925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42564179537644249307695283 63846269306466373961542925)
            ·
              refine ⟨23942350989924890235578597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63846269306466373961542925 23942350989924890235578597)
              ·
                refine ⟨4489190810610916919170987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23942350989924890235578597 4489190810610916919170987)
                ·
                  refine ⟨6733786215916375378756481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489190810610916919170987 6733786215916375378756481)
                  ·
                    refine ⟨5050339661937281534067361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733786215916375378756481 5050339661937281534067361)
                    ·
                      refine ⟨3787754746452961150550521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050339661937281534067361 3787754746452961150550521)
                      ·
                        rfl

theorem cell23_7376626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7376626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376626 prefixEnd_7376626 := by exact prefixLift 7376626
  have htrace : WordTrace (prefixWord ++ tailWord_7376626) baseStart_7376626 baseEnd_7376626 := by
    simpa [prefixWord, tailWord_7376626, baseEnd_7376626] using wordTrace_append hprefix tailTrace_7376626
  have hstable : (prefixWord ++ tailWord_7376626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376626).length < 2 ^ (prefixWord ++ tailWord_7376626).sum := by decide
  have hdescent : baseEnd_7376626 < baseStart_7376626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376652 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 3, 3, 2]
def baseStart_7376652 : Nat := 118140960795 + 7376652 * 2 ^ 59
def prefixEnd_7376652 : Nat := 4983230072969 + 3 ^ 40 * 7376652 * 2
def baseEnd_7376652 : Nat := 3787768096949978048825401

theorem tailTrace_7376652 : CollatzResearch.WordTrace tailWord_7376652 prefixEnd_7376652 3787768096949978048825401 := by
  unfold tailWord_7376652
  simp only [CollatzResearch.WordTrace]
  refine ⟨134524300835828555353186105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179365734447771407137581473 134524300835828555353186105)
  ·
    refine ⟨100893225626871416514889579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134524300835828555353186105 100893225626871416514889579)
    ·
      refine ⟨151339838440307124772334369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100893225626871416514889579 151339838440307124772334369)
      ·
        refine ⟨113504878830230343579250777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151339838440307124772334369 113504878830230343579250777)
        ·
          refine ⟨85128659122672757684438083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113504878830230343579250777 85128659122672757684438083)
          ·
            refine ⟨127692988684009136526657125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85128659122672757684438083 127692988684009136526657125)
            ·
              refine ⟨23942435378251713098748211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127692988684009136526657125 23942435378251713098748211)
              ·
                refine ⟨35913653067377569648122317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23942435378251713098748211 35913653067377569648122317)
                ·
                  refine ⟨13467619900266588618045869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35913653067377569648122317 13467619900266588618045869)
                  ·
                    refine ⟨5050357462599970731767201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13467619900266588618045869 5050357462599970731767201)
                    ·
                      refine ⟨3787768096949978048825401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050357462599970731767201 3787768096949978048825401)
                      ·
                        rfl

theorem cell23_7376652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_7376652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376652 prefixEnd_7376652 := by exact prefixLift 7376652
  have htrace : WordTrace (prefixWord ++ tailWord_7376652) baseStart_7376652 baseEnd_7376652 := by
    simpa [prefixWord, tailWord_7376652, baseEnd_7376652] using wordTrace_append hprefix tailTrace_7376652
  have hstable : (prefixWord ++ tailWord_7376652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376652).length < 2 ^ (prefixWord ++ tailWord_7376652).sum := by decide
  have hdescent : baseEnd_7376652 < baseStart_7376652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376660 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7376660 : Nat := 118140960795 + 7376660 * 2 ^ 59
def prefixEnd_7376660 : Nat := 4983230072969 + 3 ^ 40 * 7376660 * 2
def baseEnd_7376660 : Nat := 3787772204795214017525365

theorem tailTrace_7376660 : CollatzResearch.WordTrace tailWord_7376660 prefixEnd_7376660 3787772204795214017525365 := by
  unfold tailWord_7376660
  simp only [CollatzResearch.WordTrace]
  refine ⟨134524446727814064036331717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179365928970418752048442289 134524446727814064036331717)
  ·
    refine ⟨25223333761465137006812197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134524446727814064036331717 25223333761465137006812197)
    ·
      refine ⟨4729375080274713188777287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25223333761465137006812197 4729375080274713188777287)
      ·
        refine ⟨7094062620412069783165931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729375080274713188777287 7094062620412069783165931)
        ·
          refine ⟨10641093930618104674748897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094062620412069783165931 10641093930618104674748897)
          ·
            refine ⟨7980820447963578506061673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10641093930618104674748897 7980820447963578506061673)
            ·
              refine ⟨5985615335972683879546255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980820447963578506061673 5985615335972683879546255)
              ·
                refine ⟨8978423003959025819319383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985615335972683879546255 8978423003959025819319383)
                ·
                  refine ⟨13467634505938538728979075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978423003959025819319383 13467634505938538728979075)
                  ·
                    refine ⟨20201451758907808093468613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13467634505938538728979075 20201451758907808093468613)
                    ·
                      refine ⟨3787772204795214017525365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20201451758907808093468613 3787772204795214017525365)
                      ·
                        rfl

theorem cell23_7376660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7376660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376660 prefixEnd_7376660 := by exact prefixLift 7376660
  have htrace : WordTrace (prefixWord ++ tailWord_7376660) baseStart_7376660 baseEnd_7376660 := by
    simpa [prefixWord, tailWord_7376660, baseEnd_7376660] using wordTrace_append hprefix tailTrace_7376660
  have hstable : (prefixWord ++ tailWord_7376660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376660).length < 2 ^ (prefixWord ++ tailWord_7376660).sum := by decide
  have hdescent : baseEnd_7376660 < baseStart_7376660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376665 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 8, 2]
def baseStart_7376665 : Nat := 118140960795 + 7376665 * 2 ^ 59
def prefixEnd_7376665 : Nat := 4983230072969 + 3 ^ 40 * 7376665 * 2
def baseEnd_7376665 : Nat := 3787774772198486497962841

theorem tailTrace_7376665 : CollatzResearch.WordTrace tailWord_7376665 prefixEnd_7376665 3787774772198486497962841 := by
  unfold tailWord_7376665
  simp only [CollatzResearch.WordTrace]
  refine ⟨269049075820610013926595449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179366050547073342617730299 269049075820610013926595449)
  ·
    refine ⟨201786806865457510444946587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269049075820610013926595449 201786806865457510444946587)
    ·
      refine ⟨302680210298186265667419881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201786806865457510444946587 302680210298186265667419881)
      ·
        refine ⟨227010157723639699250564911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302680210298186265667419881 227010157723639699250564911)
        ·
          refine ⟨340515236585459548875847367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227010157723639699250564911 340515236585459548875847367)
          ·
            refine ⟨510772854878189323313771051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340515236585459548875847367 510772854878189323313771051)
            ·
              refine ⟨766159282317283984970656577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510772854878189323313771051 766159282317283984970656577)
              ·
                refine ⟨574619461737962988727992433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766159282317283984970656577 574619461737962988727992433)
                ·
                  refine ⟨430964596303472241545994325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574619461737962988727992433 430964596303472241545994325)
                  ·
                    refine ⟨5050366362931315330617121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 430964596303472241545994325 5050366362931315330617121)
                    ·
                      refine ⟨3787774772198486497962841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050366362931315330617121 3787774772198486497962841)
                      ·
                        rfl

theorem cell23_7376665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_7376665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376665 prefixEnd_7376665 := by exact prefixLift 7376665
  have htrace : WordTrace (prefixWord ++ tailWord_7376665) baseStart_7376665 baseEnd_7376665 := by
    simpa [prefixWord, tailWord_7376665, baseEnd_7376665] using wordTrace_append hprefix tailTrace_7376665
  have hstable : (prefixWord ++ tailWord_7376665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376665).length < 2 ^ (prefixWord ++ tailWord_7376665).sum := by decide
  have hdescent : baseEnd_7376665 < baseStart_7376665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376670 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7376670 : Nat := 118140960795 + 7376670 * 2 ^ 59
def prefixEnd_7376670 : Nat := 4983230072969 + 3 ^ 40 * 7376670 * 2
def baseEnd_7376670 : Nat := 1262592446533919659466773

theorem tailTrace_7376670 : CollatzResearch.WordTrace tailWord_7376670 prefixEnd_7376670 1262592446533919659466773 := by
  unfold tailWord_7376670
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631157273198987472565933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179366172123727933187018309 33631157273198987472565933)
  ·
    refine ⟨12611683977449620302212225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33631157273198987472565933 12611683977449620302212225)
    ·
      refine ⟨9458762983087215226659169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12611683977449620302212225 9458762983087215226659169)
      ·
        refine ⟨7094072237315411419994377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9458762983087215226659169 7094072237315411419994377)
        ·
          refine ⟨5320554177986558564995783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7094072237315411419994377 5320554177986558564995783)
          ·
            refine ⟨7980831266979837847493675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320554177986558564995783 7980831266979837847493675)
            ·
              refine ⟨11971246900469756771240513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980831266979837847493675 11971246900469756771240513)
              ·
                refine ⟨8978435175352317578430385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971246900469756771240513 8978435175352317578430385)
                ·
                  refine ⟨6733826381514238183822789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8978435175352317578430385 6733826381514238183822789)
                  ·
                    refine ⟨1262592446533919659466773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6733826381514238183822789 1262592446533919659466773)
                    ·
                      rfl

theorem cell23_7376670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7376670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376670 prefixEnd_7376670 := by exact prefixLift 7376670
  have htrace : WordTrace (prefixWord ++ tailWord_7376670) baseStart_7376670 baseEnd_7376670 := by
    simpa [prefixWord, tailWord_7376670, baseEnd_7376670] using wordTrace_append hprefix tailTrace_7376670
  have hstable : (prefixWord ++ tailWord_7376670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376670).length < 2 ^ (prefixWord ++ tailWord_7376670).sum := by decide
  have hdescent : baseEnd_7376670 < baseStart_7376670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376676 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_7376676 : Nat := 118140960795 + 7376676 * 2 ^ 59
def prefixEnd_7376676 : Nat := 4983230072969 + 3 ^ 40 * 7376676 * 2
def baseEnd_7376676 : Nat := 3787780420485685954925291

theorem tailTrace_7376676 : CollatzResearch.WordTrace tailWord_7376676 prefixEnd_7376676 3787780420485685954925291 := by
  unfold tailWord_7376676
  simp only [CollatzResearch.WordTrace]
  refine ⟨134524738511785081402622941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179366318015713441870163921 134524738511785081402622941)
  ·
    refine ⟨50446776941919405525983603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134524738511785081402622941 50446776941919405525983603)
    ·
      refine ⟨75670165412879108288975405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50446776941919405525983603 75670165412879108288975405)
      ·
        refine ⟨28376312029829665608365777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75670165412879108288975405 28376312029829665608365777)
        ·
          refine ⟨21282234022372249206274333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28376312029829665608365777 21282234022372249206274333)
          ·
            refine ⟨7980837758389593452352875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21282234022372249206274333 7980837758389593452352875)
            ·
              refine ⟨11971256637584390178529313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980837758389593452352875 11971256637584390178529313)
              ·
                refine ⟨8978442478188292633896985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971256637584390178529313 8978442478188292633896985)
                ·
                  refine ⟨6733831858641219475422739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8978442478188292633896985 6733831858641219475422739)
                  ·
                    refine ⟨10100747787961829213134109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6733831858641219475422739 10100747787961829213134109)
                    ·
                      refine ⟨3787780420485685954925291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10100747787961829213134109 3787780420485685954925291)
                      ·
                        rfl

theorem cell23_7376676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_7376676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376676 prefixEnd_7376676 := by exact prefixLift 7376676
  have htrace : WordTrace (prefixWord ++ tailWord_7376676) baseStart_7376676 baseEnd_7376676 := by
    simpa [prefixWord, tailWord_7376676, baseEnd_7376676] using wordTrace_append hprefix tailTrace_7376676
  have hstable : (prefixWord ++ tailWord_7376676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376676).length < 2 ^ (prefixWord ++ tailWord_7376676).sum := by decide
  have hdescent : baseEnd_7376676 < baseStart_7376676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376692 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_7376692 : Nat := 118140960795 + 7376692 * 2 ^ 59
def prefixEnd_7376692 : Nat := 4983230072969 + 3 ^ 40 * 7376692 * 2
def baseEnd_7376692 : Nat := 1262596212058719297441739

theorem tailTrace_7376692 : CollatzResearch.WordTrace tailWord_7376692 prefixEnd_7376692 1262596212058719297441739 := by
  unfold tailWord_7376692
  simp only [CollatzResearch.WordTrace]
  refine ⟨134525030295756098768914165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179366707061008131691885553 134525030295756098768914165)
  ·
    refine ⟨12611721590227134259585703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134525030295756098768914165 12611721590227134259585703)
    ·
      refine ⟨18917582385340701389378555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12611721590227134259585703 18917582385340701389378555)
      ·
        refine ⟨28376373578011052084067833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18917582385340701389378555 28376373578011052084067833)
        ·
          refine ⟨21282280183508289063050875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28376373578011052084067833 21282280183508289063050875)
          ·
            refine ⟨31923420275262433594576313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21282280183508289063050875 31923420275262433594576313)
            ·
              refine ⟨23942565206446825195932235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31923420275262433594576313 23942565206446825195932235)
              ·
                refine ⟨35913847809670237793898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23942565206446825195932235 35913847809670237793898353)
                ·
                  refine ⟨26935385857252678345423765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35913847809670237793898353 26935385857252678345423765)
                  ·
                    refine ⟨1262596212058719297441739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26935385857252678345423765 1262596212058719297441739)
                    ·
                      rfl

theorem cell23_7376692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_7376692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376692 prefixEnd_7376692 := by exact prefixLift 7376692
  have htrace : WordTrace (prefixWord ++ tailWord_7376692) baseStart_7376692 baseEnd_7376692 := by
    simpa [prefixWord, tailWord_7376692, baseEnd_7376692] using wordTrace_append hprefix tailTrace_7376692
  have hstable : (prefixWord ++ tailWord_7376692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376692).length < 2 ^ (prefixWord ++ tailWord_7376692).sum := by decide
  have hdescent : baseEnd_7376692 < baseStart_7376692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376735 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 4, 5]
def baseStart_7376735 : Nat := 118140960795 + 7376735 * 2 ^ 59
def prefixEnd_7376735 : Nat := 4983230072969 + 3 ^ 40 * 7376735 * 2
def baseEnd_7376735 : Nat := 1262603571948100408029173

theorem tailTrace_7376735 : CollatzResearch.WordTrace tailWord_7376735 prefixEnd_7376735 1262603571948100408029173 := by
  unfold tailWord_7376735
  simp only [CollatzResearch.WordTrace]
  refine ⟨269051628930356415881643659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179367752620237610587762439 269051628930356415881643659)
  ·
    refine ⟨403577443395534623822465489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269051628930356415881643659 403577443395534623822465489)
    ·
      refine ⟨302683082546650967866849117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403577443395534623822465489 302683082546650967866849117)
      ·
        refine ⟨113506155954994112950068419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302683082546650967866849117 113506155954994112950068419)
        ·
          refine ⟨170259233932491169425102629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113506155954994112950068419 170259233932491169425102629)
          ·
            refine ⟨31923606362342094267206743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170259233932491169425102629 31923606362342094267206743)
            ·
              refine ⟨47885409543513141400810115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31923606362342094267206743 47885409543513141400810115)
              ·
                refine ⟨71828114315269712101215173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47885409543513141400810115 71828114315269712101215173)
                ·
                  refine ⟨13467771434113071018977845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71828114315269712101215173 13467771434113071018977845)
                  ·
                    refine ⟨1262603571948100408029173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13467771434113071018977845 1262603571948100408029173)
                    ·
                      rfl

theorem cell23_7376735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_7376735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376735 prefixEnd_7376735 := by exact prefixLift 7376735
  have htrace : WordTrace (prefixWord ++ tailWord_7376735) baseStart_7376735 baseEnd_7376735 := by
    simpa [prefixWord, tailWord_7376735, baseEnd_7376735] using wordTrace_append hprefix tailTrace_7376735
  have hstable : (prefixWord ++ tailWord_7376735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376735).length < 2 ^ (prefixWord ++ tailWord_7376735).sum := by decide
  have hdescent : baseEnd_7376735 < baseStart_7376735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376739 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 7]
def baseStart_7376739 : Nat := 118140960795 + 7376739 * 2 ^ 59
def prefixEnd_7376739 : Nat := 4983230072969 + 3 ^ 40 * 7376739 * 2
def baseEnd_7376739 : Nat := 420868085529657689826389

theorem tailTrace_7376739 : CollatzResearch.WordTrace tailWord_7376739 prefixEnd_7376739 420868085529657689826389 := by
  unfold tailWord_7376739
  simp only [CollatzResearch.WordTrace]
  refine ⟨269051774822341924564789271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179367849881561283043192847 269051774822341924564789271)
  ·
    refine ⟨403577662233512886847183907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269051774822341924564789271 403577662233512886847183907)
    ·
      refine ⟨605366493350269330270775861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403577662233512886847183907 605366493350269330270775861)
      ·
        refine ⟨56753108751587749712885237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 605366493350269330270775861 56753108751587749712885237)
        ·
          refine ⟨5320603945461351535582991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56753108751587749712885237 5320603945461351535582991)
          ·
            refine ⟨7980905918192027303374487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320603945461351535582991 7980905918192027303374487)
            ·
              refine ⟨11971358877288040955061731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980905918192027303374487 11971358877288040955061731)
              ·
                refine ⟨17957038315932061432592597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11971358877288040955061731 17957038315932061432592597)
                ·
                  refine ⟨420868085529657689826389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17957038315932061432592597 420868085529657689826389)
                  ·
                    rfl

theorem cell23_7376739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 7].length) (baseStart_7376739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376739 prefixEnd_7376739 := by exact prefixLift 7376739
  have htrace : WordTrace (prefixWord ++ tailWord_7376739) baseStart_7376739 baseEnd_7376739 := by
    simpa [prefixWord, tailWord_7376739, baseEnd_7376739] using wordTrace_append hprefix tailTrace_7376739
  have hstable : (prefixWord ++ tailWord_7376739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376739).length < 2 ^ (prefixWord ++ tailWord_7376739).sum := by decide
  have hdescent : baseEnd_7376739 < baseStart_7376739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376750 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7376750 : Nat := 118140960795 + 7376750 * 2 ^ 59
def prefixEnd_7376750 : Nat := 4983230072969 + 3 ^ 40 * 7376750 * 2
def baseEnd_7376750 : Nat := 3787818418054118665399951

theorem tailTrace_7376750 : CollatzResearch.WordTrace tailWord_7376750 prefixEnd_7376750 3787818418054118665399951 := by
  unfold tailWord_7376750
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631522003162759180429963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179368117350201382295626469 33631522003162759180429963)
  ·
    refine ⟨50447283004744138770644945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33631522003162759180429963 50447283004744138770644945)
    ·
      refine ⟨37835462253558104077983709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50447283004744138770644945 37835462253558104077983709)
      ·
        refine ⟨14188298345084289029243891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37835462253558104077983709 14188298345084289029243891)
        ·
          refine ⟨21282447517626433543865837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14188298345084289029243891 21282447517626433543865837)
          ·
            refine ⟨7980917819109912578949689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21282447517626433543865837 7980917819109912578949689)
            ·
              refine ⟨5985688364332434434212267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980917819109912578949689 5985688364332434434212267)
              ·
                refine ⟨8978532546498651651318401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985688364332434434212267 8978532546498651651318401)
                ·
                  refine ⟨6733899409873988738488801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8978532546498651651318401 6733899409873988738488801)
                  ·
                    refine ⟨5050424557405491553866601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733899409873988738488801 5050424557405491553866601)
                    ·
                      refine ⟨3787818418054118665399951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050424557405491553866601 3787818418054118665399951)
                      ·
                        rfl

theorem cell23_7376750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7376750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376750 prefixEnd_7376750 := by exact prefixLift 7376750
  have htrace : WordTrace (prefixWord ++ tailWord_7376750) baseStart_7376750 baseEnd_7376750 := by
    simpa [prefixWord, tailWord_7376750, baseEnd_7376750] using wordTrace_append hprefix tailTrace_7376750
  have hstable : (prefixWord ++ tailWord_7376750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376750).length < 2 ^ (prefixWord ++ tailWord_7376750).sum := by decide
  have hdescent : baseEnd_7376750 < baseStart_7376750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376755 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 4]
def baseStart_7376755 : Nat := 118140960795 + 7376755 * 2 ^ 59
def prefixEnd_7376755 : Nat := 4983230072969 + 3 ^ 40 * 7376755 * 2
def baseEnd_7376755 : Nat := 3787820985457391145837427

theorem tailTrace_7376755 : CollatzResearch.WordTrace tailWord_7376755 prefixEnd_7376755 3787820985457391145837427 := by
  unfold tailWord_7376755
  simp only [CollatzResearch.WordTrace]
  refine ⟨269052358390283959297371719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179368238926855972864914479 269052358390283959297371719)
  ·
    refine ⟨403578537585425938946057579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269052358390283959297371719 403578537585425938946057579)
    ·
      refine ⟨605367806378138908419086369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403578537585425938946057579 605367806378138908419086369)
      ·
        refine ⟨454025854783604181314314777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605367806378138908419086369 454025854783604181314314777)
        ·
          refine ⟨340519391087703135985736083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454025854783604181314314777 340519391087703135985736083)
          ·
            refine ⟨510779086631554703978604125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340519391087703135985736083 510779086631554703978604125)
            ·
              refine ⟨191542157486833013991976547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510779086631554703978604125 191542157486833013991976547)
              ·
                refine ⟨287313236230249520987964821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191542157486833013991976547 287313236230249520987964821)
                ·
                  refine ⟨13467807948292946296310851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287313236230249520987964821 13467807948292946296310851)
                  ·
                    refine ⟨20201711922439419444466277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13467807948292946296310851 20201711922439419444466277)
                    ·
                      refine ⟨3787820985457391145837427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20201711922439419444466277 3787820985457391145837427)
                      ·
                        rfl

theorem cell23_7376755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_7376755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376755 prefixEnd_7376755 := by exact prefixLift 7376755
  have htrace : WordTrace (prefixWord ++ tailWord_7376755) baseStart_7376755 baseEnd_7376755 := by
    simpa [prefixWord, tailWord_7376755, baseEnd_7376755] using wordTrace_append hprefix tailTrace_7376755
  have hstable : (prefixWord ++ tailWord_7376755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376755).length < 2 ^ (prefixWord ++ tailWord_7376755).sum := by decide
  have hdescent : baseEnd_7376755 < baseStart_7376755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376772 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7376772 : Nat := 118140960795 + 7376772 * 2 ^ 59
def prefixEnd_7376772 : Nat := 4983230072969 + 3 ^ 40 * 7376772 * 2
def baseEnd_7376772 : Nat := 3787829714628517579324849

theorem tailTrace_7376772 : CollatzResearch.WordTrace tailWord_7376772 prefixEnd_7376772 3787829714628517579324849 := by
  unfold tailWord_7376772
  simp only [CollatzResearch.WordTrace]
  refine ⟨134526489215611185600370285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179368652287481580800493713 134526489215611185600370285)
  ·
    refine ⟨50447433455854194600138857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134526489215611185600370285 50447433455854194600138857)
    ·
      refine ⟨37835575091890645950104143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50447433455854194600138857 37835575091890645950104143)
      ·
        refine ⟨56753362637835968925156215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37835575091890645950104143 56753362637835968925156215)
        ·
          refine ⟨85130043956753953387734323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56753362637835968925156215 85130043956753953387734323)
          ·
            refine ⟨127695065935130930081601485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85130043956753953387734323 127695065935130930081601485)
            ·
              refine ⟨47885649725674098780600557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127695065935130930081601485 47885649725674098780600557)
              ·
                refine ⟨17957118647127787042725209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47885649725674098780600557 17957118647127787042725209)
                ·
                  refine ⟨13467838985345840282043907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17957118647127787042725209 13467838985345840282043907)
                  ·
                    refine ⟨20201758478018760423065861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13467838985345840282043907 20201758478018760423065861)
                    ·
                      refine ⟨3787829714628517579324849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20201758478018760423065861 3787829714628517579324849)
                      ·
                        rfl

theorem cell23_7376772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7376772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376772 prefixEnd_7376772 := by exact prefixLift 7376772
  have htrace : WordTrace (prefixWord ++ tailWord_7376772) baseStart_7376772 baseEnd_7376772 := by
    simpa [prefixWord, tailWord_7376772, baseEnd_7376772] using wordTrace_append hprefix tailTrace_7376772
  have hstable : (prefixWord ++ tailWord_7376772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376772).length < 2 ^ (prefixWord ++ tailWord_7376772).sum := by decide
  have hdescent : baseEnd_7376772 < baseStart_7376772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376856 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 1, 1, 3]
def baseStart_7376856 : Nat := 118140960795 + 7376856 * 2 ^ 59
def prefixEnd_7376856 : Nat := 4983230072969 + 3 ^ 40 * 7376856 * 2
def baseEnd_7376856 : Nat := 3787872847003495250674463

theorem tailTrace_7376856 : CollatzResearch.WordTrace tailWord_7376856 prefixEnd_7376856 3787872847003495250674463 := by
  unfold tailWord_7376856
  simp only [CollatzResearch.WordTrace]
  refine ⟨134528021081459026773399211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179370694775278702364532281 134528021081459026773399211)
  ·
    refine ⟨201792031622188540160098817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134528021081459026773399211 201792031622188540160098817)
    ·
      refine ⟨151344023716641405120074113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201792031622188540160098817 151344023716641405120074113)
      ·
        refine ⟨113508017787481053840055585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151344023716641405120074113 113508017787481053840055585)
        ·
          refine ⟨85131013340610790380041689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113508017787481053840055585 85131013340610790380041689)
          ·
            refine ⟨63848260005458092785031267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85131013340610790380041689 63848260005458092785031267)
            ·
              refine ⟨95772390008187139177546901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63848260005458092785031267 95772390008187139177546901)
              ·
                refine ⟨4489330781633772148947511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95772390008187139177546901 4489330781633772148947511)
                ·
                  refine ⟨6733996172450658223421267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489330781633772148947511 6733996172450658223421267)
                  ·
                    refine ⟨10100994258675987335131901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6733996172450658223421267 10100994258675987335131901)
                    ·
                      refine ⟨3787872847003495250674463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10100994258675987335131901 3787872847003495250674463)
                      ·
                        rfl

theorem cell23_7376856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_7376856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376856 prefixEnd_7376856 := by exact prefixLift 7376856
  have htrace : WordTrace (prefixWord ++ tailWord_7376856) baseStart_7376856 baseEnd_7376856 := by
    simpa [prefixWord, tailWord_7376856, baseEnd_7376856] using wordTrace_append hprefix tailTrace_7376856
  have hstable : (prefixWord ++ tailWord_7376856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376856).length < 2 ^ (prefixWord ++ tailWord_7376856).sum := by decide
  have hdescent : baseEnd_7376856 < baseStart_7376856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376879 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 4]
def baseStart_7376879 : Nat := 118140960795 + 7376879 * 2 ^ 59
def prefixEnd_7376879 : Nat := 4983230072969 + 3 ^ 40 * 7376879 * 2
def baseEnd_7376879 : Nat := 3787884657058548660686857

theorem tailTrace_7376879 : CollatzResearch.WordTrace tailWord_7376879 prefixEnd_7376879 3787884657058548660686857 := by
  unfold tailWord_7376879
  simp only [CollatzResearch.WordTrace]
  refine ⟨269056881041834728474885691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179371254027889818983257127 269056881041834728474885691)
  ·
    refine ⟨403585321562752092712328537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269056881041834728474885691 403585321562752092712328537)
    ·
      refine ⟨302688991172064069534246403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403585321562752092712328537 302688991172064069534246403)
      ·
        refine ⟨454033486758096104301369605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302688991172064069534246403 454033486758096104301369605)
        ·
          refine ⟨85131278767143019556506801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454033486758096104301369605 85131278767143019556506801)
          ·
            refine ⟨63848459075357264667380101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85131278767143019556506801 63848459075357264667380101)
            ·
              refine ⟨11971586076629487125133769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63848459075357264667380101 11971586076629487125133769)
              ·
                refine ⟨8978689557472115343850327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971586076629487125133769 8978689557472115343850327)
                ·
                  refine ⟨13468034336208173015775491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978689557472115343850327 13468034336208173015775491)
                  ·
                    refine ⟨20202051504312259523663237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13468034336208173015775491 20202051504312259523663237)
                    ·
                      refine ⟨3787884657058548660686857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20202051504312259523663237 3787884657058548660686857)
                      ·
                        rfl

theorem cell23_7376879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_7376879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376879 prefixEnd_7376879 := by exact prefixLift 7376879
  have htrace : WordTrace (prefixWord ++ tailWord_7376879) baseStart_7376879 baseEnd_7376879 := by
    simpa [prefixWord, tailWord_7376879, baseEnd_7376879] using wordTrace_append hprefix tailTrace_7376879
  have hstable : (prefixWord ++ tailWord_7376879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376879).length < 2 ^ (prefixWord ++ tailWord_7376879).sum := by decide
  have hdescent : baseEnd_7376879 < baseStart_7376879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376892 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7376892 : Nat := 118140960795 + 7376892 * 2 ^ 59
def prefixEnd_7376892 : Nat := 4983230072969 + 3 ^ 40 * 7376892 * 2
def baseEnd_7376892 : Nat := 3787891332307057109824297

theorem tailTrace_7376892 : CollatzResearch.WordTrace tailWord_7376892 prefixEnd_7376892 3787891332307057109824297 := by
  unfold tailWord_7376892
  simp only [CollatzResearch.WordTrace]
  refine ⟨134528677595393815847554465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179371570127191754463405953 134528677595393815847554465)
  ·
    refine ⟨100896508196545361885665849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134528677595393815847554465 100896508196545361885665849)
    ·
      refine ⟨75672381147409021414249387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100896508196545361885665849 75672381147409021414249387)
      ·
        refine ⟨113508571721113532121374081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75672381147409021414249387 113508571721113532121374081)
        ·
          refine ⟨85131428790835149091030561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113508571721113532121374081 85131428790835149091030561)
          ·
            refine ⟨63848571593126361818272921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85131428790835149091030561 63848571593126361818272921)
            ·
              refine ⟨47886428694844771363704691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63848571593126361818272921 47886428694844771363704691)
              ·
                refine ⟨71829643042267157045557037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47886428694844771363704691 71829643042267157045557037)
                ·
                  refine ⟨26936116140850183892083889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71829643042267157045557037 26936116140850183892083889)
                  ·
                    refine ⟨20202087105637637919062917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26936116140850183892083889 20202087105637637919062917)
                    ·
                      refine ⟨3787891332307057109824297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20202087105637637919062917 3787891332307057109824297)
                      ·
                        rfl

theorem cell23_7376892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7376892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376892 prefixEnd_7376892 := by exact prefixLift 7376892
  have htrace : WordTrace (prefixWord ++ tailWord_7376892) baseStart_7376892 baseEnd_7376892 := by
    simpa [prefixWord, tailWord_7376892, baseEnd_7376892] using wordTrace_append hprefix tailTrace_7376892
  have hstable : (prefixWord ++ tailWord_7376892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376892).length < 2 ^ (prefixWord ++ tailWord_7376892).sum := by decide
  have hdescent : baseEnd_7376892 < baseStart_7376892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376912 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_7376912 : Nat := 118140960795 + 7376912 * 2 ^ 59
def prefixEnd_7376912 : Nat := 4983230072969 + 3 ^ 40 * 7376912 * 2
def baseEnd_7376912 : Nat := 3787901601920147031574205

theorem tailTrace_7376912 : CollatzResearch.WordTrace tailWord_7376912 prefixEnd_7376912 3787901601920147031574205 := by
  unfold tailWord_7376912
  simp only [CollatzResearch.WordTrace]
  refine ⟨134529042325357587555418495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179372056433810116740557993 134529042325357587555418495)
  ·
    refine ⟨201793563488036381333127743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134529042325357587555418495 201793563488036381333127743)
    ·
      refine ⟨302690345232054571999691615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201793563488036381333127743 302690345232054571999691615)
      ·
        refine ⟨454035517848081857999537423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302690345232054571999691615 454035517848081857999537423)
        ·
          refine ⟨681053276772122786999306135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454035517848081857999537423 681053276772122786999306135)
          ·
            refine ⟨1021579915158184180498959203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681053276772122786999306135 1021579915158184180498959203)
            ·
              refine ⟨1532369872737276270748438805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021579915158184180498959203 1532369872737276270748438805)
              ·
                refine ⟨71829837784559825191333069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1532369872737276270748438805 71829837784559825191333069)
                ·
                  refine ⟨26936189169209934446749901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71829837784559825191333069 26936189169209934446749901)
                  ·
                    refine ⟨10101070938453725417531213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26936189169209934446749901 10101070938453725417531213)
                    ·
                      refine ⟨3787901601920147031574205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101070938453725417531213 3787901601920147031574205)
                      ·
                        rfl

theorem cell23_7376912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_7376912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376912 prefixEnd_7376912 := by exact prefixLift 7376912
  have htrace : WordTrace (prefixWord ++ tailWord_7376912) baseStart_7376912 baseEnd_7376912 := by
    simpa [prefixWord, tailWord_7376912, baseEnd_7376912] using wordTrace_append hprefix tailTrace_7376912
  have hstable : (prefixWord ++ tailWord_7376912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376912).length < 2 ^ (prefixWord ++ tailWord_7376912).sum := by decide
  have hdescent : baseEnd_7376912 < baseStart_7376912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376919 : List Nat := [1, 1, 3, 5, 2, 1, 2, 8]
def baseStart_7376919 : Nat := 118140960795 + 7376919 * 2 ^ 59
def prefixEnd_7376919 : Nat := 4983230072969 + 3 ^ 40 * 7376919 * 2
def baseEnd_7376919 : Nat := 140292785047582537192099

theorem tailTrace_7376919 : CollatzResearch.WordTrace tailWord_7376919 prefixEnd_7376919 140292785047582537192099 := by
  unfold tailWord_7376919
  simp only [CollatzResearch.WordTrace]
  refine ⟨269058339961689815306341811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179372226641126543537561207 269058339961689815306341811)
  ·
    refine ⟨403587509942534722959512717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269058339961689815306341811 403587509942534722959512717)
    ·
      refine ⟨151345316228450521109817269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403587509942534722959512717 151345316228450521109817269)
      ·
        refine ⟨14188623396417236354045369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151345316228450521109817269 14188623396417236354045369)
        ·
          refine ⟨10641467547312927265534027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14188623396417236354045369 10641467547312927265534027)
          ·
            refine ⟨15962201320969390898301041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641467547312927265534027 15962201320969390898301041)
            ·
              refine ⟨11971650990727043173725781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15962201320969390898301041 11971650990727043173725781)
              ·
                refine ⟨140292785047582537192099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11971650990727043173725781 140292785047582537192099)
                ·
                  rfl

theorem cell23_7376919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 8].length) (baseStart_7376919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376919 prefixEnd_7376919 := by exact prefixLift 7376919
  have htrace : WordTrace (prefixWord ++ tailWord_7376919) baseStart_7376919 baseEnd_7376919 := by
    simpa [prefixWord, tailWord_7376919, baseEnd_7376919] using wordTrace_append hprefix tailTrace_7376919
  have hstable : (prefixWord ++ tailWord_7376919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376919).length < 2 ^ (prefixWord ++ tailWord_7376919).sum := by decide
  have hdescent : baseEnd_7376919 < baseStart_7376919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376969 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 3, 4, 2]
def baseStart_7376969 : Nat := 118140960795 + 7376969 * 2 ^ 59
def prefixEnd_7376969 : Nat := 4983230072969 + 3 ^ 40 * 7376969 * 2
def baseEnd_7376969 : Nat := 3787930870317453308561443

theorem tailTrace_7376969 : CollatzResearch.WordTrace tailWord_7376969 prefixEnd_7376969 3787930870317453308561443 := by
  unfold tailWord_7376969
  simp only [CollatzResearch.WordTrace]
  refine ⟨269060163611508673845661961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179373442407672449230441307 269060163611508673845661961)
  ·
    refine ⟨201795122708631505384246471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269060163611508673845661961 201795122708631505384246471)
    ·
      refine ⟨302692684062947258076369707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201795122708631505384246471 302692684062947258076369707)
      ·
        refine ⟨454039026094420887114554561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302692684062947258076369707 454039026094420887114554561)
        ·
          refine ⟨340529269570815665335915921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454039026094420887114554561 340529269570815665335915921)
          ·
            refine ⟨255396952178111749001936941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340529269570815665335915921 255396952178111749001936941)
            ·
              refine ⟨95773857066791905875726353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255396952178111749001936941 95773857066791905875726353)
              ·
                refine ⟨71830392800093929406794765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95773857066791905875726353 71830392800093929406794765)
                ·
                  refine ⟨26936397300035223527548037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71830392800093929406794765 26936397300035223527548037)
                  ·
                    refine ⟨5050574493756604411415257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26936397300035223527548037 5050574493756604411415257)
                    ·
                      refine ⟨3787930870317453308561443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050574493756604411415257 3787930870317453308561443)
                      ·
                        rfl

theorem cell23_7376969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 4, 2].length) (baseStart_7376969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376969 prefixEnd_7376969 := by exact prefixLift 7376969
  have htrace : WordTrace (prefixWord ++ tailWord_7376969) baseStart_7376969 baseEnd_7376969 := by
    simpa [prefixWord, tailWord_7376969, baseEnd_7376969] using wordTrace_append hprefix tailTrace_7376969
  have hstable : (prefixWord ++ tailWord_7376969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376969).length < 2 ^ (prefixWord ++ tailWord_7376969).sum := by decide
  have hdescent : baseEnd_7376969 < baseStart_7376969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376972 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7376972 : Nat := 118140960795 + 7376972 * 2 ^ 59
def prefixEnd_7376972 : Nat := 4983230072969 + 3 ^ 40 * 7376972 * 2
def baseEnd_7376972 : Nat := 3787932410759416796823929

theorem tailTrace_7376972 : CollatzResearch.WordTrace tailWord_7376972 prefixEnd_7376972 3787932410759416796823929 := by
  unfold tailWord_7376972
  simp only [CollatzResearch.WordTrace]
  refine ⟨134530136515248902679010585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179373515353665203572014113 134530136515248902679010585)
  ·
    refine ⟨100897602386436677009257939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134530136515248902679010585 100897602386436677009257939)
    ·
      refine ⟨151346403579655015513886909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100897602386436677009257939 151346403579655015513886909)
      ·
        refine ⟨56754901342370630817707591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151346403579655015513886909 56754901342370630817707591)
        ·
          refine ⟨85132352013555946226561387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56754901342370630817707591 85132352013555946226561387)
          ·
            refine ⟨127698528020333919339842081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85132352013555946226561387 127698528020333919339842081)
            ·
              refine ⟨95773896015250439504881561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127698528020333919339842081 95773896015250439504881561)
              ·
                refine ⟨71830422011437829628661171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95773896015250439504881561 71830422011437829628661171)
                ·
                  refine ⟨107745633017156744442991757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71830422011437829628661171 107745633017156744442991757)
                  ·
                    refine ⟨40404612381433779166121909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107745633017156744442991757 40404612381433779166121909)
                    ·
                      refine ⟨3787932410759416796823929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40404612381433779166121909 3787932410759416796823929)
                      ·
                        rfl

theorem cell23_7376972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7376972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376972 prefixEnd_7376972 := by exact prefixLift 7376972
  have htrace : WordTrace (prefixWord ++ tailWord_7376972) baseStart_7376972 baseEnd_7376972 := by
    simpa [prefixWord, tailWord_7376972, baseEnd_7376972] using wordTrace_append hprefix tailTrace_7376972
  have hstable : (prefixWord ++ tailWord_7376972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376972).length < 2 ^ (prefixWord ++ tailWord_7376972).sum := by decide
  have hdescent : baseEnd_7376972 < baseStart_7376972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376986 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2]
def baseStart_7376986 : Nat := 118140960795 + 7376986 * 2 ^ 59
def prefixEnd_7376986 : Nat := 4983230072969 + 3 ^ 40 * 7376986 * 2
def baseEnd_7376986 : Nat := 3787939599488579742048865

theorem tailTrace_7376986 : CollatzResearch.WordTrace tailWord_7376986 prefixEnd_7376986 3787939599488579742048865 := by
  unfold tailWord_7376986
  simp only [CollatzResearch.WordTrace]
  refine ⟨67265195913111771437257703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179373855768298057166020541 67265195913111771437257703)
  ·
    refine ⟨100897793869667657155886555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67265195913111771437257703 100897793869667657155886555)
    ·
      refine ⟨151346690804501485733829833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100897793869667657155886555 151346690804501485733829833)
      ·
        refine ⟨113510018103376114300372375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151346690804501485733829833 113510018103376114300372375)
        ·
          refine ⟨170265027155064171450558563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113510018103376114300372375 170265027155064171450558563)
          ·
            refine ⟨255397540732596257175837845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170265027155064171450558563 255397540732596257175837845)
            ·
              refine ⟨11971759721840449555117399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255397540732596257175837845 11971759721840449555117399)
              ·
                refine ⟨17957639582760674332676099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11971759721840449555117399 17957639582760674332676099)
                ·
                  refine ⟨26936459374141011499014149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17957639582760674332676099 26936459374141011499014149)
                  ·
                    refine ⟨5050586132651439656065153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26936459374141011499014149 5050586132651439656065153)
                    ·
                      refine ⟨3787939599488579742048865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050586132651439656065153 3787939599488579742048865)
                      ·
                        rfl

theorem cell23_7376986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_7376986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376986 prefixEnd_7376986 := by exact prefixLift 7376986
  have htrace : WordTrace (prefixWord ++ tailWord_7376986) baseStart_7376986 baseEnd_7376986 := by
    simpa [prefixWord, tailWord_7376986, baseEnd_7376986] using wordTrace_append hprefix tailTrace_7376986
  have hstable : (prefixWord ++ tailWord_7376986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376986).length < 2 ^ (prefixWord ++ tailWord_7376986).sum := by decide
  have hdescent : baseEnd_7376986 < baseStart_7376986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7376992 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 9]
def baseStart_7376992 : Nat := 118140960795 + 7376992 * 2 ^ 59
def prefixEnd_7376992 : Nat := 4983230072969 + 3 ^ 40 * 7376992 * 2
def baseEnd_7376992 : Nat := 420882520041389635397093

theorem tailTrace_7376992 : CollatzResearch.WordTrace tailWord_7376992 prefixEnd_7376992 420882520041389635397093 := by
  unfold tailWord_7376992
  simp only [CollatzResearch.WordTrace]
  refine ⟨134530501245212674386874615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179374001660283565849166153 134530501245212674386874615)
  ·
    refine ⟨201795751867819011580311923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134530501245212674386874615 201795751867819011580311923)
    ·
      refine ⟨302693627801728517370467885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201795751867819011580311923 302693627801728517370467885)
      ·
        refine ⟨113510110425648194013925457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302693627801728517370467885 113510110425648194013925457)
        ·
          refine ⟨85132582819236145510444093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113510110425648194013925457 85132582819236145510444093)
          ·
            refine ⟨31924718557213554566416535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85132582819236145510444093 31924718557213554566416535)
            ·
              refine ⟨47887077835820331849624803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31924718557213554566416535 47887077835820331849624803)
              ·
                refine ⟨71830616753730497774437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47887077835820331849624803 71830616753730497774437205)
                ·
                  refine ⟨420882520041389635397093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71830616753730497774437205 420882520041389635397093)
                  ·
                    rfl

theorem cell23_7376992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_7376992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7376992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7376992 prefixEnd_7376992 := by exact prefixLift 7376992
  have htrace : WordTrace (prefixWord ++ tailWord_7376992) baseStart_7376992 baseEnd_7376992 := by
    simpa [prefixWord, tailWord_7376992, baseEnd_7376992] using wordTrace_append hprefix tailTrace_7376992
  have hstable : (prefixWord ++ tailWord_7376992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7376992).length < 2 ^ (prefixWord ++ tailWord_7376992).sum := by decide
  have hdescent : baseEnd_7376992 < baseStart_7376992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7376992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377020 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_7377020 : Nat := 118140960795 + 7377020 * 2 ^ 59
def prefixEnd_7377020 : Nat := 4983230072969 + 3 ^ 40 * 7377020 * 2
def baseEnd_7377020 : Nat := 3787957057830832609023709

theorem tailTrace_7377020 : CollatzResearch.WordTrace tailWord_7377020 prefixEnd_7377020 3787957057830832609023709 := by
  unfold tailWord_7377020
  simp only [CollatzResearch.WordTrace]
  refine ⟨134531011867161954777884257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179374682489549273037179009 134531011867161954777884257)
  ·
    refine ⟨100898258900371466083413193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134531011867161954777884257 100898258900371466083413193)
    ·
      refine ⟨75673694175278599562559895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100898258900371466083413193 75673694175278599562559895)
      ·
        refine ⟨113510541262917899343839843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75673694175278599562559895 113510541262917899343839843)
        ·
          refine ⟨170265811894376849015759765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113510541262917899343839843 170265811894376849015759765)
          ·
            refine ⟨7981209932548914797613739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170265811894376849015759765 7981209932548914797613739)
            ·
              refine ⟨11971814898823372196420609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981209932548914797613739 11971814898823372196420609)
              ·
                refine ⟨8978861174117529147315457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971814898823372196420609 8978861174117529147315457)
                ·
                  refine ⟨6734145880588146860486593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8978861174117529147315457 6734145880588146860486593)
                  ·
                    refine ⟨5050609410441110145364945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734145880588146860486593 5050609410441110145364945)
                    ·
                      refine ⟨3787957057830832609023709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050609410441110145364945 3787957057830832609023709)
                      ·
                        rfl

theorem cell23_7377020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_7377020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377020 prefixEnd_7377020 := by exact prefixLift 7377020
  have htrace : WordTrace (prefixWord ++ tailWord_7377020) baseStart_7377020 baseEnd_7377020 := by
    simpa [prefixWord, tailWord_7377020, baseEnd_7377020] using wordTrace_append hprefix tailTrace_7377020
  have hstable : (prefixWord ++ tailWord_7377020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377020).length < 2 ^ (prefixWord ++ tailWord_7377020).sum := by decide
  have hdescent : baseEnd_7377020 < baseStart_7377020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377060 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 5]
def baseStart_7377060 : Nat := 118140960795 + 7377060 * 2 ^ 59
def prefixEnd_7377060 : Nat := 4983230072969 + 3 ^ 40 * 7377060 * 2
def baseEnd_7377060 : Nat := 420886399673001383613725

theorem tailTrace_7377060 : CollatzResearch.WordTrace tailWord_7377060 prefixEnd_7377060 420886399673001383613725 := by
  unfold tailWord_7377060
  simp only [CollatzResearch.WordTrace]
  refine ⟨134531741327089498193612317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179375655102785997591483089 134531741327089498193612317)
  ·
    refine ⟨50449402997658561822604619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134531741327089498193612317 50449402997658561822604619)
    ·
      refine ⟨75674104496487842733906929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50449402997658561822604619 75674104496487842733906929)
      ·
        refine ⟨56755578372365882050430197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75674104496487842733906929 56755578372365882050430197)
        ·
          refine ⟨5320835472409301442227831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56755578372365882050430197 5320835472409301442227831)
          ·
            refine ⟨7981253208613952163341747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320835472409301442227831 7981253208613952163341747)
            ·
              refine ⟨11971879812920928245012621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981253208613952163341747 11971879812920928245012621)
              ·
                refine ⟨4489454929845348091879733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11971879812920928245012621 4489454929845348091879733)
                ·
                  refine ⟨420886399673001383613725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4489454929845348091879733 420886399673001383613725)
                  ·
                    rfl

theorem cell23_7377060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_7377060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377060 prefixEnd_7377060 := by exact prefixLift 7377060
  have htrace : WordTrace (prefixWord ++ tailWord_7377060) baseStart_7377060 baseEnd_7377060 := by
    simpa [prefixWord, tailWord_7377060, baseEnd_7377060] using wordTrace_append hprefix tailTrace_7377060
  have hstable : (prefixWord ++ tailWord_7377060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377060).length < 2 ^ (prefixWord ++ tailWord_7377060).sum := by decide
  have hdescent : baseEnd_7377060 < baseStart_7377060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377099 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 6]
def baseStart_7377099 : Nat := 118140960795 + 7377099 * 2 ^ 59
def prefixEnd_7377099 : Nat := 4983230072969 + 3 ^ 40 * 7377099 * 2
def baseEnd_7377099 : Nat := 420888624755837533326205

theorem tailTrace_7377099 : CollatzResearch.WordTrace tailWord_7377099 prefixEnd_7377099 420888624755837533326205 := by
  unfold tailWord_7377099
  simp only [CollatzResearch.WordTrace]
  refine ⟨269064905101037706047894351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179376603400691804031929567 269064905101037706047894351)
  ·
    refine ⟨403597357651556559071841527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269064905101037706047894351 403597357651556559071841527)
    ·
      refine ⟨605396036477334838607762291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403597357651556559071841527 605396036477334838607762291)
      ·
        refine ⟨908094054716002257911643437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605396036477334838607762291 908094054716002257911643437)
        ·
          refine ⟨340535270518500846716866289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 908094054716002257911643437 340535270518500846716866289)
          ·
            refine ⟨255401452888875635037649717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340535270518500846716866289 255401452888875635037649717)
            ·
              refine ⟨23943886208332090784779661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255401452888875635037649717 23943886208332090784779661)
              ·
                refine ⟨8978957328124534044292373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23943886208332090784779661 8978957328124534044292373)
                ·
                  refine ⟨420888624755837533326205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8978957328124534044292373 420888624755837533326205)
                  ·
                    rfl

theorem cell23_7377099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 6].length) (baseStart_7377099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377099 prefixEnd_7377099 := by exact prefixLift 7377099
  have htrace : WordTrace (prefixWord ++ tailWord_7377099) baseStart_7377099 baseEnd_7377099 := by
    simpa [prefixWord, tailWord_7377099, baseEnd_7377099] using wordTrace_append hprefix tailTrace_7377099
  have hstable : (prefixWord ++ tailWord_7377099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377099).length < 2 ^ (prefixWord ++ tailWord_7377099).sum := by decide
  have hdescent : baseEnd_7377099 < baseStart_7377099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377110 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7377110 : Nat := 118140960795 + 7377110 * 2 ^ 59
def prefixEnd_7377110 : Nat := 4983230072969 + 3 ^ 40 * 7377110 * 2
def baseEnd_7377110 : Nat := 3788003271089737256898295

theorem tailTrace_7377110 : CollatzResearch.WordTrace tailWord_7377110 prefixEnd_7377110 3788003271089737256898295 := by
  unfold tailWord_7377110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16816581643999865932909049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179376870869331903284363189 16816581643999865932909049)
  ·
    refine ⟨12612436232999899449681787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16816581643999865932909049 12612436232999899449681787)
    ·
      refine ⟨18918654349499849174522681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612436232999899449681787 18918654349499849174522681)
      ·
        refine ⟨14188990762124886880892011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18918654349499849174522681 14188990762124886880892011)
        ·
          refine ⟨21283486143187330321338017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14188990762124886880892011 21283486143187330321338017)
          ·
            refine ⟨15962614607390497741003513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21283486143187330321338017 15962614607390497741003513)
            ·
              refine ⟨11971960955542873305752635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15962614607390497741003513 11971960955542873305752635)
              ·
                refine ⟨17957941433314309958628953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11971960955542873305752635 17957941433314309958628953)
                ·
                  refine ⟨13468456074985732468971715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17957941433314309958628953 13468456074985732468971715)
                  ·
                    refine ⟨20202684112478598703457573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13468456074985732468971715 20202684112478598703457573)
                    ·
                      refine ⟨3788003271089737256898295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20202684112478598703457573 3788003271089737256898295)
                      ·
                        rfl

theorem cell23_7377110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7377110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377110 prefixEnd_7377110 := by exact prefixLift 7377110
  have htrace : WordTrace (prefixWord ++ tailWord_7377110) baseStart_7377110 baseEnd_7377110 := by
    simpa [prefixWord, tailWord_7377110, baseEnd_7377110] using wordTrace_append hprefix tailTrace_7377110
  have hstable : (prefixWord ++ tailWord_7377110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377110).length < 2 ^ (prefixWord ++ tailWord_7377110).sum := by decide
  have hdescent : baseEnd_7377110 < baseStart_7377110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377133 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 6]
def baseStart_7377133 : Nat := 118140960795 + 7377133 * 2 ^ 59
def prefixEnd_7377133 : Nat := 4983230072969 + 3 ^ 40 * 7377133 * 2
def baseEnd_7377133 : Nat := 420890564571643407434521

theorem tailTrace_7377133 : CollatzResearch.WordTrace tailWord_7377133 prefixEnd_7377133 420890564571643407434521 := by
  unfold tailWord_7377133
  simp only [CollatzResearch.WordTrace]
  refine ⟨269066145182914529854632053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179377430121943019903088035 269066145182914529854632053)
  ·
    refine ⟨25224951110898237173871755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269066145182914529854632053 25224951110898237173871755)
    ·
      refine ⟨37837426666347355760807633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25224951110898237173871755 37837426666347355760807633)
      ·
        refine ⟨28378069999760516820605725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37837426666347355760807633 28378069999760516820605725)
        ·
          refine ⟨10641776249910193807727147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28378069999760516820605725 10641776249910193807727147)
          ·
            refine ⟨15962664374865290711590721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641776249910193807727147 15962664374865290711590721)
            ·
              refine ⟨11971998281148968033693041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15962664374865290711590721 11971998281148968033693041)
              ·
                refine ⟨8978998710861726025269781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971998281148968033693041 8978998710861726025269781)
                ·
                  refine ⟨420890564571643407434521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8978998710861726025269781 420890564571643407434521)
                  ·
                    rfl

theorem cell23_7377133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_7377133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377133 prefixEnd_7377133 := by exact prefixLift 7377133
  have htrace : WordTrace (prefixWord ++ tailWord_7377133) baseStart_7377133 baseEnd_7377133 := by
    simpa [prefixWord, tailWord_7377133, baseEnd_7377133] using wordTrace_append hprefix tailTrace_7377133
  have hstable : (prefixWord ++ tailWord_7377133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377133).length < 2 ^ (prefixWord ++ tailWord_7377133).sum := by decide
  have hdescent : baseEnd_7377133 < baseStart_7377133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377166 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7377166 : Nat := 118140960795 + 7377166 * 2 ^ 59
def prefixEnd_7377166 : Nat := 4983230072969 + 3 ^ 40 * 7377166 * 2
def baseEnd_7377166 : Nat := 3788032026006389037798037

theorem tailTrace_7377166 : CollatzResearch.WordTrace tailWord_7377166 prefixEnd_7377166 3788032026006389037798037 := by
  unfold tailWord_7377166
  simp only [CollatzResearch.WordTrace]
  refine ⟨33633418598974372061322919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179378232527863317660388901 33633418598974372061322919)
  ·
    refine ⟨50450127898461558091984379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33633418598974372061322919 50450127898461558091984379)
    ·
      refine ⟨75675191847692337137976569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50450127898461558091984379 75675191847692337137976569)
      ·
        refine ⟨56756393885769252853482427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75675191847692337137976569 56756393885769252853482427)
        ·
          refine ⟨85134590828653879280223641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56756393885769252853482427 85134590828653879280223641)
          ·
            refine ⟨63850943121490409460167731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85134590828653879280223641 63850943121490409460167731)
            ·
              refine ⟨95776414682235614190251597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63850943121490409460167731 95776414682235614190251597)
              ·
                refine ⟨35916155505838355321344349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95776414682235614190251597 35916155505838355321344349)
                ·
                  refine ⟨13468558314689383245504131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35916155505838355321344349 13468558314689383245504131)
                  ·
                    refine ⟨20202837472034074868256197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13468558314689383245504131 20202837472034074868256197)
                    ·
                      refine ⟨3788032026006389037798037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20202837472034074868256197 3788032026006389037798037)
                      ·
                        rfl

theorem cell23_7377166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7377166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377166 prefixEnd_7377166 := by exact prefixLift 7377166
  have htrace : WordTrace (prefixWord ++ tailWord_7377166) baseStart_7377166 baseEnd_7377166 := by
    simpa [prefixWord, tailWord_7377166, baseEnd_7377166] using wordTrace_append hprefix tailTrace_7377166
  have hstable : (prefixWord ++ tailWord_7377166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377166).length < 2 ^ (prefixWord ++ tailWord_7377166).sum := by decide
  have hdescent : baseEnd_7377166 < baseStart_7377166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377176 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 4, 4]
def baseStart_7377176 : Nat := 118140960795 + 7377176 * 2 ^ 59
def prefixEnd_7377176 : Nat := 4983230072969 + 3 ^ 40 * 7377176 * 2
def baseEnd_7377176 : Nat := 1262679053604311332890997

theorem tailTrace_7377176 : CollatzResearch.WordTrace tailWord_7377176 prefixEnd_7377176 1262679053604311332890997 := by
  unfold tailWord_7377176
  simp only [CollatzResearch.WordTrace]
  refine ⟨134533856760879374099223691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179378475681172498798964921 134533856760879374099223691)
  ·
    refine ⟨201800785141319061148835537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134533856760879374099223691 201800785141319061148835537)
    ·
      refine ⟨151350588855989295861626653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201800785141319061148835537 151350588855989295861626653)
      ·
        refine ⟨56756470820995985948109995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151350588855989295861626653 56756470820995985948109995)
        ·
          refine ⟨85134706231493978922164993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56756470820995985948109995 85134706231493978922164993)
          ·
            refine ⟨63851029673620484191623745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85134706231493978922164993 63851029673620484191623745)
            ·
              refine ⟨47888272255215363143717809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63851029673620484191623745 47888272255215363143717809)
              ·
                refine ⟨35916204191411522357788357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47888272255215363143717809 35916204191411522357788357)
                ·
                  refine ⟨6734288285889660442085317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35916204191411522357788357 6734288285889660442085317)
                  ·
                    refine ⟨1262679053604311332890997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6734288285889660442085317 1262679053604311332890997)
                    ·
                      rfl

theorem cell23_7377176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_7377176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377176 prefixEnd_7377176 := by exact prefixLift 7377176
  have htrace : WordTrace (prefixWord ++ tailWord_7377176) baseStart_7377176 baseEnd_7377176 := by
    simpa [prefixWord, tailWord_7377176, baseEnd_7377176] using wordTrace_append hprefix tailTrace_7377176
  have hstable : (prefixWord ++ tailWord_7377176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377176).length < 2 ^ (prefixWord ++ tailWord_7377176).sum := by decide
  have hdescent : baseEnd_7377176 < baseStart_7377176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377183 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 4]
def baseStart_7377183 : Nat := 118140960795 + 7377183 * 2 ^ 59
def prefixEnd_7377183 : Nat := 4983230072969 + 3 ^ 40 * 7377183 * 2
def baseEnd_7377183 : Nat := 3788040755177515471285459

theorem tailTrace_7377183 : CollatzResearch.WordTrace tailWord_7377183 prefixEnd_7377183 3788040755177515471285459 := by
  unfold tailWord_7377183
  simp only [CollatzResearch.WordTrace]
  refine ⟨269067968832733388393952203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179378645888488925595968135 269067968832733388393952203)
  ·
    refine ⟨403601953249100082590928305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269067968832733388393952203 403601953249100082590928305)
    ·
      refine ⟨302701464936825061943196229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403601953249100082590928305 302701464936825061943196229)
      ·
        refine ⟨56756524675654699114349293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302701464936825061943196229 56756524675654699114349293)
        ·
          refine ⟨21283696753370512167880985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56756524675654699114349293 21283696753370512167880985)
          ·
            refine ⟨15962772565027884125910739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21283696753370512167880985 15962772565027884125910739)
            ·
              refine ⟨23944158847541826188866109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15962772565027884125910739 23944158847541826188866109)
              ·
                refine ⟨8979059567828184820824791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23944158847541826188866109 8979059567828184820824791)
                ·
                  refine ⟨13468589351742277231237187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979059567828184820824791 13468589351742277231237187)
                  ·
                    refine ⟨20202884027613415846855781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13468589351742277231237187 20202884027613415846855781)
                    ·
                      refine ⟨3788040755177515471285459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20202884027613415846855781 3788040755177515471285459)
                      ·
                        rfl

theorem cell23_7377183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_7377183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377183 prefixEnd_7377183 := by exact prefixLift 7377183
  have htrace : WordTrace (prefixWord ++ tailWord_7377183) baseStart_7377183 baseEnd_7377183 := by
    simpa [prefixWord, tailWord_7377183, baseEnd_7377183] using wordTrace_append hprefix tailTrace_7377183
  have hstable : (prefixWord ++ tailWord_7377183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377183).length < 2 ^ (prefixWord ++ tailWord_7377183).sum := by decide
  have hdescent : baseEnd_7377183 < baseStart_7377183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377210 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_7377210 : Nat := 118140960795 + 7377210 * 2 ^ 59
def prefixEnd_7377210 : Nat := 4983230072969 + 3 ^ 40 * 7377210 * 2
def baseEnd_7377210 : Nat := 1262684873051728955215945

theorem tailTrace_7377210 : CollatzResearch.WordTrace tailWord_7377210 prefixEnd_7377210 1262684873051728955215945 := by
  unfold tailWord_7377210
  simp only [CollatzResearch.WordTrace]
  refine ⟨67267238400908893001296271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179379302402423714670123389 67267238400908893001296271)
  ·
    refine ⟨100900857601363339501944407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67267238400908893001296271 100900857601363339501944407)
    ·
      refine ⟨151351286402045009252916611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100900857601363339501944407 151351286402045009252916611)
      ·
        refine ⟨227026929603067513879374917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151351286402045009252916611 227026929603067513879374917)
        ·
          refine ⟨42567549300575158852382797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227026929603067513879374917 42567549300575158852382797)
          ·
            refine ⟨15962830987715684569643549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42567549300575158852382797 15962830987715684569643549)
            ·
              refine ⟨5986061620393381713616331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15962830987715684569643549 5986061620393381713616331)
              ·
                refine ⟨8979092430590072570424497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986061620393381713616331 8979092430590072570424497)
                ·
                  refine ⟨6734319322942554427818373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8979092430590072570424497 6734319322942554427818373)
                  ·
                    refine ⟨1262684873051728955215945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6734319322942554427818373 1262684873051728955215945)
                    ·
                      rfl

theorem cell23_7377210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_7377210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377210 prefixEnd_7377210 := by exact prefixLift 7377210
  have htrace : WordTrace (prefixWord ++ tailWord_7377210) baseStart_7377210 baseEnd_7377210 := by
    simpa [prefixWord, tailWord_7377210, baseEnd_7377210] using wordTrace_append hprefix tailTrace_7377210
  have hstable : (prefixWord ++ tailWord_7377210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377210).length < 2 ^ (prefixWord ++ tailWord_7377210).sum := by decide
  have hdescent : baseEnd_7377210 < baseStart_7377210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377216 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_7377216 : Nat := 118140960795 + 7377216 * 2 ^ 59
def prefixEnd_7377216 : Nat := 4983230072969 + 3 ^ 40 * 7377216 * 2
def baseEnd_7377216 : Nat := 3788057700039113842172807

theorem tailTrace_7377216 : CollatzResearch.WordTrace tailWord_7377216 prefixEnd_7377216 3788057700039113842172807 := by
  unfold tailWord_7377216
  simp only [CollatzResearch.WordTrace]
  refine ⟨134534586220806917514951751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179379448294409223353269001 134534586220806917514951751)
  ·
    refine ⟨201801879331210376272427627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134534586220806917514951751 201801879331210376272427627)
    ·
      refine ⟨302702818996815564408641441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201801879331210376272427627 302702818996815564408641441)
      ·
        refine ⟨227027114247611673306481081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302702818996815564408641441 227027114247611673306481081)
        ·
          refine ⟨170270335685708754979860811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227027114247611673306481081 170270335685708754979860811)
          ·
            refine ⟨255405503528563132469791217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170270335685708754979860811 255405503528563132469791217)
            ·
              refine ⟨191554127646422349352343413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255405503528563132469791217 191554127646422349352343413)
              ·
                refine ⟨17958199466852095251782195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191554127646422349352343413 17958199466852095251782195)
                ·
                  refine ⟨26937299200278142877673293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17958199466852095251782195 26937299200278142877673293)
                  ·
                    refine ⟨10101487200104303579127485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26937299200278142877673293 10101487200104303579127485)
                    ·
                      refine ⟨3788057700039113842172807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101487200104303579127485 3788057700039113842172807)
                      ·
                        rfl

theorem cell23_7377216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_7377216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377216 prefixEnd_7377216 := by exact prefixLift 7377216
  have htrace : WordTrace (prefixWord ++ tailWord_7377216) baseStart_7377216 baseEnd_7377216 := by
    simpa [prefixWord, tailWord_7377216, baseEnd_7377216] using wordTrace_append hprefix tailTrace_7377216
  have hstable : (prefixWord ++ tailWord_7377216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377216).length < 2 ^ (prefixWord ++ tailWord_7377216).sum := by decide
  have hdescent : baseEnd_7377216 < baseStart_7377216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377219 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 2, 7]
def baseStart_7377219 : Nat := 118140960795 + 7377219 * 2 ^ 59
def prefixEnd_7377219 : Nat := 4983230072969 + 3 ^ 40 * 7377219 * 2
def baseEnd_7377219 : Nat := 1262686413493692443478431

theorem tailTrace_7377219 : CollatzResearch.WordTrace tailWord_7377219 prefixEnd_7377219 1262686413493692443478431 := by
  unfold tailWord_7377219
  simp only [CollatzResearch.WordTrace]
  refine ⟨269069281860602966542262711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179379521240401977694841807 269069281860602966542262711)
  ·
    refine ⟨403603922790904449813394067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269069281860602966542262711 403603922790904449813394067)
    ·
      refine ⟨605405884186356674720091101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403603922790904449813394067 605405884186356674720091101)
      ·
        refine ⟨227027206569883753020034163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605405884186356674720091101 227027206569883753020034163)
        ·
          refine ⟨340540809854825629530051245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227027206569883753020034163 340540809854825629530051245)
          ·
            refine ⟨127702803695559611073769217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340540809854825629530051245 127702803695559611073769217)
            ·
              refine ⟨95777102771669708305326913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127702803695559611073769217 95777102771669708305326913)
              ·
                refine ⟨71832827078752281228995185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95777102771669708305326913 71832827078752281228995185)
                ·
                  refine ⟨53874620309064210921746389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71832827078752281228995185 53874620309064210921746389)
                  ·
                    refine ⟨1262686413493692443478431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53874620309064210921746389 1262686413493692443478431)
                    ·
                      rfl

theorem cell23_7377219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_7377219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377219 prefixEnd_7377219 := by exact prefixLift 7377219
  have htrace : WordTrace (prefixWord ++ tailWord_7377219) baseStart_7377219 baseEnd_7377219 := by
    simpa [prefixWord, tailWord_7377219, baseEnd_7377219] using wordTrace_append hprefix tailTrace_7377219
  have hstable : (prefixWord ++ tailWord_7377219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377219).length < 2 ^ (prefixWord ++ tailWord_7377219).sum := by decide
  have hdescent : baseEnd_7377219 < baseStart_7377219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377233 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_7377233 : Nat := 118140960795 + 7377233 * 2 ^ 59
def prefixEnd_7377233 : Nat := 4983230072969 + 3 ^ 40 * 7377233 * 2
def baseEnd_7377233 : Nat := 3788066429210240275660229

theorem tailTrace_7377233 : CollatzResearch.WordTrace tailWord_7377233 prefixEnd_7377233 3788066429210240275660229 := by
  unfold tailWord_7377233
  simp only [CollatzResearch.WordTrace]
  refine ⟨269069792482552246933272353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179379861655034831288848235 269069792482552246933272353)
  ·
    refine ⟨201802344361914185199954265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269069792482552246933272353 201802344361914185199954265)
    ·
      refine ⟨151351758271435638899965699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201802344361914185199954265 151351758271435638899965699)
      ·
        refine ⟨227027637407153458349948549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151351758271435638899965699 227027637407153458349948549)
        ·
          refine ⟨42567682013841273440615353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227027637407153458349948549 42567682013841273440615353)
          ·
            refine ⟨31925761510380955080461515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42567682013841273440615353 31925761510380955080461515)
            ·
              refine ⟨47888642265571432620692273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31925761510380955080461515 47888642265571432620692273)
              ·
                refine ⟨35916481699178574465519205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47888642265571432620692273 35916481699178574465519205)
                ·
                  refine ⟨6734340318595982712284851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35916481699178574465519205 6734340318595982712284851)
                  ·
                    refine ⟨10101510477893974068427277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6734340318595982712284851 10101510477893974068427277)
                    ·
                      refine ⟨3788066429210240275660229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101510477893974068427277 3788066429210240275660229)
                      ·
                        rfl

theorem cell23_7377233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_7377233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377233 prefixEnd_7377233 := by exact prefixLift 7377233
  have htrace : WordTrace (prefixWord ++ tailWord_7377233) baseStart_7377233 baseEnd_7377233 := by
    simpa [prefixWord, tailWord_7377233, baseEnd_7377233] using wordTrace_append hprefix tailTrace_7377233
  have hstable : (prefixWord ++ tailWord_7377233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377233).length < 2 ^ (prefixWord ++ tailWord_7377233).sum := by decide
  have hdescent : baseEnd_7377233 < baseStart_7377233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377250 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7377250 : Nat := 118140960795 + 7377250 * 2 ^ 59
def prefixEnd_7377250 : Nat := 4983230072969 + 3 ^ 40 * 7377250 * 2
def baseEnd_7377250 : Nat := 3788075158381366709147651

theorem tailTrace_7377250 : CollatzResearch.WordTrace tailWord_7377250 prefixEnd_7377250 3788075158381366709147651 := by
  unfold tailWord_7377250
  simp only [CollatzResearch.WordTrace]
  refine ⟨67267603130872664709160301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179380275015660439224427469 67267603130872664709160301)
  ·
    refine ⟨25225351174077249265935113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67267603130872664709160301 25225351174077249265935113)
    ·
      refine ⟨18919013380557936949451335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25225351174077249265935113 18919013380557936949451335)
      ·
        refine ⟨28378520070836905424177003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919013380557936949451335 28378520070836905424177003)
        ·
          refine ⟨42567780106255358136265505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28378520070836905424177003 42567780106255358136265505)
          ·
            refine ⟨31925835079691518602199129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42567780106255358136265505 31925835079691518602199129)
            ·
              refine ⟨23944376309768638951649347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31925835079691518602199129 23944376309768638951649347)
              ·
                refine ⟨35916564464652958427474021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23944376309768638951649347 35916564464652958427474021)
                ·
                  refine ⟨6734355837122429705151379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35916564464652958427474021 6734355837122429705151379)
                  ·
                    refine ⟨10101533755683644557727069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6734355837122429705151379 10101533755683644557727069)
                    ·
                      refine ⟨3788075158381366709147651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101533755683644557727069 3788075158381366709147651)
                      ·
                        rfl

theorem cell23_7377250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7377250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377250 prefixEnd_7377250 := by exact prefixLift 7377250
  have htrace : WordTrace (prefixWord ++ tailWord_7377250) baseStart_7377250 baseEnd_7377250 := by
    simpa [prefixWord, tailWord_7377250, baseEnd_7377250] using wordTrace_append hprefix tailTrace_7377250
  have hstable : (prefixWord ++ tailWord_7377250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377250).length < 2 ^ (prefixWord ++ tailWord_7377250).sum := by decide
  have hdescent : baseEnd_7377250 < baseStart_7377250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377273 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 1, 4, 2]
def baseStart_7377273 : Nat := 118140960795 + 7377273 * 2 ^ 59
def prefixEnd_7377273 : Nat := 4983230072969 + 3 ^ 40 * 7377273 * 2
def baseEnd_7377273 : Nat := 3788086968436420119160045

theorem tailTrace_7377273 : CollatzResearch.WordTrace tailWord_7377273 prefixEnd_7377273 3788086968436420119160045 := by
  unfold tailWord_7377273
  simp only [CollatzResearch.WordTrace]
  refine ⟨269071251402407333764728473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179380834268271555843152315 269071251402407333764728473)
  ·
    refine ⟨201803438551805500323546355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269071251402407333764728473 201803438551805500323546355)
    ·
      refine ⟨302705157827708250485319533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201803438551805500323546355 302705157827708250485319533)
      ·
        refine ⟨113514434185390593931994825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302705157827708250485319533 113514434185390593931994825)
        ·
          refine ⟨85135825639042945448996119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113514434185390593931994825 85135825639042945448996119)
          ·
            refine ⟨127703738458564418173494179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85135825639042945448996119 127703738458564418173494179)
            ·
              refine ⟨191555607687846627260241269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127703738458564418173494179 191555607687846627260241269)
              ·
                refine ⟨17958338220735621305647619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191555607687846627260241269 17958338220735621305647619)
                ·
                  refine ⟨26937507331103431958471429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17958338220735621305647619 26937507331103431958471429)
                  ·
                    refine ⟨5050782624581893492213393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26937507331103431958471429 5050782624581893492213393)
                    ·
                      refine ⟨3788086968436420119160045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050782624581893492213393 3788086968436420119160045)
                      ·
                        rfl

theorem cell23_7377273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_7377273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377273 prefixEnd_7377273 := by exact prefixLift 7377273
  have htrace : WordTrace (prefixWord ++ tailWord_7377273) baseStart_7377273 baseEnd_7377273 := by
    simpa [prefixWord, tailWord_7377273, baseEnd_7377273] using wordTrace_append hprefix tailTrace_7377273
  have hstable : (prefixWord ++ tailWord_7377273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377273).length < 2 ^ (prefixWord ++ tailWord_7377273).sum := by decide
  have hdescent : baseEnd_7377273 < baseStart_7377273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377276 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_7377276 : Nat := 118140960795 + 7377276 * 2 ^ 59
def prefixEnd_7377276 : Nat := 4983230072969 + 3 ^ 40 * 7377276 * 2
def baseEnd_7377276 : Nat := 3788088508878383607422531

theorem tailTrace_7377276 : CollatzResearch.WordTrace tailWord_7377276 prefixEnd_7377276 3788088508878383607422531 := by
  unfold tailWord_7377276
  simp only [CollatzResearch.WordTrace]
  refine ⟨134535680410698232638543841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179380907214264310184725121 134535680410698232638543841)
  ·
    refine ⟨100901760308023674478907881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134535680410698232638543841 100901760308023674478907881)
    ·
      refine ⟨75676320231017755859180911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100901760308023674478907881 75676320231017755859180911)
      ·
        refine ⟨113514480346526633788771367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75676320231017755859180911 113514480346526633788771367)
        ·
          refine ⟨170271720519789950683157051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113514480346526633788771367 170271720519789950683157051)
          ·
            refine ⟨255407580779684926024735577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170271720519789950683157051 255407580779684926024735577)
            ·
              refine ⟨191555685584763694518551683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255407580779684926024735577 191555685584763694518551683)
              ·
                refine ⟨287333528377145541777827525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191555685584763694518551683 287333528377145541777827525)
                ·
                  refine ⟨53875036570714789083342661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287333528377145541777827525 53875036570714789083342661)
                  ·
                    refine ⟨10101569357009022953126749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53875036570714789083342661 10101569357009022953126749)
                    ·
                      refine ⟨3788088508878383607422531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101569357009022953126749 3788088508878383607422531)
                      ·
                        rfl

theorem cell23_7377276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_7377276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377276 prefixEnd_7377276 := by exact prefixLift 7377276
  have htrace : WordTrace (prefixWord ++ tailWord_7377276) baseStart_7377276 baseEnd_7377276 := by
    simpa [prefixWord, tailWord_7377276, baseEnd_7377276] using wordTrace_append hprefix tailTrace_7377276
  have hstable : (prefixWord ++ tailWord_7377276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377276).length < 2 ^ (prefixWord ++ tailWord_7377276).sum := by decide
  have hdescent : baseEnd_7377276 < baseStart_7377276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377277 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_7377277 : Nat := 118140960795 + 7377277 * 2 ^ 59
def prefixEnd_7377277 : Nat := 4983230072969 + 3 ^ 40 * 7377277 * 2
def baseEnd_7377277 : Nat := 3788089022359038103510027

theorem tailTrace_7377277 : CollatzResearch.WordTrace tailWord_7377277 prefixEnd_7377277 3788089022359038103510027 := by
  unfold tailWord_7377277
  simp only [CollatzResearch.WordTrace]
  refine ⟨269071397294392842447874085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179380931529595228298582723 269071397294392842447874085)
  ·
    refine ⟨50450886992698657958976391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269071397294392842447874085 50450886992698657958976391)
    ·
      refine ⟨75676330489047986938464587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50450886992698657958976391 75676330489047986938464587)
      ·
        refine ⟨113514495733571980407696881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75676330489047986938464587 113514495733571980407696881)
        ·
          refine ⟨85135871800178985305772661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113514495733571980407696881 85135871800178985305772661)
          ·
            refine ⟨7981487981266779872416187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85135871800178985305772661 7981487981266779872416187)
            ·
              refine ⟨11972231971900169808624281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981487981266779872416187 11972231971900169808624281)
              ·
                refine ⟨8979173978925127356468211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11972231971900169808624281 8979173978925127356468211)
                ·
                  refine ⟨13468760968387691034702317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979173978925127356468211 13468760968387691034702317)
                  ·
                    refine ⟨5050785363145384138013369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13468760968387691034702317 5050785363145384138013369)
                    ·
                      refine ⟨3788089022359038103510027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050785363145384138013369 3788089022359038103510027)
                      ·
                        rfl

theorem cell23_7377277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_7377277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377277 prefixEnd_7377277 := by exact prefixLift 7377277
  have htrace : WordTrace (prefixWord ++ tailWord_7377277) baseStart_7377277 baseEnd_7377277 := by
    simpa [prefixWord, tailWord_7377277, baseEnd_7377277] using wordTrace_append hprefix tailTrace_7377277
  have hstable : (prefixWord ++ tailWord_7377277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377277).length < 2 ^ (prefixWord ++ tailWord_7377277).sum := by decide
  have hdescent : baseEnd_7377277 < baseStart_7377277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377294 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7377294 : Nat := 118140960795 + 7377294 * 2 ^ 59
def prefixEnd_7377294 : Nat := 4983230072969 + 3 ^ 40 * 7377294 * 2
def baseEnd_7377294 : Nat := 3788097751530164536997449

theorem tailTrace_7377294 : CollatzResearch.WordTrace tailWord_7377294 prefixEnd_7377294 3788097751530164536997449 := by
  unfold tailWord_7377294
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634002166916406793905367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179381344890220836234161957 33634002166916406793905367)
  ·
    refine ⟨50451003250374610190858051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33634002166916406793905367 50451003250374610190858051)
    ·
      refine ⟨75676504875561915286287077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50451003250374610190858051 75676504875561915286287077)
      ·
        refine ⟨14189344664167859116178827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75676504875561915286287077 14189344664167859116178827)
        ·
          refine ⟨21284016996251788674268241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14189344664167859116178827 21284016996251788674268241)
          ·
            refine ⟨15963012747188841505701181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21284016996251788674268241 15963012747188841505701181)
            ·
              refine ⟨5986129780195815564637943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15963012747188841505701181 5986129780195815564637943)
              ·
                refine ⟨8979194670293723346956915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986129780195815564637943 8979194670293723346956915)
                ·
                  refine ⟨13468792005440585020435373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979194670293723346956915 13468792005440585020435373)
                  ·
                    refine ⟨5050797002040219382663265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13468792005440585020435373 5050797002040219382663265)
                    ·
                      refine ⟨3788097751530164536997449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050797002040219382663265 3788097751530164536997449)
                      ·
                        rfl

theorem cell23_7377294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7377294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377294 prefixEnd_7377294 := by exact prefixLift 7377294
  have htrace : WordTrace (prefixWord ++ tailWord_7377294) baseStart_7377294 baseEnd_7377294 := by
    simpa [prefixWord, tailWord_7377294, baseEnd_7377294] using wordTrace_append hprefix tailTrace_7377294
  have hstable : (prefixWord ++ tailWord_7377294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377294).length < 2 ^ (prefixWord ++ tailWord_7377294).sum := by decide
  have hdescent : baseEnd_7377294 < baseStart_7377294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377302 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7377302 : Nat := 118140960795 + 7377302 * 2 ^ 59
def prefixEnd_7377302 : Nat := 4983230072969 + 3 ^ 40 * 7377302 * 2
def baseEnd_7377302 : Nat := 3788101859375400505697413

theorem tailTrace_7377302 : CollatzResearch.WordTrace tailWord_7377302 prefixEnd_7377302 3788101859375400505697413 := by
  unfold tailWord_7377302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16817019319956391982345885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179381539412868181145022773 16817019319956391982345885)
  ·
    refine ⟨6306382244983646993379707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16817019319956391982345885 6306382244983646993379707)
    ·
      refine ⟨9459573367475470490069561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306382244983646993379707 9459573367475470490069561)
      ·
        refine ⟨7094680025606602867552171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9459573367475470490069561 7094680025606602867552171)
        ·
          refine ⟨10642020038409904301328257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094680025606602867552171 10642020038409904301328257)
          ·
            refine ⟨7981515028807428225996193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10642020038409904301328257 7981515028807428225996193)
            ·
              refine ⟨5986136271605571169497145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7981515028807428225996193 5986136271605571169497145)
              ·
                refine ⟨4489602203704178377122859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5986136271605571169497145 4489602203704178377122859)
                ·
                  refine ⟨6734403305556267565684289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489602203704178377122859 6734403305556267565684289)
                  ·
                    refine ⟨5050802479167200674263217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734403305556267565684289 5050802479167200674263217)
                    ·
                      refine ⟨3788101859375400505697413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050802479167200674263217 3788101859375400505697413)
                      ·
                        rfl

theorem cell23_7377302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7377302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377302 prefixEnd_7377302 := by exact prefixLift 7377302
  have htrace : WordTrace (prefixWord ++ tailWord_7377302) baseStart_7377302 baseEnd_7377302 := by
    simpa [prefixWord, tailWord_7377302, baseEnd_7377302] using wordTrace_append hprefix tailTrace_7377302
  have hstable : (prefixWord ++ tailWord_7377302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377302).length < 2 ^ (prefixWord ++ tailWord_7377302).sum := by decide
  have hdescent : baseEnd_7377302 < baseStart_7377302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377310 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7377310 : Nat := 118140960795 + 7377310 * 2 ^ 59
def prefixEnd_7377310 : Nat := 4983230072969 + 3 ^ 40 * 7377310 * 2
def baseEnd_7377310 : Nat := 3788105967220636474397375

theorem tailTrace_7377310 : CollatzResearch.WordTrace tailWord_7377310 prefixEnd_7377310 3788105967220636474397375 := by
  unfold tailWord_7377310
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634075112909161135478173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179381733935515526055883589 33634075112909161135478173)
  ·
    refine ⟨12612778167340935425804315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33634075112909161135478173 12612778167340935425804315)
    ·
      refine ⟨18919167251011403138706473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612778167340935425804315 18919167251011403138706473)
      ·
        refine ⟨14189375438258552354029855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18919167251011403138706473 14189375438258552354029855)
        ·
          refine ⟨21284063157387828531044783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14189375438258552354029855 21284063157387828531044783)
          ·
            refine ⟨31926094736081742796567175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21284063157387828531044783 31926094736081742796567175)
            ·
              refine ⟨47889142104122614194850763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31926094736081742796567175 47889142104122614194850763)
              ·
                refine ⟨71833713156183921292276145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47889142104122614194850763 71833713156183921292276145)
                ·
                  refine ⟨53875284867137940969207109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71833713156183921292276145 53875284867137940969207109)
                  ·
                    refine ⟨10101615912588363931726333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53875284867137940969207109 10101615912588363931726333)
                    ·
                      refine ⟨3788105967220636474397375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101615912588363931726333 3788105967220636474397375)
                      ·
                        rfl

theorem cell23_7377310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7377310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377310 prefixEnd_7377310 := by exact prefixLift 7377310
  have htrace : WordTrace (prefixWord ++ tailWord_7377310) baseStart_7377310 baseEnd_7377310 := by
    simpa [prefixWord, tailWord_7377310, baseEnd_7377310] using wordTrace_append hprefix tailTrace_7377310
  have hstable : (prefixWord ++ tailWord_7377310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377310).length < 2 ^ (prefixWord ++ tailWord_7377310).sum := by decide
  have hdescent : baseEnd_7377310 < baseStart_7377310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377320 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7377320 : Nat := 118140960795 + 7377320 * 2 ^ 59
def prefixEnd_7377320 : Nat := 4983230072969 + 3 ^ 40 * 7377320 * 2
def baseEnd_7377320 : Nat := 3788111102027181435272329

theorem tailTrace_7377320 : CollatzResearch.WordTrace tailWord_7377320 prefixEnd_7377320 3788111102027181435272329 := by
  unfold tailWord_7377320
  simp only [CollatzResearch.WordTrace]
  refine ⟨134536482816618530395844707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179381977088824707194459609 134536482816618530395844707)
  ·
    refine ⟨201804724224927795593767061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134536482816618530395844707 201804724224927795593767061)
    ·
      refine ⟨9459596448043490418457831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201804724224927795593767061 9459596448043490418457831)
      ·
        refine ⟨14189394672065235627686747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9459596448043490418457831 14189394672065235627686747)
        ·
          refine ⟨21284092008097853441530121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14189394672065235627686747 21284092008097853441530121)
          ·
            refine ⟨15963069006073390081147591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21284092008097853441530121 15963069006073390081147591)
            ·
              refine ⟨23944603509110085121721387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15963069006073390081147591 23944603509110085121721387)
              ·
                refine ⟨35916905263665127682582081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23944603509110085121721387 35916905263665127682582081)
                ·
                  refine ⟨26937678947748845761936561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35916905263665127682582081 26937678947748845761936561)
                  ·
                    refine ⟨20203259210811634321452421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26937678947748845761936561 20203259210811634321452421)
                    ·
                      refine ⟨3788111102027181435272329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20203259210811634321452421 3788111102027181435272329)
                      ·
                        rfl

theorem cell23_7377320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7377320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377320 prefixEnd_7377320 := by exact prefixLift 7377320
  have htrace : WordTrace (prefixWord ++ tailWord_7377320) baseStart_7377320 baseEnd_7377320 := by
    simpa [prefixWord, tailWord_7377320, baseEnd_7377320] using wordTrace_append hprefix tailTrace_7377320
  have hstable : (prefixWord ++ tailWord_7377320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377320).length < 2 ^ (prefixWord ++ tailWord_7377320).sum := by decide
  have hdescent : baseEnd_7377320 < baseStart_7377320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377345 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7377345 : Nat := 118140960795 + 7377345 * 2 ^ 59
def prefixEnd_7377345 : Nat := 4983230072969 + 3 ^ 40 * 7377345 * 2
def baseEnd_7377345 : Nat := 3788123939043543837459715

theorem tailTrace_7377345 : CollatzResearch.WordTrace tailWord_7377345 prefixEnd_7377345 3788123939043543837459715 := by
  unfold tailWord_7377345
  simp only [CollatzResearch.WordTrace]
  refine ⟨269073877458146490061349489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179382584972097660040899659 269073877458146490061349489)
  ·
    refine ⟨201805408093609867546012117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269073877458146490061349489 201805408093609867546012117)
    ·
      refine ⟨4729814252193981270609659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 201805408093609867546012117 4729814252193981270609659)
      ·
        refine ⟨7094721378290971905914489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729814252193981270609659 7094721378290971905914489)
        ·
          refine ⟨5321041033718228929435867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7094721378290971905914489 5321041033718228929435867)
          ·
            refine ⟨7981561550577343394153801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321041033718228929435867 7981561550577343394153801)
            ·
              refine ⟨5986171162933007545615351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7981561550577343394153801 5986171162933007545615351)
              ·
                refine ⟨8979256744399511318423027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986171162933007545615351 8979256744399511318423027)
                ·
                  refine ⟨13468885116599266977634541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979256744399511318423027 13468885116599266977634541)
                  ·
                    refine ⟨5050831918724725116612953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13468885116599266977634541 5050831918724725116612953)
                    ·
                      refine ⟨3788123939043543837459715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050831918724725116612953 3788123939043543837459715)
                      ·
                        rfl

theorem cell23_7377345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7377345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377345 prefixEnd_7377345 := by exact prefixLift 7377345
  have htrace : WordTrace (prefixWord ++ tailWord_7377345) baseStart_7377345 baseEnd_7377345 := by
    simpa [prefixWord, tailWord_7377345, baseEnd_7377345] using wordTrace_append hprefix tailTrace_7377345
  have hstable : (prefixWord ++ tailWord_7377345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377345).length < 2 ^ (prefixWord ++ tailWord_7377345).sum := by decide
  have hdescent : baseEnd_7377345 < baseStart_7377345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377376 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_7377376 : Nat := 118140960795 + 7377376 * 2 ^ 59
def prefixEnd_7377376 : Nat := 4983230072969 + 3 ^ 40 * 7377376 * 2
def baseEnd_7377376 : Nat := 3788139856943833216172071

theorem tailTrace_7377376 : CollatzResearch.WordTrace tailWord_7377376 prefixEnd_7377376 3788139856943833216172071 := by
  unfold tailWord_7377376
  simp only [CollatzResearch.WordTrace]
  refine ⟨134537504060517091177863991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179383338747356121570485321 134537504060517091177863991)
  ·
    refine ⟨201806256090775636766795987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134537504060517091177863991 201806256090775636766795987)
    ·
      refine ⟨302709384136163455150193981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201806256090775636766795987 302709384136163455150193981)
      ·
        refine ⟨113516019051061295681322743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302709384136163455150193981 113516019051061295681322743)
        ·
          refine ⟨170274028576591943521984115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113516019051061295681322743 170274028576591943521984115)
          ·
            refine ⟨255411042864887915282976173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170274028576591943521984115 255411042864887915282976173)
            ·
              refine ⟨95779141074332968231116065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255411042864887915282976173 95779141074332968231116065)
              ·
                refine ⟨71834355805749726173337049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95779141074332968231116065 71834355805749726173337049)
                ·
                  refine ⟨53875766854312294630002787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71834355805749726173337049 53875766854312294630002787)
                  ·
                    refine ⟨80813650281468441945004181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53875766854312294630002787 80813650281468441945004181)
                    ·
                      refine ⟨3788139856943833216172071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80813650281468441945004181 3788139856943833216172071)
                      ·
                        rfl

theorem cell23_7377376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_7377376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377376 prefixEnd_7377376 := by exact prefixLift 7377376
  have htrace : WordTrace (prefixWord ++ tailWord_7377376) baseStart_7377376 baseEnd_7377376 := by
    simpa [prefixWord, tailWord_7377376, baseEnd_7377376] using wordTrace_append hprefix tailTrace_7377376
  have hstable : (prefixWord ++ tailWord_7377376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377376).length < 2 ^ (prefixWord ++ tailWord_7377376).sum := by decide
  have hdescent : baseEnd_7377376 < baseStart_7377376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377383 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7377383 : Nat := 118140960795 + 7377383 * 2 ^ 59
def prefixEnd_7377383 : Nat := 4983230072969 + 3 ^ 40 * 7377383 * 2
def baseEnd_7377383 : Nat := 3788143451308414688784539

theorem tailTrace_7377383 : CollatzResearch.WordTrace tailWord_7377383 prefixEnd_7377383 3788143451308414688784539 := by
  unfold tailWord_7377383
  simp only [CollatzResearch.WordTrace]
  refine ⟨269075263432008822551232803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179383508954672548367488535 269075263432008822551232803)
  ·
    refine ⟨403612895148013233826849205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269075263432008822551232803 403612895148013233826849205)
    ·
      refine ⟨37838708920126240671267113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403612895148013233826849205 37838708920126240671267113)
      ·
        refine ⟨28379031690094680503450335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37838708920126240671267113 28379031690094680503450335)
        ·
          refine ⟨42568547535142020755175503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28379031690094680503450335 42568547535142020755175503)
          ·
            refine ⟨63852821302713031132763255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42568547535142020755175503 63852821302713031132763255)
            ·
              refine ⟨95779231954069546699144883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63852821302713031132763255 95779231954069546699144883)
              ·
                refine ⟨143668847931104320048717325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95779231954069546699144883 143668847931104320048717325)
                ·
                  refine ⟨53875817974164120018268997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143668847931104320048717325 53875817974164120018268997)
                  ·
                    refine ⟨10101715870155772503425437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53875817974164120018268997 10101715870155772503425437)
                    ·
                      refine ⟨3788143451308414688784539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101715870155772503425437 3788143451308414688784539)
                      ·
                        rfl

theorem cell23_7377383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7377383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377383 prefixEnd_7377383 := by exact prefixLift 7377383
  have htrace : WordTrace (prefixWord ++ tailWord_7377383) baseStart_7377383 baseEnd_7377383 := by
    simpa [prefixWord, tailWord_7377383, baseEnd_7377383] using wordTrace_append hprefix tailTrace_7377383
  have hstable : (prefixWord ++ tailWord_7377383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377383).length < 2 ^ (prefixWord ++ tailWord_7377383).sum := by decide
  have hdescent : baseEnd_7377383 < baseStart_7377383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377390 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_7377390 : Nat := 118140960795 + 7377390 * 2 ^ 59
def prefixEnd_7377390 : Nat := 4983230072969 + 3 ^ 40 * 7377390 * 2
def baseEnd_7377390 : Nat := 1262715681890998720465669

theorem tailTrace_7377390 : CollatzResearch.WordTrace tailWord_7377390 prefixEnd_7377390 1262715681890998720465669 := by
  unfold tailWord_7377390
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634439842872932843342203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179383679161988975164491749 33634439842872932843342203)
  ·
    refine ⟨50451659764309399265013305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33634439842872932843342203 50451659764309399265013305)
    ·
      refine ⟨37838744823232049448759979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50451659764309399265013305 37838744823232049448759979)
      ·
        refine ⟨56758117234848074173139969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37838744823232049448759979 56758117234848074173139969)
        ·
          refine ⟨42568587926136055629854977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56758117234848074173139969 42568587926136055629854977)
          ·
            refine ⟨31926440944602041722391233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42568587926136055629854977 31926440944602041722391233)
            ·
              refine ⟨23944830708451531291793425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31926440944602041722391233 23944830708451531291793425)
              ·
                refine ⟨17958623031338648468845069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23944830708451531291793425 17958623031338648468845069)
                ·
                  refine ⟨6734483636751993175816901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17958623031338648468845069 6734483636751993175816901)
                  ·
                    refine ⟨1262715681890998720465669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6734483636751993175816901 1262715681890998720465669)
                    ·
                      rfl

theorem cell23_7377390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_7377390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377390 prefixEnd_7377390 := by exact prefixLift 7377390
  have htrace : WordTrace (prefixWord ++ tailWord_7377390) baseStart_7377390 baseEnd_7377390 := by
    simpa [prefixWord, tailWord_7377390, baseEnd_7377390] using wordTrace_append hprefix tailTrace_7377390
  have hstable : (prefixWord ++ tailWord_7377390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377390).length < 2 ^ (prefixWord ++ tailWord_7377390).sum := by decide
  have hdescent : baseEnd_7377390 < baseStart_7377390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377414 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7377414 : Nat := 118140960795 + 7377414 * 2 ^ 59
def prefixEnd_7377414 : Nat := 4983230072969 + 3 ^ 40 * 7377414 * 2
def baseEnd_7377414 : Nat := 3788159369208704067496897

theorem tailTrace_7377414 : CollatzResearch.WordTrace tailWord_7377414 prefixEnd_7377414 3788159369208704067496897 := by
  unfold tailWord_7377414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8408637315465516088925353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179384262729931009897074197 8408637315465516088925353)
  ·
    refine ⟨6306477986599137066694015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8408637315465516088925353 6306477986599137066694015)
    ·
      refine ⟨9459716979898705600041023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306477986599137066694015 9459716979898705600041023)
      ·
        refine ⟨14189575469848058400061535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9459716979898705600041023 14189575469848058400061535)
        ·
          refine ⟨21284363204772087600092303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14189575469848058400061535 21284363204772087600092303)
          ·
            refine ⟨31926544807158131400138455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21284363204772087600092303 31926544807158131400138455)
            ·
              refine ⟨47889817210737197100207683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31926544807158131400138455 47889817210737197100207683)
              ·
                refine ⟨71834725816105795650311525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47889817210737197100207683 71834725816105795650311525)
                ·
                  refine ⟨13469011090519836684433411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71834725816105795650311525 13469011090519836684433411)
                  ·
                    refine ⟨20203516635779755026650117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13469011090519836684433411 20203516635779755026650117)
                    ·
                      refine ⟨3788159369208704067496897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20203516635779755026650117 3788159369208704067496897)
                      ·
                        rfl

theorem cell23_7377414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7377414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377414 prefixEnd_7377414 := by exact prefixLift 7377414
  have htrace : WordTrace (prefixWord ++ tailWord_7377414) baseStart_7377414 baseEnd_7377414 := by
    simpa [prefixWord, tailWord_7377414, baseEnd_7377414] using wordTrace_append hprefix tailTrace_7377414
  have hstable : (prefixWord ++ tailWord_7377414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377414).length < 2 ^ (prefixWord ++ tailWord_7377414).sum := by decide
  have hdescent : baseEnd_7377414 < baseStart_7377414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377437 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 6]
def baseStart_7377437 : Nat := 118140960795 + 7377437 * 2 ^ 59
def prefixEnd_7377437 : Nat := 4983230072969 + 3 ^ 40 * 7377437 * 2
def baseEnd_7377437 : Nat := 420907908807084164167699

theorem tailTrace_7377437 : CollatzResearch.WordTrace tailWord_7377437 prefixEnd_7377437 420907908807084164167699 := by
  unfold tailWord_7377437
  simp only [CollatzResearch.WordTrace]
  refine ⟨269077232973813189773698565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179384821982542126515799043 269077232973813189773698565)
  ·
    refine ⟨50451981182589973082568481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269077232973813189773698565 50451981182589973082568481)
    ·
      refine ⟨37838985886942479811926361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50451981182589973082568481 37838985886942479811926361)
      ·
        refine ⟨28379239415206859858944771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37838985886942479811926361 28379239415206859858944771)
        ·
          refine ⟨42568859122810289788417157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28379239415206859858944771 42568859122810289788417157)
          ·
            refine ⟨7981661085526929335328217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42568859122810289788417157 7981661085526929335328217)
            ·
              refine ⟨5986245814145197001496163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7981661085526929335328217 5986245814145197001496163)
              ·
                refine ⟨8979368721217795502244245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986245814145197001496163 8979368721217795502244245)
                ·
                  refine ⟨420907908807084164167699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8979368721217795502244245 420907908807084164167699)
                  ·
                    rfl

theorem cell23_7377437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_7377437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377437 prefixEnd_7377437 := by exact prefixLift 7377437
  have htrace : WordTrace (prefixWord ++ tailWord_7377437) baseStart_7377437 baseEnd_7377437 := by
    simpa [prefixWord, tailWord_7377437, baseEnd_7377437] using wordTrace_append hprefix tailTrace_7377437
  have hstable : (prefixWord ++ tailWord_7377437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377437).length < 2 ^ (prefixWord ++ tailWord_7377437).sum := by decide
  have hdescent : baseEnd_7377437 < baseStart_7377437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377450 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_7377450 : Nat := 118140960795 + 7377450 * 2 ^ 59
def prefixEnd_7377450 : Nat := 4983230072969 + 3 ^ 40 * 7377450 * 2
def baseEnd_7377450 : Nat := 1262725951504088642215577

theorem tailTrace_7377450 : CollatzResearch.WordTrace tailWord_7377450 prefixEnd_7377450 1262725951504088642215577 := by
  unfold tailWord_7377450
  simp only [CollatzResearch.WordTrace]
  refine ⟨67269426780691523248480451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179385138081844061995947869 67269426780691523248480451)
  ·
    refine ⟨100904140171037284872720677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67269426780691523248480451 100904140171037284872720677)
    ·
      refine ⟨18919526282069490913635127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100904140171037284872720677 18919526282069490913635127)
      ·
        refine ⟨28379289423104236370452691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919526282069490913635127 28379289423104236370452691)
        ·
          refine ⟨42568934134656354555679037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28379289423104236370452691 42568934134656354555679037)
          ·
            refine ⟨15963350300496132958379639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42568934134656354555679037 15963350300496132958379639)
            ·
              refine ⟨23945025450744199437569459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15963350300496132958379639 23945025450744199437569459)
              ·
                refine ⟨35917538176116299156354189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23945025450744199437569459 35917538176116299156354189)
                ·
                  refine ⟨13469076816043612183632821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35917538176116299156354189 13469076816043612183632821)
                  ·
                    refine ⟨1262725951504088642215577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13469076816043612183632821 1262725951504088642215577)
                    ·
                      rfl

theorem cell23_7377450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_7377450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377450 prefixEnd_7377450 := by exact prefixLift 7377450
  have htrace : WordTrace (prefixWord ++ tailWord_7377450) baseStart_7377450 baseEnd_7377450 := by
    simpa [prefixWord, tailWord_7377450, baseEnd_7377450] using wordTrace_append hprefix tailTrace_7377450
  have hstable : (prefixWord ++ tailWord_7377450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377450).length < 2 ^ (prefixWord ++ tailWord_7377450).sum := by decide
  have hdescent : baseEnd_7377450 < baseStart_7377450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377463 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 1, 6]
def baseStart_7377463 : Nat := 118140960795 + 7377463 * 2 ^ 59
def prefixEnd_7377463 : Nat := 4983230072969 + 3 ^ 40 * 7377463 * 2
def baseEnd_7377463 : Nat := 1262728176586924791928057

theorem tailTrace_7377463 : CollatzResearch.WordTrace tailWord_7377463 prefixEnd_7377463 1262728176586924791928057 := by
  unfold tailWord_7377463
  simp only [CollatzResearch.WordTrace]
  refine ⟨269078181271718996214145043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179385454181145997476096695 269078181271718996214145043)
  ·
    refine ⟨403617271907578494321217565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269078181271718996214145043 403617271907578494321217565)
    ·
      refine ⟨151356476965341935370456587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403617271907578494321217565 151356476965341935370456587)
      ·
        refine ⟨227034715448012903055684881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151356476965341935370456587 227034715448012903055684881)
        ·
          refine ⟨170276036586009677291763661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227034715448012903055684881 170276036586009677291763661)
          ·
            refine ⟨63853513719753628984411373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170276036586009677291763661 63853513719753628984411373)
            ·
              refine ⟨23945067644907610869154265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63853513719753628984411373 23945067644907610869154265)
              ·
                refine ⟨17958800733680708151865699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23945067644907610869154265 17958800733680708151865699)
                ·
                  refine ⟨26938201100521062227798549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17958800733680708151865699 26938201100521062227798549)
                  ·
                    refine ⟨1262728176586924791928057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26938201100521062227798549 1262728176586924791928057)
                    ·
                      rfl

theorem cell23_7377463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_7377463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377463 prefixEnd_7377463 := by exact prefixLift 7377463
  have htrace : WordTrace (prefixWord ++ tailWord_7377463) baseStart_7377463 baseEnd_7377463 := by
    simpa [prefixWord, tailWord_7377463, baseEnd_7377463] using wordTrace_append hprefix tailTrace_7377463
  have hstable : (prefixWord ++ tailWord_7377463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377463).length < 2 ^ (prefixWord ++ tailWord_7377463).sum := by decide
  have hdescent : baseEnd_7377463 < baseStart_7377463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377490 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_7377490 : Nat := 118140960795 + 7377490 * 2 ^ 59
def prefixEnd_7377490 : Nat := 4983230072969 + 3 ^ 40 * 7377490 * 2
def baseEnd_7377490 : Nat := 3788198393738445770146547

theorem tailTrace_7377490 : CollatzResearch.WordTrace tailWord_7377490 prefixEnd_7377490 3788198393738445770146547 := by
  unfold tailWord_7377490
  simp only [CollatzResearch.WordTrace]
  refine ⟨67269791510655294956344481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179386110695080786550251949 67269791510655294956344481)
  ·
    refine ⟨50452343632991471217258361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67269791510655294956344481 50452343632991471217258361)
    ·
      refine ⟨37839257724743603412943771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50452343632991471217258361 37839257724743603412943771)
      ·
        refine ⟨56758886587115405119415657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37839257724743603412943771 56758886587115405119415657)
        ·
          refine ⟨42569164940336553839561743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56758886587115405119415657 42569164940336553839561743)
          ·
            refine ⟨63853747410504830759342615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42569164940336553839561743 63853747410504830759342615)
            ·
              refine ⟨95780621115757246139013923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63853747410504830759342615 95780621115757246139013923)
              ·
                refine ⟨143670931673635869208520885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95780621115757246139013923 143670931673635869208520885)
                ·
                  refine ⟨13469149844403362738298833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143670931673635869208520885 13469149844403362738298833)
                  ·
                    refine ⟨10101862383302522053724125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13469149844403362738298833 10101862383302522053724125)
                    ·
                      refine ⟨3788198393738445770146547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101862383302522053724125 3788198393738445770146547)
                      ·
                        rfl

theorem cell23_7377490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_7377490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377490 prefixEnd_7377490 := by exact prefixLift 7377490
  have htrace : WordTrace (prefixWord ++ tailWord_7377490) baseStart_7377490 baseEnd_7377490 := by
    simpa [prefixWord, tailWord_7377490, baseEnd_7377490] using wordTrace_append hprefix tailTrace_7377490
  have hstable : (prefixWord ++ tailWord_7377490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377490).length < 2 ^ (prefixWord ++ tailWord_7377490).sum := by decide
  have hdescent : baseEnd_7377490 < baseStart_7377490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377493 : List Nat := [1, 3, 2, 2, 1, 1, 5, 8]
def baseStart_7377493 : Nat := 118140960795 + 7377493 * 2 ^ 59
def prefixEnd_7377493 : Nat := 4983230072969 + 3 ^ 40 * 7377493 * 2
def baseEnd_7377493 : Nat := 140303701265941083644779

theorem tailTrace_7377493 : CollatzResearch.WordTrace tailWord_7377493 prefixEnd_7377493 140303701265941083644779 := by
  unfold tailWord_7377493
  simp only [CollatzResearch.WordTrace]
  refine ⟨269079275461610311337737133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179386183641073540891824755 269079275461610311337737133)
  ·
    refine ⟨100904728298103866751651425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269079275461610311337737133 100904728298103866751651425)
    ·
      refine ⟨75678546223577900063738569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100904728298103866751651425 75678546223577900063738569)
      ·
        refine ⟨56758909667683425047803927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75678546223577900063738569 56758909667683425047803927)
        ·
          refine ⟨85138364501525137571705891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56758909667683425047803927 85138364501525137571705891)
          ·
            refine ⟨127707546752287706357558837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85138364501525137571705891 127707546752287706357558837)
            ·
              refine ⟨11972582508026972471021141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127707546752287706357558837 11972582508026972471021141)
              ·
                refine ⟨140303701265941083644779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11972582508026972471021141 140303701265941083644779)
                ·
                  rfl

theorem cell23_7377493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 8].length) (baseStart_7377493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377493 prefixEnd_7377493 := by exact prefixLift 7377493
  have htrace : WordTrace (prefixWord ++ tailWord_7377493) baseStart_7377493 baseEnd_7377493 := by
    simpa [prefixWord, tailWord_7377493, baseEnd_7377493] using wordTrace_append hprefix tailTrace_7377493
  have hstable : (prefixWord ++ tailWord_7377493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377493).length < 2 ^ (prefixWord ++ tailWord_7377493).sum := by decide
  have hdescent : baseEnd_7377493 < baseStart_7377493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377537 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_7377537 : Nat := 118140960795 + 7377537 * 2 ^ 59
def prefixEnd_7377537 : Nat := 4983230072969 + 3 ^ 40 * 7377537 * 2
def baseEnd_7377537 : Nat := 3788222527329207086258831

theorem tailTrace_7377537 : CollatzResearch.WordTrace tailWord_7377537 prefixEnd_7377537 3788222527329207086258831 := by
  unfold tailWord_7377537
  simp only [CollatzResearch.WordTrace]
  refine ⟨269080880273450906852338865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179387253515633937901559243 269080880273450906852338865)
  ·
    refine ⟨201810660205088180139254149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269080880273450906852338865 201810660205088180139254149)
    ·
      refine ⟨37839498788454033776110153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201810660205088180139254149 37839498788454033776110153)
      ·
        refine ⟨28379624091340525332082615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37839498788454033776110153 28379624091340525332082615)
        ·
          refine ⟨42569436137010787998123923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28379624091340525332082615 42569436137010787998123923)
          ·
            refine ⟨63854154205516181997185885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42569436137010787998123923 63854154205516181997185885)
            ·
              refine ⟨23945307827068568248944707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63854154205516181997185885 23945307827068568248944707)
              ·
                refine ⟨35917961740602852373417061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23945307827068568248944707 35917961740602852373417061)
                ·
                  refine ⟨6734617826363034820015699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35917961740602852373417061 6734617826363034820015699)
                  ·
                    refine ⟨10101926739544552230023549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6734617826363034820015699 10101926739544552230023549)
                    ·
                      refine ⟨3788222527329207086258831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101926739544552230023549 3788222527329207086258831)
                      ·
                        rfl

theorem cell23_7377537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_7377537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377537 prefixEnd_7377537 := by exact prefixLift 7377537
  have htrace : WordTrace (prefixWord ++ tailWord_7377537) baseStart_7377537 baseEnd_7377537 := by
    simpa [prefixWord, tailWord_7377537, baseEnd_7377537] using wordTrace_append hprefix tailTrace_7377537
  have hstable : (prefixWord ++ tailWord_7377537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377537).length < 2 ^ (prefixWord ++ tailWord_7377537).sum := by decide
  have hdescent : baseEnd_7377537 < baseStart_7377537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377554 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_7377554 : Nat := 118140960795 + 7377554 * 2 ^ 59
def prefixEnd_7377554 : Nat := 4983230072969 + 3 ^ 40 * 7377554 * 2
def baseEnd_7377554 : Nat := 3788231256500333519746253

theorem tailTrace_7377554 : CollatzResearch.WordTrace tailWord_7377554 prefixEnd_7377554 3788231256500333519746253 := by
  unfold tailWord_7377554
  simp only [CollatzResearch.WordTrace]
  refine ⟨67270375078597329688926929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179387666876259545837138477 67270375078597329688926929)
  ·
    refine ⟨50452781308947997266695197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67270375078597329688926929 50452781308947997266695197)
    ·
      refine ⟨18919792990855498975010699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50452781308947997266695197 18919792990855498975010699)
      ·
        refine ⟨28379689486283248462516049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919792990855498975010699 28379689486283248462516049)
        ·
          refine ⟨21284767114712436346887037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28379689486283248462516049 21284767114712436346887037)
          ·
            refine ⟨7981787668017163630082639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21284767114712436346887037 7981787668017163630082639)
            ·
              refine ⟨11972681502025745445123959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981787668017163630082639 11972681502025745445123959)
              ·
                refine ⟨17959022253038618167685939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11972681502025745445123959 17959022253038618167685939)
                ·
                  refine ⟨26938533379557927251528909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17959022253038618167685939 26938533379557927251528909)
                  ·
                    refine ⟨10101950017334222719323341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26938533379557927251528909 10101950017334222719323341)
                    ·
                      refine ⟨3788231256500333519746253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10101950017334222719323341 3788231256500333519746253)
                      ·
                        rfl

theorem cell23_7377554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_7377554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377554 prefixEnd_7377554 := by exact prefixLift 7377554
  have htrace : WordTrace (prefixWord ++ tailWord_7377554) baseStart_7377554 baseEnd_7377554 := by
    simpa [prefixWord, tailWord_7377554, baseEnd_7377554] using wordTrace_append hprefix tailTrace_7377554
  have hstable : (prefixWord ++ tailWord_7377554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377554).length < 2 ^ (prefixWord ++ tailWord_7377554).sum := by decide
  have hdescent : baseEnd_7377554 < baseStart_7377554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377564 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7377564 : Nat := 118140960795 + 7377564 * 2 ^ 59
def prefixEnd_7377564 : Nat := 4983230072969 + 3 ^ 40 * 7377564 * 2
def baseEnd_7377564 : Nat := 3788236391306878480621207

theorem tailTrace_7377564 : CollatzResearch.WordTrace tailWord_7377564 prefixEnd_7377564 3788236391306878480621207 := by
  unfold tailWord_7377564
  simp only [CollatzResearch.WordTrace]
  refine ⟨134540932522176545231785873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179387910029568726975714497 134540932522176545231785873)
  ·
    refine ⟨100905699391632408923839405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134540932522176545231785873 100905699391632408923839405)
    ·
      refine ⟨37839637271862153346439777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100905699391632408923839405 37839637271862153346439777)
      ·
        refine ⟨28379727953896615009829833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37839637271862153346439777 28379727953896615009829833)
        ·
          refine ⟨21284795965422461257372375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28379727953896615009829833 21284795965422461257372375)
          ·
            refine ⟨31927193948133691886058563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21284795965422461257372375 31927193948133691886058563)
            ·
              refine ⟨47890790922200537829087845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31927193948133691886058563 47890790922200537829087845)
              ·
                refine ⟨8979523297912600842953971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47890790922200537829087845 8979523297912600842953971)
                ·
                  refine ⟨13469284946868901264430957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979523297912600842953971 13469284946868901264430957)
                  ·
                    refine ⟨5050981855075837974161609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13469284946868901264430957 5050981855075837974161609)
                    ·
                      refine ⟨3788236391306878480621207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050981855075837974161609 3788236391306878480621207)
                      ·
                        rfl

theorem cell23_7377564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7377564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377564 prefixEnd_7377564 := by exact prefixLift 7377564
  have htrace : WordTrace (prefixWord ++ tailWord_7377564) baseStart_7377564 baseEnd_7377564 := by
    simpa [prefixWord, tailWord_7377564, baseEnd_7377564] using wordTrace_append hprefix tailTrace_7377564
  have hstable : (prefixWord ++ tailWord_7377564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377564).length < 2 ^ (prefixWord ++ tailWord_7377564).sum := by decide
  have hdescent : baseEnd_7377564 < baseStart_7377564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377577 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 4, 2, 2]
def baseStart_7377577 : Nat := 118140960795 + 7377577 * 2 ^ 59
def prefixEnd_7377577 : Nat := 4983230072969 + 3 ^ 40 * 7377577 * 2
def baseEnd_7377577 : Nat := 3788243066555386929758647

theorem tailTrace_7377577 : CollatzResearch.WordTrace tailWord_7377577 prefixEnd_7377577 3788243066555386929758647 := by
  unfold tailWord_7377577
  simp only [CollatzResearch.WordTrace]
  refine ⟨269082339193305993683794985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179388226128870662455863323 269082339193305993683794985)
  ·
    refine ⟨201811754394979495262846239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269082339193305993683794985 201811754394979495262846239)
    ·
      refine ⟨302717631592469242894269359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201811754394979495262846239 302717631592469242894269359)
      ·
        refine ⟨454076447388703864341404039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302717631592469242894269359 454076447388703864341404039)
        ·
          refine ⟨681114671083055796512106059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454076447388703864341404039 681114671083055796512106059)
          ·
            refine ⟨1021672006624583694768159089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681114671083055796512106059 1021672006624583694768159089)
            ·
              refine ⟨766254004968437771076119317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021672006624583694768159089 766254004968437771076119317)
              ·
                refine ⟨35918156482895520519193093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 766254004968437771076119317 35918156482895520519193093)
                ·
                  refine ⟨6734654340542910097348705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35918156482895520519193093 6734654340542910097348705)
                  ·
                    refine ⟨5050990755407182573011529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734654340542910097348705 5050990755407182573011529)
                    ·
                      refine ⟨3788243066555386929758647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5050990755407182573011529 3788243066555386929758647)
                      ·
                        rfl

theorem cell23_7377577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 2, 2].length) (baseStart_7377577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377577 prefixEnd_7377577 := by exact prefixLift 7377577
  have htrace : WordTrace (prefixWord ++ tailWord_7377577) baseStart_7377577 baseEnd_7377577 := by
    simpa [prefixWord, tailWord_7377577, baseEnd_7377577] using wordTrace_append hprefix tailTrace_7377577
  have hstable : (prefixWord ++ tailWord_7377577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377577).length < 2 ^ (prefixWord ++ tailWord_7377577).sum := by decide
  have hdescent : baseEnd_7377577 < baseStart_7377577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377593 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7377593 : Nat := 118140960795 + 7377593 * 2 ^ 59
def prefixEnd_7377593 : Nat := 4983230072969 + 3 ^ 40 * 7377593 * 2
def baseEnd_7377593 : Nat := 3788251282245858867158573

theorem tailTrace_7377593 : CollatzResearch.WordTrace tailWord_7377593 prefixEnd_7377593 3788251282245858867158573 := by
  unfold tailWord_7377593
  simp only [CollatzResearch.WordTrace]
  refine ⟨269082922761248028416377433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179388615174165352277584955 269082922761248028416377433)
  ·
    refine ⟨201812192070936021312283075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269082922761248028416377433 201812192070936021312283075)
    ·
      refine ⟨302718288106404031968424613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201812192070936021312283075 302718288106404031968424613)
      ·
        refine ⟨56759679019950755994079615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302718288106404031968424613 56759679019950755994079615)
        ·
          refine ⟨85139518529926133991119423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56759679019950755994079615 85139518529926133991119423)
          ·
            refine ⟨127709277794889200986679135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85139518529926133991119423 127709277794889200986679135)
            ·
              refine ⟨191563916692333801480018703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127709277794889200986679135 191563916692333801480018703)
              ·
                refine ⟨287345875038500702220028055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191563916692333801480018703 287345875038500702220028055)
                ·
                  refine ⟨431018812557751053330042083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287345875038500702220028055 431018812557751053330042083)
                  ·
                    refine ⟨646528218836626579995063125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431018812557751053330042083 646528218836626579995063125)
                    ·
                      refine ⟨3788251282245858867158573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 646528218836626579995063125 3788251282245858867158573)
                      ·
                        rfl

theorem cell23_7377593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7377593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377593 prefixEnd_7377593 := by exact prefixLift 7377593
  have htrace : WordTrace (prefixWord ++ tailWord_7377593) baseStart_7377593 baseEnd_7377593 := by
    simpa [prefixWord, tailWord_7377593, baseEnd_7377593] using wordTrace_append hprefix tailTrace_7377593
  have hstable : (prefixWord ++ tailWord_7377593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377593).length < 2 ^ (prefixWord ++ tailWord_7377593).sum := by decide
  have hdescent : baseEnd_7377593 < baseStart_7377593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377594 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2]
def baseStart_7377594 : Nat := 118140960795 + 7377594 * 2 ^ 59
def prefixEnd_7377594 : Nat := 4983230072969 + 3 ^ 40 * 7377594 * 2
def baseEnd_7377594 : Nat := 3788251795726513363246069

theorem tailTrace_7377594 : CollatzResearch.WordTrace tailWord_7377594 prefixEnd_7377594 3788251795726513363246069 := by
  unfold tailWord_7377594
  simp only [CollatzResearch.WordTrace]
  refine ⟨67270739808561101396790959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179388639489496270391442557 67270739808561101396790959)
  ·
    refine ⟨100906109712841652095186439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67270739808561101396790959 100906109712841652095186439)
    ·
      refine ⟨151359164569262478142779659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100906109712841652095186439 151359164569262478142779659)
      ·
        refine ⟨227038746853893717214169489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151359164569262478142779659 227038746853893717214169489)
        ·
          refine ⟨170279060140420287910627117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227038746853893717214169489 170279060140420287910627117)
          ·
            refine ⟨63854647552657607966485169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170279060140420287910627117 63854647552657607966485169)
            ·
              refine ⟨47890985664493205974863877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63854647552657607966485169 47890985664493205974863877)
              ·
                refine ⟨8979559812092476120286977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47890985664493205974863877 8979559812092476120286977)
                ·
                  refine ⟨6734669859069357090215233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8979559812092476120286977 6734669859069357090215233)
                  ·
                    refine ⟨5051002394302017817661425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734669859069357090215233 5051002394302017817661425)
                    ·
                      refine ⟨3788251795726513363246069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051002394302017817661425 3788251795726513363246069)
                      ·
                        rfl

theorem cell23_7377594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_7377594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377594 prefixEnd_7377594 := by exact prefixLift 7377594
  have htrace : WordTrace (prefixWord ++ tailWord_7377594) baseStart_7377594 baseEnd_7377594 := by
    simpa [prefixWord, tailWord_7377594, baseEnd_7377594] using wordTrace_append hprefix tailTrace_7377594
  have hstable : (prefixWord ++ tailWord_7377594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377594).length < 2 ^ (prefixWord ++ tailWord_7377594).sum := by decide
  have hdescent : baseEnd_7377594 < baseStart_7377594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377600 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 7]
def baseStart_7377600 : Nat := 118140960795 + 7377600 * 2 ^ 59
def prefixEnd_7377600 : Nat := 4983230072969 + 3 ^ 40 * 7377600 * 2
def baseEnd_7377600 : Nat := 420917208512271148863449

theorem tailTrace_7377600 : CollatzResearch.WordTrace tailWord_7377600 prefixEnd_7377600 420917208512271148863449 := by
  unfold tailWord_7377600
  simp only [CollatzResearch.WordTrace]
  refine ⟨134541589036111334305941127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179388785381481779074588169 134541589036111334305941127)
  ·
    refine ⟨201812383554167001458911691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134541589036111334305941127 201812383554167001458911691)
    ·
      refine ⟨302718575331250502188367537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201812383554167001458911691 302718575331250502188367537)
      ·
        refine ⟨227038931498437876641275653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302718575331250502188367537 227038931498437876641275653)
        ·
          refine ⟨42569799655957101870239185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227038931498437876641275653 42569799655957101870239185)
          ·
            refine ⟨31927349741967826402679389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42569799655957101870239185 31927349741967826402679389)
            ·
              refine ⟨11972756153237934901004771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31927349741967826402679389 11972756153237934901004771)
              ·
                refine ⟨17959134229856902351507157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11972756153237934901004771 17959134229856902351507157)
                ·
                  refine ⟨420917208512271148863449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17959134229856902351507157 420917208512271148863449)
                  ·
                    rfl

theorem cell23_7377600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_7377600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377600 prefixEnd_7377600 := by exact prefixLift 7377600
  have htrace : WordTrace (prefixWord ++ tailWord_7377600) baseStart_7377600 baseEnd_7377600 := by
    simpa [prefixWord, tailWord_7377600, baseEnd_7377600] using wordTrace_append hprefix tailTrace_7377600
  have hstable : (prefixWord ++ tailWord_7377600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377600).length < 2 ^ (prefixWord ++ tailWord_7377600).sum := by decide
  have hdescent : baseEnd_7377600 < baseStart_7377600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377690 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_7377690 : Nat := 118140960795 + 7377690 * 2 ^ 59
def prefixEnd_7377690 : Nat := 4983230072969 + 3 ^ 40 * 7377690 * 2
def baseEnd_7377690 : Nat := 420922343318816109738403

theorem tailTrace_7377690 : CollatzResearch.WordTrace tailWord_7377690 prefixEnd_7377690 420922343318816109738403 := by
  unfold tailWord_7377690
  simp only [CollatzResearch.WordTrace]
  refine ⟨67271615160474153495664631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179390973761264409321772349 67271615160474153495664631)
  ·
    refine ⟨100907422740711230243496947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67271615160474153495664631 100907422740711230243496947)
    ·
      refine ⟨151361134111066845365245421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100907422740711230243496947 151361134111066845365245421)
      ·
        refine ⟨56760425291650067011967033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151361134111066845365245421 56760425291650067011967033)
        ·
          refine ⟨42570318968737550258975275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56760425291650067011967033 42570318968737550258975275)
          ·
            refine ⟨63855478453106325388462913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42570318968737550258975275 63855478453106325388462913)
            ·
              refine ⟨47891608839829744041347185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63855478453106325388462913 47891608839829744041347185)
              ·
                refine ⟨35918706629872308031010389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47891608839829744041347185 35918706629872308031010389)
                ·
                  refine ⟨420922343318816109738403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35918706629872308031010389 420922343318816109738403)
                  ·
                    rfl

theorem cell23_7377690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_7377690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377690 prefixEnd_7377690 := by exact prefixLift 7377690
  have htrace : WordTrace (prefixWord ++ tailWord_7377690) baseStart_7377690 baseEnd_7377690 := by
    simpa [prefixWord, tailWord_7377690, baseEnd_7377690] using wordTrace_append hprefix tailTrace_7377690
  have hstable : (prefixWord ++ tailWord_7377690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377690).length < 2 ^ (prefixWord ++ tailWord_7377690).sum := by decide
  have hdescent : baseEnd_7377690 < baseStart_7377690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377737 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 1, 5]
def baseStart_7377737 : Nat := 118140960795 + 7377737 * 2 ^ 59
def prefixEnd_7377737 : Nat := 4983230072969 + 3 ^ 40 * 7377737 * 2
def baseEnd_7377737 : Nat := 1262775074486702101252637

theorem tailTrace_7377737 : CollatzResearch.WordTrace tailWord_7377737 prefixEnd_7377737 1262775074486702101252637 := by
  unfold tailWord_7377737
  simp only [CollatzResearch.WordTrace]
  refine ⟨269088174872726341009619465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179392116581817560673079643 269088174872726341009619465)
  ·
    refine ⟨201816131154544755757214599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269088174872726341009619465 201816131154544755757214599)
    ·
      refine ⟨302724196731817133635821899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201816131154544755757214599 302724196731817133635821899)
      ·
        refine ⟨454086295097725700453732849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302724196731817133635821899 454086295097725700453732849)
        ·
          refine ⟨340564721323294275340299637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454086295097725700453732849 340564721323294275340299637)
          ·
            refine ⟨31927942624058838313153091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 340564721323294275340299637 31927942624058838313153091)
            ·
              refine ⟨47891913936088257469729637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31927942624058838313153091 47891913936088257469729637)
              ·
                refine ⟨8979733863016548275574307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47891913936088257469729637 8979733863016548275574307)
                ·
                  refine ⟨13469600794524822413361461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979733863016548275574307 13469600794524822413361461)
                  ·
                    refine ⟨1262775074486702101252637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13469600794524822413361461 1262775074486702101252637)
                    ·
                      rfl

theorem cell23_7377737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_7377737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377737 prefixEnd_7377737 := by exact prefixLift 7377737
  have htrace : WordTrace (prefixWord ++ tailWord_7377737) baseStart_7377737 baseEnd_7377737 := by
    simpa [prefixWord, tailWord_7377737, baseEnd_7377737] using wordTrace_append hprefix tailTrace_7377737
  have hstable : (prefixWord ++ tailWord_7377737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377737).length < 2 ^ (prefixWord ++ tailWord_7377737).sum := by decide
  have hdescent : baseEnd_7377737 < baseStart_7377737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377777 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_7377777 : Nat := 118140960795 + 7377777 * 2 ^ 59
def prefixEnd_7377777 : Nat := 4983230072969 + 3 ^ 40 * 7377777 * 2
def baseEnd_7377777 : Nat := 3788345762686286147257727

theorem tailTrace_7377777 : CollatzResearch.WordTrace tailWord_7377777 prefixEnd_7377777 3788345762686286147257727 := by
  unfold tailWord_7377777
  simp only [CollatzResearch.WordTrace]
  refine ⟨269089633792581427841075585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179393089195054285227383723 269089633792581427841075585)
  ·
    refine ⟨201817225344436070880806689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269089633792581427841075585 201817225344436070880806689)
    ·
      refine ⟨151362919008327053160605017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201817225344436070880806689 151362919008327053160605017)
      ·
        refine ⟨113522189256245289870453763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151362919008327053160605017 113522189256245289870453763)
        ·
          refine ⟨170283283884367934805680645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113522189256245289870453763 170283283884367934805680645)
          ·
            refine ⟨31928115728318987776065121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170283283884367934805680645 31928115728318987776065121)
            ·
              refine ⟨23946086796239240832048841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31928115728318987776065121 23946086796239240832048841)
              ·
                refine ⟨17959565097179430624036631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23946086796239240832048841 17959565097179430624036631)
                ·
                  refine ⟨26939347645769145936054947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17959565097179430624036631 26939347645769145936054947)
                  ·
                    refine ⟨40409021468653718904082421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26939347645769145936054947 40409021468653718904082421)
                    ·
                      refine ⟨3788345762686286147257727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40409021468653718904082421 3788345762686286147257727)
                      ·
                        rfl

theorem cell23_7377777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_7377777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377777 prefixEnd_7377777 := by exact prefixLift 7377777
  have htrace : WordTrace (prefixWord ++ tailWord_7377777) baseStart_7377777 baseEnd_7377777 := by
    simpa [prefixWord, tailWord_7377777, baseEnd_7377777] using wordTrace_append hprefix tailTrace_7377777
  have hstable : (prefixWord ++ tailWord_7377777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377777).length < 2 ^ (prefixWord ++ tailWord_7377777).sum := by decide
  have hdescent : baseEnd_7377777 < baseStart_7377777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377824 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 4, 1, 3]
def baseStart_7377824 : Nat := 118140960795 + 7377824 * 2 ^ 59
def prefixEnd_7377824 : Nat := 4983230072969 + 3 ^ 40 * 7377824 * 2
def baseEnd_7377824 : Nat := 3788369896277047463370011

theorem tailTrace_7377824 : CollatzResearch.WordTrace tailWord_7377824 prefixEnd_7377824 3788369896277047463370011 := by
  unfold tailWord_7377824
  simp only [CollatzResearch.WordTrace]
  refine ⟨134545674011705577434018263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179394232015607436578691017 134545674011705577434018263)
  ·
    refine ⟨201818511017558366151027395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134545674011705577434018263 201818511017558366151027395)
    ·
      refine ⟨302727766526337549226541093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201818511017558366151027395 302727766526337549226541093)
      ·
        refine ⟨56761456223688290479976455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302727766526337549226541093 56761456223688290479976455)
        ·
          refine ⟨85142184335532435719964683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56761456223688290479976455 85142184335532435719964683)
          ·
            refine ⟨127713276503298653579947025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85142184335532435719964683 127713276503298653579947025)
            ·
              refine ⟨95784957377473990184960269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127713276503298653579947025 95784957377473990184960269)
              ·
                refine ⟨35919359016552746319360101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95784957377473990184960269 35919359016552746319360101)
                ·
                  refine ⟨6734879815603639934880019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35919359016552746319360101 6734879815603639934880019)
                  ·
                    refine ⟨10102319723405459902320029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6734879815603639934880019 10102319723405459902320029)
                    ·
                      refine ⟨3788369896277047463370011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10102319723405459902320029 3788369896277047463370011)
                      ·
                        rfl

theorem cell23_7377824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_7377824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377824 prefixEnd_7377824 := by exact prefixLift 7377824
  have htrace : WordTrace (prefixWord ++ tailWord_7377824) baseStart_7377824 baseEnd_7377824 := by
    simpa [prefixWord, tailWord_7377824, baseEnd_7377824] using wordTrace_append hprefix tailTrace_7377824
  have hstable : (prefixWord ++ tailWord_7377824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377824).length < 2 ^ (prefixWord ++ tailWord_7377824).sum := by decide
  have hdescent : baseEnd_7377824 < baseStart_7377824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377825 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7377825 : Nat := 118140960795 + 7377825 * 2 ^ 59
def prefixEnd_7377825 : Nat := 4983230072969 + 3 ^ 40 * 7377825 * 2
def baseEnd_7377825 : Nat := 3788370409757701959457507

theorem tailTrace_7377825 : CollatzResearch.WordTrace tailWord_7377825 prefixEnd_7377825 3788370409757701959457507 := by
  unfold tailWord_7377825
  simp only [CollatzResearch.WordTrace]
  refine ⟨269091384496407532038822929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179394256330938354692548619 269091384496407532038822929)
  ·
    refine ⟨201818538372305649029117197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269091384496407532038822929 201818538372305649029117197)
    ·
      refine ⟨75681951889614618385918949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201818538372305649029117197 75681951889614618385918949)
      ·
        refine ⟨14190365979302740947359803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75681951889614618385918949 14190365979302740947359803)
        ·
          refine ⟨21285548968954111421039705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14190365979302740947359803 21285548968954111421039705)
          ·
            refine ⟨15964161726715583565779779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21285548968954111421039705 15964161726715583565779779)
            ·
              refine ⟨23946242590073375348669669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15964161726715583565779779 23946242590073375348669669)
              ·
                refine ⟨4489920485638757877875563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23946242590073375348669669 4489920485638757877875563)
                ·
                  refine ⟨6734880728458136816813345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489920485638757877875563 6734880728458136816813345)
                  ·
                    refine ⟨5051160546343602612610009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734880728458136816813345 5051160546343602612610009)
                    ·
                      refine ⟨3788370409757701959457507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051160546343602612610009 3788370409757701959457507)
                      ·
                        rfl

theorem cell23_7377825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7377825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377825 prefixEnd_7377825 := by exact prefixLift 7377825
  have htrace : WordTrace (prefixWord ++ tailWord_7377825) baseStart_7377825 baseEnd_7377825 := by
    simpa [prefixWord, tailWord_7377825, baseEnd_7377825] using wordTrace_append hprefix tailTrace_7377825
  have hstable : (prefixWord ++ tailWord_7377825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377825).length < 2 ^ (prefixWord ++ tailWord_7377825).sum := by decide
  have hdescent : baseEnd_7377825 < baseStart_7377825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377831 : List Nat := [1, 1, 6, 1, 4, 1, 1, 8]
def baseStart_7377831 : Nat := 118140960795 + 7377831 * 2 ^ 59
def prefixEnd_7377831 : Nat := 4983230072969 + 3 ^ 40 * 7377831 * 2
def baseEnd_7377831 : Nat := 140310129283023293925277

theorem tailTrace_7377831 : CollatzResearch.WordTrace tailWord_7377831 prefixEnd_7377831 140310129283023293925277 := by
  unfold tailWord_7377831
  simp only [CollatzResearch.WordTrace]
  refine ⟨269091603334385795063541347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179394402222923863375694231 269091603334385795063541347)
  ·
    refine ⟨403637405001578692595312021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269091603334385795063541347 403637405001578692595312021)
    ·
      refine ⟨18920503359449001215405251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 403637405001578692595312021 18920503359449001215405251)
      ·
        refine ⟨28380755039173501823107877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18920503359449001215405251 28380755039173501823107877)
        ·
          refine ⟨5321391569845031591832727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28380755039173501823107877 5321391569845031591832727)
          ·
            refine ⟨7982087354767547387749091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321391569845031591832727 7982087354767547387749091)
            ·
              refine ⟨11973131032151321081623637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982087354767547387749091 11973131032151321081623637)
              ·
                refine ⟨140310129283023293925277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11973131032151321081623637 140310129283023293925277)
                ·
                  rfl

theorem cell23_7377831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 8].length) (baseStart_7377831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377831 prefixEnd_7377831 := by exact prefixLift 7377831
  have htrace : WordTrace (prefixWord ++ tailWord_7377831) baseStart_7377831 baseEnd_7377831 := by
    simpa [prefixWord, tailWord_7377831, baseEnd_7377831] using wordTrace_append hprefix tailTrace_7377831
  have hstable : (prefixWord ++ tailWord_7377831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377831).length < 2 ^ (prefixWord ++ tailWord_7377831).sum := by decide
  have hdescent : baseEnd_7377831 < baseStart_7377831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377841 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7377841 : Nat := 118140960795 + 7377841 * 2 ^ 59
def prefixEnd_7377841 : Nat := 4983230072969 + 3 ^ 40 * 7377841 * 2
def baseEnd_7377841 : Nat := 3788378625448173896857433

theorem tailTrace_7377841 : CollatzResearch.WordTrace tailWord_7377841 prefixEnd_7377841 3788378625448173896857433 := by
  unfold tailWord_7377841
  simp only [CollatzResearch.WordTrace]
  refine ⟨269091968064349566771405377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179394645376233044514270251 269091968064349566771405377)
  ·
    refine ⟨201818976048262175078554033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269091968064349566771405377 201818976048262175078554033)
    ·
      refine ⟨151364232036196631308915525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201818976048262175078554033 151364232036196631308915525)
      ·
        refine ⟨28380793506786868370421661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151364232036196631308915525 28380793506786868370421661)
        ·
          refine ⟨10642797565045075638908123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28380793506786868370421661 10642797565045075638908123)
          ·
            refine ⟨15964196347567613458362185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10642797565045075638908123 15964196347567613458362185)
            ·
              refine ⟨11973147260675710093771639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15964196347567613458362185 11973147260675710093771639)
              ·
                refine ⟨17959720891013565140657459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973147260675710093771639 17959720891013565140657459)
                ·
                  refine ⟨26939581336520347710986189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17959720891013565140657459 26939581336520347710986189)
                  ·
                    refine ⟨10102343001195130391619821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26939581336520347710986189 10102343001195130391619821)
                    ·
                      refine ⟨3788378625448173896857433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10102343001195130391619821 3788378625448173896857433)
                      ·
                        rfl

theorem cell23_7377841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7377841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377841 prefixEnd_7377841 := by exact prefixLift 7377841
  have htrace : WordTrace (prefixWord ++ tailWord_7377841) baseStart_7377841 baseEnd_7377841 := by
    simpa [prefixWord, tailWord_7377841, baseEnd_7377841] using wordTrace_append hprefix tailTrace_7377841
  have hstable : (prefixWord ++ tailWord_7377841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377841).length < 2 ^ (prefixWord ++ tailWord_7377841).sum := by decide
  have hdescent : baseEnd_7377841 < baseStart_7377841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377869 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7377869 : Nat := 118140960795 + 7377869 * 2 ^ 59
def prefixEnd_7377869 : Nat := 4983230072969 + 3 ^ 40 * 7377869 * 2
def baseEnd_7377869 : Nat := 1262797667635499929102435

theorem tailTrace_7377869 : CollatzResearch.WordTrace tailWord_7377869 prefixEnd_7377869 1262797667635499929102435 := by
  unfold tailWord_7377869
  simp only [CollatzResearch.WordTrace]
  refine ⟨269092989308248127553424661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179395326205498751702283107 269092989308248127553424661)
  ·
    refine ⟨12613733873824130979066781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269092989308248127553424661 12613733873824130979066781)
    ·
      refine ⟨4730150202684049117150043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12613733873824130979066781 4730150202684049117150043)
      ·
        refine ⟨7095225304026073675725065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730150202684049117150043 7095225304026073675725065)
        ·
          refine ⟨5321418978019555256793799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7095225304026073675725065 5321418978019555256793799)
          ·
            refine ⟨7982128467029332885190699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321418978019555256793799 7982128467029332885190699)
            ·
              refine ⟨11973192700543999327786049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982128467029332885190699 11973192700543999327786049)
              ·
                refine ⟨8979894525407999495839537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11973192700543999327786049 8979894525407999495839537)
                ·
                  refine ⟨6734920894055999621879653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8979894525407999495839537 6734920894055999621879653)
                  ·
                    refine ⟨1262797667635499929102435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6734920894055999621879653 1262797667635499929102435)
                    ·
                      rfl

theorem cell23_7377869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7377869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377869 prefixEnd_7377869 := by exact prefixLift 7377869
  have htrace : WordTrace (prefixWord ++ tailWord_7377869) baseStart_7377869 baseEnd_7377869 := by
    simpa [prefixWord, tailWord_7377869, baseEnd_7377869] using wordTrace_append hprefix tailTrace_7377869
  have hstable : (prefixWord ++ tailWord_7377869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377869).length < 2 ^ (prefixWord ++ tailWord_7377869).sum := by decide
  have hdescent : baseEnd_7377869 < baseStart_7377869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377874 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_7377874 : Nat := 118140960795 + 7377874 * 2 ^ 59
def prefixEnd_7377874 : Nat := 4983230072969 + 3 ^ 40 * 7377874 * 2
def baseEnd_7377874 : Nat := 1262798523436590755914927

theorem tailTrace_7377874 : CollatzResearch.WordTrace tailWord_7377874 prefixEnd_7377874 1262798523436590755914927 := by
  unfold tailWord_7377874
  simp only [CollatzResearch.WordTrace]
  refine ⟨67273292918307503351839169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179395447782153342271571117 67273292918307503351839169)
  ·
    refine ⟨50454969688730627513879377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67273292918307503351839169 50454969688730627513879377)
    ·
      refine ⟨37841227266547970635409533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50454969688730627513879377 37841227266547970635409533)
      ·
        refine ⟨14190460224955488988278575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37841227266547970635409533 14190460224955488988278575)
        ·
          refine ⟨21285690337433233482417863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14190460224955488988278575 21285690337433233482417863)
          ·
            refine ⟨31928535506149850223626795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21285690337433233482417863 31928535506149850223626795)
            ·
              refine ⟨47892803259224775335440193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31928535506149850223626795 47892803259224775335440193)
              ·
                refine ⟨35919602444418581501580145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47892803259224775335440193 35919602444418581501580145)
                ·
                  refine ⟨26939701833313936126185109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35919602444418581501580145 26939701833313936126185109)
                  ·
                    refine ⟨1262798523436590755914927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26939701833313936126185109 1262798523436590755914927)
                    ·
                      rfl

theorem cell23_7377874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_7377874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377874 prefixEnd_7377874 := by exact prefixLift 7377874
  have htrace : WordTrace (prefixWord ++ tailWord_7377874) baseStart_7377874 baseEnd_7377874 := by
    simpa [prefixWord, tailWord_7377874, baseEnd_7377874] using wordTrace_append hprefix tailTrace_7377874
  have hstable : (prefixWord ++ tailWord_7377874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377874).length < 2 ^ (prefixWord ++ tailWord_7377874).sum := by decide
  have hdescent : baseEnd_7377874 < baseStart_7377874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377898 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_7377898 : Nat := 118140960795 + 7377898 * 2 ^ 59
def prefixEnd_7377898 : Nat := 4983230072969 + 3 ^ 40 * 7377898 * 2
def baseEnd_7377898 : Nat := 3788407893845480173844671

theorem tailTrace_7377898 : CollatzResearch.WordTrace tailWord_7377898 prefixEnd_7377898 3788407893845480173844671 := by
  unfold tailWord_7377898
  simp only [CollatzResearch.WordTrace]
  refine ⟨67273511756285766376557587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179396031350095377004153565 67273511756285766376557587)
  ·
    refine ⟨100910267634428649564836381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67273511756285766376557587 100910267634428649564836381)
    ·
      refine ⟨37841350362910743586813643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100910267634428649564836381 37841350362910743586813643)
      ·
        refine ⟨56762025544366115380220465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37841350362910743586813643 56762025544366115380220465)
        ·
          refine ⟨42571519158274586535165349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56762025544366115380220465 42571519158274586535165349)
          ·
            refine ⟨7982159842176484975343503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42571519158274586535165349 7982159842176484975343503)
            ·
              refine ⟨11973239763264727463015255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982159842176484975343503 11973239763264727463015255)
              ·
                refine ⟨17959859644897091194522883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973239763264727463015255 17959859644897091194522883)
                ·
                  refine ⟨26939789467345636791784325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17959859644897091194522883 26939789467345636791784325)
                  ·
                    refine ⟨5051210525127306898459561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26939789467345636791784325 5051210525127306898459561)
                    ·
                      refine ⟨3788407893845480173844671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051210525127306898459561 3788407893845480173844671)
                      ·
                        rfl

theorem cell23_7377898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_7377898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377898 prefixEnd_7377898 := by exact prefixLift 7377898
  have htrace : WordTrace (prefixWord ++ tailWord_7377898) baseStart_7377898 baseEnd_7377898 := by
    simpa [prefixWord, tailWord_7377898, baseEnd_7377898] using wordTrace_append hprefix tailTrace_7377898
  have hstable : (prefixWord ++ tailWord_7377898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377898).length < 2 ^ (prefixWord ++ tailWord_7377898).sum := by decide
  have hdescent : baseEnd_7377898 < baseStart_7377898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377921 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 5]
def baseStart_7377921 : Nat := 118140960795 + 7377921 * 2 ^ 59
def prefixEnd_7377921 : Nat := 4983230072969 + 3 ^ 40 * 7377921 * 2
def baseEnd_7377921 : Nat := 420935522655614842650785

theorem tailTrace_7377921 : CollatzResearch.WordTrace tailWord_7377921 prefixEnd_7377921 420935522655614842650785 := by
  unfold tailWord_7377921
  simp only [CollatzResearch.WordTrace]
  refine ⟨269094885904059740434317617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179396590602706493622878411 269094885904059740434317617)
  ·
    refine ⟨201821164428044805325738213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269094885904059740434317617 201821164428044805325738213)
    ·
      refine ⟨37841468330258400998575915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201821164428044805325738213 37841468330258400998575915)
      ·
        refine ⟨56762202495387601497863873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37841468330258400998575915 56762202495387601497863873)
        ·
          refine ⟨42571651871540701123397905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56762202495387601497863873 42571651871540701123397905)
          ·
            refine ⟨31928738903655525842548429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42571651871540701123397905 31928738903655525842548429)
            ·
              refine ⟨11973277088870822190955661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31928738903655525842548429 11973277088870822190955661)
              ·
                refine ⟨4489978908326558321608373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11973277088870822190955661 4489978908326558321608373)
                ·
                  refine ⟨420935522655614842650785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4489978908326558321608373 420935522655614842650785)
                  ·
                    rfl

theorem cell23_7377921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 5].length) (baseStart_7377921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377921 prefixEnd_7377921 := by exact prefixLift 7377921
  have htrace : WordTrace (prefixWord ++ tailWord_7377921) baseStart_7377921 baseEnd_7377921 := by
    simpa [prefixWord, tailWord_7377921, baseEnd_7377921] using wordTrace_append hprefix tailTrace_7377921
  have hstable : (prefixWord ++ tailWord_7377921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377921).length < 2 ^ (prefixWord ++ tailWord_7377921).sum := by decide
  have hdescent : baseEnd_7377921 < baseStart_7377921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377934 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7377934 : Nat := 118140960795 + 7377934 * 2 ^ 59
def prefixEnd_7377934 : Nat := 4983230072969 + 3 ^ 40 * 7377934 * 2
def baseEnd_7377934 : Nat := 1262808793049680677664835

theorem tailTrace_7377934 : CollatzResearch.WordTrace tailWord_7377934 prefixEnd_7377934 1262808793049680677664835 := by
  unfold tailWord_7377934
  simp only [CollatzResearch.WordTrace]
  refine ⟨33636920006626580456817607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179396906702008429103027237 33636920006626580456817607)
  ·
    refine ⟨50455380009939870685226411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33636920006626580456817607 50455380009939870685226411)
    ·
      refine ⟨75683070014909806027839617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50455380009939870685226411 75683070014909806027839617)
      ·
        refine ⟨56762302511182354520879713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75683070014909806027839617 56762302511182354520879713)
        ·
          refine ⟨42571726883386765890659785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56762302511182354520879713 42571726883386765890659785)
          ·
            refine ⟨31928795162540074417994839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42571726883386765890659785 31928795162540074417994839)
            ·
              refine ⟨47893192743810111626992259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31928795162540074417994839 47893192743810111626992259)
              ·
                refine ⟨71839789115715167440488389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47893192743810111626992259 71839789115715167440488389)
                ·
                  refine ⟨13469960459196593895091573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71839789115715167440488389 13469960459196593895091573)
                  ·
                    refine ⟨1262808793049680677664835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13469960459196593895091573 1262808793049680677664835)
                    ·
                      rfl

theorem cell23_7377934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7377934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377934 prefixEnd_7377934 := by exact prefixLift 7377934
  have htrace : WordTrace (prefixWord ++ tailWord_7377934) baseStart_7377934 baseEnd_7377934 := by
    simpa [prefixWord, tailWord_7377934, baseEnd_7377934] using wordTrace_append hprefix tailTrace_7377934
  have hstable : (prefixWord ++ tailWord_7377934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377934).length < 2 ^ (prefixWord ++ tailWord_7377934).sum := by decide
  have hdescent : baseEnd_7377934 < baseStart_7377934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377944 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7377944 : Nat := 118140960795 + 7377944 * 2 ^ 59
def prefixEnd_7377944 : Nat := 4983230072969 + 3 ^ 40 * 7377944 * 2
def baseEnd_7377944 : Nat := 3788431513955586993869459

theorem tailTrace_7377944 : CollatzResearch.WordTrace tailWord_7377944 prefixEnd_7377944 3788431513955586993869459 := by
  unfold tailWord_7377944
  simp only [CollatzResearch.WordTrace]
  refine ⟨134547862391488207681202443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179397149855317610241603257 134547862391488207681202443)
  ·
    refine ⟨201821793587232311521803665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134547862391488207681202443 201821793587232311521803665)
    ·
      refine ⟨151366345190424233641352749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201821793587232311521803665 151366345190424233641352749)
      ·
        refine ⟨56762379446409087615507281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151366345190424233641352749 56762379446409087615507281)
        ·
          refine ⟨42571784584806815711630461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56762379446409087615507281 42571784584806815711630461)
          ·
            refine ⟨15964419219302555891861423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42571784584806815711630461 15964419219302555891861423)
            ·
              refine ⟨23946628828953833837792135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15964419219302555891861423 23946628828953833837792135)
              ·
                refine ⟨35919943243430750756688203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23946628828953833837792135 35919943243430750756688203)
                ·
                  refine ⟨53879914865146126135032305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35919943243430750756688203 53879914865146126135032305)
                  ·
                    refine ⟨40409936148859594601274229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53879914865146126135032305 40409936148859594601274229)
                    ·
                      refine ⟨3788431513955586993869459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40409936148859594601274229 3788431513955586993869459)
                      ·
                        rfl

theorem cell23_7377944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7377944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377944 prefixEnd_7377944 := by exact prefixLift 7377944
  have htrace : WordTrace (prefixWord ++ tailWord_7377944) baseStart_7377944 baseEnd_7377944 := by
    simpa [prefixWord, tailWord_7377944, baseEnd_7377944] using wordTrace_append hprefix tailTrace_7377944
  have hstable : (prefixWord ++ tailWord_7377944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377944).length < 2 ^ (prefixWord ++ tailWord_7377944).sum := by decide
  have hdescent : baseEnd_7377944 < baseStart_7377944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377949 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_7377949 : Nat := 118140960795 + 7377949 * 2 ^ 59
def prefixEnd_7377949 : Nat := 4983230072969 + 3 ^ 40 * 7377949 * 2
def baseEnd_7377949 : Nat := 3788434081358859474306937

theorem tailTrace_7377949 : CollatzResearch.WordTrace tailWord_7377949 prefixEnd_7377949 3788434081358859474306937 := by
  unfold tailWord_7377949
  simp only [CollatzResearch.WordTrace]
  refine ⟨269095907147958301216336901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179397271431972200810891267 269095907147958301216336901)
  ·
    refine ⟨50455482590242181478063169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269095907147958301216336901 50455482590242181478063169)
    ·
      refine ⟨37841611942681636108547377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50455482590242181478063169 37841611942681636108547377)
      ·
        refine ⟨28381208957011227081410533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37841611942681636108547377 28381208957011227081410533)
        ·
          refine ⟨5321476679439605077764475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28381208957011227081410533 5321476679439605077764475)
          ·
            refine ⟨7982215019159407616646713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321476679439605077764475 7982215019159407616646713)
            ·
              refine ⟨5986661264369555712485035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982215019159407616646713 5986661264369555712485035)
              ·
                refine ⟨8979991896554333568727553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986661264369555712485035 8979991896554333568727553)
                ·
                  refine ⟨6734993922415750176545665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8979991896554333568727553 6734993922415750176545665)
                  ·
                    refine ⟨5051245441811812632409249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734993922415750176545665 5051245441811812632409249)
                    ·
                      refine ⟨3788434081358859474306937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051245441811812632409249 3788434081358859474306937)
                      ·
                        rfl

theorem cell23_7377949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_7377949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377949 prefixEnd_7377949 := by exact prefixLift 7377949
  have htrace : WordTrace (prefixWord ++ tailWord_7377949) baseStart_7377949 baseEnd_7377949 := by
    simpa [prefixWord, tailWord_7377949, baseEnd_7377949] using wordTrace_append hprefix tailTrace_7377949
  have hstable : (prefixWord ++ tailWord_7377949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377949).length < 2 ^ (prefixWord ++ tailWord_7377949).sum := by decide
  have hdescent : baseEnd_7377949 < baseStart_7377949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377964 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_7377964 : Nat := 118140960795 + 7377964 * 2 ^ 59
def prefixEnd_7377964 : Nat := 4983230072969 + 3 ^ 40 * 7377964 * 2
def baseEnd_7377964 : Nat := 1262813927856225638539789

theorem tailTrace_7377964 : CollatzResearch.WordTrace tailWord_7377964 prefixEnd_7377964 1262813927856225638539789 := by
  unfold tailWord_7377964
  simp only [CollatzResearch.WordTrace]
  refine ⟨134548227121451979389066473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179397636161935972518755297 134548227121451979389066473)
  ·
    refine ⟨100911170341088984541799855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134548227121451979389066473 100911170341088984541799855)
    ·
      refine ⟨151366755511633476812699783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100911170341088984541799855 151366755511633476812699783)
      ·
        refine ⟨227050133267450215219049675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151366755511633476812699783 227050133267450215219049675)
        ·
          refine ⟨340575199901175322828574513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227050133267450215219049675 340575199901175322828574513)
          ·
            refine ⟨255431399925881492121430885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340575199901175322828574513 255431399925881492121430885)
            ·
              refine ⟨47893387486102779772768291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255431399925881492121430885 47893387486102779772768291)
              ·
                refine ⟨71840081229154169659152437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47893387486102779772768291 71840081229154169659152437)
                ·
                  refine ⟨6735007615233203405545541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71840081229154169659152437 6735007615233203405545541)
                  ·
                    refine ⟨1262813927856225638539789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735007615233203405545541 1262813927856225638539789)
                    ·
                      rfl

theorem cell23_7377964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_7377964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377964 prefixEnd_7377964 := by exact prefixLift 7377964
  have htrace : WordTrace (prefixWord ++ tailWord_7377964) baseStart_7377964 baseEnd_7377964 := by
    simpa [prefixWord, tailWord_7377964, baseEnd_7377964] using wordTrace_append hprefix tailTrace_7377964
  have hstable : (prefixWord ++ tailWord_7377964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377964).length < 2 ^ (prefixWord ++ tailWord_7377964).sum := by decide
  have hdescent : baseEnd_7377964 < baseStart_7377964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377991 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_7377991 : Nat := 118140960795 + 7377991 * 2 ^ 59
def prefixEnd_7377991 : Nat := 4983230072969 + 3 ^ 40 * 7377991 * 2
def baseEnd_7377991 : Nat := 3788455647546348309981743

theorem tailTrace_7377991 : CollatzResearch.WordTrace tailWord_7377991 prefixEnd_7377991 3788455647546348309981743 := by
  unfold tailWord_7377991
  simp only [CollatzResearch.WordTrace]
  refine ⟨269097439013806142389365827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179398292675870761592910551 269097439013806142389365827)
  ·
    refine ⟨403646158520709213584048741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269097439013806142389365827 403646158520709213584048741)
    ·
      refine ⟨75683654722632977547009139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403646158520709213584048741 75683654722632977547009139)
      ·
        refine ⟨113525482083949466320513709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75683654722632977547009139 113525482083949466320513709)
        ·
          refine ⟨42572055781481049870192641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113525482083949466320513709 42572055781481049870192641)
          ·
            refine ⟨31929041836110787402644481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42572055781481049870192641 31929041836110787402644481)
            ·
              refine ⟨23946781377083090551983361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31929041836110787402644481 23946781377083090551983361)
              ·
                refine ⟨17960086032812317913987521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23946781377083090551983361 17960086032812317913987521)
                ·
                  refine ⟨13470064524609238435490641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17960086032812317913987521 13470064524609238435490641)
                  ·
                    refine ⟨10102548393456928826617981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13470064524609238435490641 10102548393456928826617981)
                    ·
                      refine ⟨3788455647546348309981743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10102548393456928826617981 3788455647546348309981743)
                      ·
                        rfl

theorem cell23_7377991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_7377991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377991 prefixEnd_7377991 := by exact prefixLift 7377991
  have htrace : WordTrace (prefixWord ++ tailWord_7377991) baseStart_7377991 baseEnd_7377991 := by
    simpa [prefixWord, tailWord_7377991, baseEnd_7377991] using wordTrace_append hprefix tailTrace_7377991
  have hstable : (prefixWord ++ tailWord_7377991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377991).length < 2 ^ (prefixWord ++ tailWord_7377991).sum := by decide
  have hdescent : baseEnd_7377991 < baseStart_7377991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377994 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_7377994 : Nat := 118140960795 + 7377994 * 2 ^ 59
def prefixEnd_7377994 : Nat := 4983230072969 + 3 ^ 40 * 7377994 * 2
def baseEnd_7377994 : Nat := 420939687554256866471581

theorem tailTrace_7377994 : CollatzResearch.WordTrace tailWord_7377994 prefixEnd_7377994 420939687554256866471581 := by
  unfold tailWord_7377994
  simp only [CollatzResearch.WordTrace]
  refine ⟨67274387108198818475431259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179398365621863515934483357 67274387108198818475431259)
  ·
    refine ⟨100911580662298227713146889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67274387108198818475431259 100911580662298227713146889)
    ·
      refine ⟨75683685496723670784860167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100911580662298227713146889 75683685496723670784860167)
      ·
        refine ⟨113525528245085506177290251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75683685496723670784860167 113525528245085506177290251)
        ·
          refine ⟨170288292367628259265935377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113525528245085506177290251 170288292367628259265935377)
          ·
            refine ⟨127716219275721194449451533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170288292367628259265935377 127716219275721194449451533)
            ·
              refine ⟨47893582228395447918544325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127716219275721194449451533 47893582228395447918544325)
              ·
                refine ⟨8980046667824146484727061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47893582228395447918544325 8980046667824146484727061)
                ·
                  refine ⟨420939687554256866471581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8980046667824146484727061 420939687554256866471581)
                  ·
                    rfl

theorem cell23_7377994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_7377994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377994 prefixEnd_7377994 := by exact prefixLift 7377994
  have htrace : WordTrace (prefixWord ++ tailWord_7377994) baseStart_7377994 baseEnd_7377994 := by
    simpa [prefixWord, tailWord_7377994, baseEnd_7377994] using wordTrace_append hprefix tailTrace_7377994
  have hstable : (prefixWord ++ tailWord_7377994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377994).length < 2 ^ (prefixWord ++ tailWord_7377994).sum := by decide
  have hdescent : baseEnd_7377994 < baseStart_7377994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7377998 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_7377998 : Nat := 118140960795 + 7377998 * 2 ^ 59
def prefixEnd_7377998 : Nat := 4983230072969 + 3 ^ 40 * 7377998 * 2
def baseEnd_7377998 : Nat := 1262819747303643260864737

theorem tailTrace_7377998 : CollatzResearch.WordTrace tailWord_7377998 prefixEnd_7377998 1262819747303643260864737 := by
  unfold tailWord_7377998
  simp only [CollatzResearch.WordTrace]
  refine ⟨33637211790597597823108831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179398462883187188389913765 33637211790597597823108831)
  ·
    refine ⟨50455817685896396734663247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33637211790597597823108831 50455817685896396734663247)
    ·
      refine ⟨75683726528844595101994871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50455817685896396734663247 75683726528844595101994871)
      ·
        refine ⟨113525589793266892652992307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75683726528844595101994871 113525589793266892652992307)
        ·
          refine ⟨170288384689900338979488461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113525589793266892652992307 170288384689900338979488461)
          ·
            refine ⟨63858144258712627117308173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170288384689900338979488461 63858144258712627117308173)
            ·
              refine ⟨23946804097017235168990565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63858144258712627117308173 23946804097017235168990565)
              ·
                refine ⟨4490025768190731594185731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23946804097017235168990565 4490025768190731594185731)
                ·
                  refine ⟨6735038652286097391278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490025768190731594185731 6735038652286097391278597)
                  ·
                    refine ⟨1262819747303643260864737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735038652286097391278597 1262819747303643260864737)
                    ·
                      rfl

theorem cell23_7377998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_7377998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7377998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7377998 prefixEnd_7377998 := by exact prefixLift 7377998
  have htrace : WordTrace (prefixWord ++ tailWord_7377998) baseStart_7377998 baseEnd_7377998 := by
    simpa [prefixWord, tailWord_7377998, baseEnd_7377998] using wordTrace_append hprefix tailTrace_7377998
  have hstable : (prefixWord ++ tailWord_7377998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7377998).length < 2 ^ (prefixWord ++ tailWord_7377998).sum := by decide
  have hdescent : baseEnd_7377998 < baseStart_7377998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7377998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378031 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 1, 5, 2]
def baseStart_7378031 : Nat := 118140960795 + 7378031 * 2 ^ 59
def prefixEnd_7378031 : Nat := 4983230072969 + 3 ^ 40 * 7378031 * 2
def baseEnd_7378031 : Nat := 3788476186772528153481559

theorem tailTrace_7378031 : CollatzResearch.WordTrace tailWord_7378031 prefixEnd_7378031 3788476186772528153481559 := by
  unfold tailWord_7378031
  simp only [CollatzResearch.WordTrace]
  refine ⟨269098897933661229220821947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179399265289107486147214631 269098897933661229220821947)
  ·
    refine ⟨403648346900491843831232921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269098897933661229220821947 403648346900491843831232921)
    ·
      refine ⟨302736260175368882873424691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403648346900491843831232921 302736260175368882873424691)
      ·
        refine ⟨454104390263053324310137037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302736260175368882873424691 454104390263053324310137037)
        ·
          refine ⟨170289146348644996616301389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454104390263053324310137037 170289146348644996616301389)
          ·
            refine ⟨63858429880741873731113021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170289146348644996616301389 63858429880741873731113021)
            ·
              refine ⟨23946911205278202649167383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63858429880741873731113021 23946911205278202649167383)
              ·
                refine ⟨35920366807917303973751075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23946911205278202649167383 35920366807917303973751075)
                ·
                  refine ⟨53880550211875955960626613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35920366807917303973751075 53880550211875955960626613)
                  ·
                    refine ⟨5051301582363370871308745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53880550211875955960626613 5051301582363370871308745)
                    ·
                      refine ⟨3788476186772528153481559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051301582363370871308745 3788476186772528153481559)
                      ·
                        rfl

theorem cell23_7378031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5, 2].length) (baseStart_7378031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378031 prefixEnd_7378031 := by exact prefixLift 7378031
  have htrace : WordTrace (prefixWord ++ tailWord_7378031) baseStart_7378031 baseEnd_7378031 := by
    simpa [prefixWord, tailWord_7378031, baseEnd_7378031] using wordTrace_append hprefix tailTrace_7378031
  have hstable : (prefixWord ++ tailWord_7378031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378031).length < 2 ^ (prefixWord ++ tailWord_7378031).sum := by decide
  have hdescent : baseEnd_7378031 < baseStart_7378031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378038 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7378038 : Nat := 118140960795 + 7378038 * 2 ^ 59
def prefixEnd_7378038 : Nat := 4983230072969 + 3 ^ 40 * 7378038 * 2
def baseEnd_7378038 : Nat := 3788479781137109626094027

theorem tailTrace_7378038 : CollatzResearch.WordTrace tailWord_7378038 prefixEnd_7378038 3788479781137109626094027 := by
  unfold tailWord_7378038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16818697077789741838520423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179399435496423912944217845 16818697077789741838520423)
  ·
    refine ⟨25228045616684612757780635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16818697077789741838520423 25228045616684612757780635)
    ·
      refine ⟨37842068425026919136670953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25228045616684612757780635 37842068425026919136670953)
      ·
        refine ⟨28381551318770189352503215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37842068425026919136670953 28381551318770189352503215)
        ·
          refine ⟨42572326978155284028754823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28381551318770189352503215 42572326978155284028754823)
          ·
            refine ⟨63858490467232926043132235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42572326978155284028754823 63858490467232926043132235)
            ·
              refine ⟨95787735700849389064698353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63858490467232926043132235 95787735700849389064698353)
              ·
                refine ⟨71840801775637041798523765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95787735700849389064698353 71840801775637041798523765)
                ·
                  refine ⟨6735075166465972668611603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71840801775637041798523765 6735075166465972668611603)
                  ·
                    refine ⟨10102612749698959002917405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6735075166465972668611603 10102612749698959002917405)
                    ·
                      refine ⟨3788479781137109626094027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10102612749698959002917405 3788479781137109626094027)
                      ·
                        rfl

theorem cell23_7378038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7378038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378038 prefixEnd_7378038 := by exact prefixLift 7378038
  have htrace : WordTrace (prefixWord ++ tailWord_7378038) baseStart_7378038 baseEnd_7378038 := by
    simpa [prefixWord, tailWord_7378038, baseEnd_7378038] using wordTrace_append hprefix tailTrace_7378038
  have hstable : (prefixWord ++ tailWord_7378038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378038).length < 2 ^ (prefixWord ++ tailWord_7378038).sum := by decide
  have hdescent : baseEnd_7378038 < baseStart_7378038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378064 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_7378064 : Nat := 118140960795 + 7378064 * 2 ^ 59
def prefixEnd_7378064 : Nat := 4983230072969 + 3 ^ 40 * 7378064 * 2
def baseEnd_7378064 : Nat := 3788493131634126524368907

theorem tailTrace_7378064 : CollatzResearch.WordTrace tailWord_7378064 prefixEnd_7378064 3788493131634126524368907 := by
  unfold tailWord_7378064
  simp only [CollatzResearch.WordTrace]
  refine ⟨134550050771270837928386623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179400067695027783904515497 134550050771270837928386623)
  ·
    refine ⟨201825076156906256892579935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134550050771270837928386623 201825076156906256892579935)
    ·
      refine ⟨302737614235359385338869903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201825076156906256892579935 302737614235359385338869903)
      ·
        refine ⟨454106421353039078008304855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302737614235359385338869903 454106421353039078008304855)
        ·
          refine ⟨681159632029558617012457283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454106421353039078008304855 681159632029558617012457283)
          ·
            refine ⟨1021739448044337925518685925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681159632029558617012457283 1021739448044337925518685925)
            ·
              refine ⟨191576146508313361034753611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1021739448044337925518685925 191576146508313361034753611)
              ·
                refine ⟨287364219762470041552130417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191576146508313361034753611 287364219762470041552130417)
                ·
                  refine ⟨215523164821852531164097813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287364219762470041552130417 215523164821852531164097813)
                  ·
                    refine ⟨10102648351024337398317085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215523164821852531164097813 10102648351024337398317085)
                    ·
                      refine ⟨3788493131634126524368907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10102648351024337398317085 3788493131634126524368907)
                      ·
                        rfl

theorem cell23_7378064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_7378064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378064 prefixEnd_7378064 := by exact prefixLift 7378064
  have htrace : WordTrace (prefixWord ++ tailWord_7378064) baseStart_7378064 baseEnd_7378064 := by
    simpa [prefixWord, tailWord_7378064, baseEnd_7378064] using wordTrace_append hprefix tailTrace_7378064
  have hstable : (prefixWord ++ tailWord_7378064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378064).length < 2 ^ (prefixWord ++ tailWord_7378064).sum := by decide
  have hdescent : baseEnd_7378064 < baseStart_7378064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378071 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 1, 6]
def baseStart_7378071 : Nat := 118140960795 + 7378071 * 2 ^ 59
def prefixEnd_7378071 : Nat := 4983230072969 + 3 ^ 40 * 7378071 * 2
def baseEnd_7378071 : Nat := 1262832241999569332327125

theorem tailTrace_7378071 : CollatzResearch.WordTrace tailWord_7378071 prefixEnd_7378071 1262832241999569332327125 := by
  unfold tailWord_7378071
  simp only [CollatzResearch.WordTrace]
  refine ⟨269100356853516316052278067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179400237902344210701518711 269100356853516316052278067)
  ·
    refine ⟨403650535280274474078417101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269100356853516316052278067 403650535280274474078417101)
    ·
      refine ⟨151368950730102927779406413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403650535280274474078417101 151368950730102927779406413)
      ·
        refine ⟨56763356523788597917277405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151368950730102927779406413 56763356523788597917277405)
        ·
          refine ⟨21286258696420724218979027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56763356523788597917277405 21286258696420724218979027)
          ·
            refine ⟨31929388044631086328468541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21286258696420724218979027 31929388044631086328468541)
            ·
              refine ⟨11973520516736657373175703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31929388044631086328468541 11973520516736657373175703)
              ·
                refine ⟨17960280775104986059763555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973520516736657373175703 17960280775104986059763555)
                ·
                  refine ⟨26940421162657479089645333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17960280775104986059763555 26940421162657479089645333)
                  ·
                    refine ⟨1262832241999569332327125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26940421162657479089645333 1262832241999569332327125)
                    ·
                      rfl

theorem cell23_7378071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_7378071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378071 prefixEnd_7378071 := by exact prefixLift 7378071
  have htrace : WordTrace (prefixWord ++ tailWord_7378071) baseStart_7378071 baseEnd_7378071 := by
    simpa [prefixWord, tailWord_7378071, baseEnd_7378071] using wordTrace_append hprefix tailTrace_7378071
  have hstable : (prefixWord ++ tailWord_7378071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378071).length < 2 ^ (prefixWord ++ tailWord_7378071).sum := by decide
  have hdescent : baseEnd_7378071 < baseStart_7378071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378098 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_7378098 : Nat := 118140960795 + 7378098 * 2 ^ 59
def prefixEnd_7378098 : Nat := 4983230072969 + 3 ^ 40 * 7378098 * 2
def baseEnd_7378098 : Nat := 3788510589976379391343751

theorem tailTrace_7378098 : CollatzResearch.WordTrace tailWord_7378098 prefixEnd_7378098 3788510589976379391343751 := by
  unfold tailWord_7378098
  simp only [CollatzResearch.WordTrace]
  refine ⟨67275335406104624915877737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179400894416278999775673965 67275335406104624915877737)
  ·
    refine ⟨50456501554578468686908303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67275335406104624915877737 50456501554578468686908303)
    ·
      refine ⟨75684752331867703030362455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50456501554578468686908303 75684752331867703030362455)
      ·
        refine ⟨113527128497801554545543683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75684752331867703030362455 113527128497801554545543683)
        ·
          refine ⟨170290692746702331818315525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113527128497801554545543683 170290692746702331818315525)
          ·
            refine ⟨31929504890006687215934161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170290692746702331818315525 31929504890006687215934161)
            ·
              refine ⟨23947128667505015411950621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31929504890006687215934161 23947128667505015411950621)
              ·
                refine ⟨8980173250314380779481483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23947128667505015411950621 8980173250314380779481483)
                ·
                  refine ⟨13470259875471571169222225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8980173250314380779481483 13470259875471571169222225)
                  ·
                    refine ⟨10102694906603678376916669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13470259875471571169222225 10102694906603678376916669)
                    ·
                      refine ⟨3788510589976379391343751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10102694906603678376916669 3788510589976379391343751)
                      ·
                        rfl

theorem cell23_7378098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_7378098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378098 prefixEnd_7378098 := by exact prefixLift 7378098
  have htrace : WordTrace (prefixWord ++ tailWord_7378098) baseStart_7378098 baseEnd_7378098 := by
    simpa [prefixWord, tailWord_7378098, baseEnd_7378098] using wordTrace_append hprefix tailTrace_7378098
  have hstable : (prefixWord ++ tailWord_7378098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378098).length < 2 ^ (prefixWord ++ tailWord_7378098).sum := by decide
  have hdescent : baseEnd_7378098 < baseStart_7378098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378112 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 3, 2, 2]
def baseStart_7378112 : Nat := 118140960795 + 7378112 * 2 ^ 59
def prefixEnd_7378112 : Nat := 4983230072969 + 3 ^ 40 * 7378112 * 2
def baseEnd_7378112 : Nat := 3788517778705542336568687

theorem tailTrace_7378112 : CollatzResearch.WordTrace tailWord_7378112 prefixEnd_7378112 3788517778705542336568687 := by
  unfold tailWord_7378112
  simp only [CollatzResearch.WordTrace]
  refine ⟨134550926123183890027260295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179401234830911853369680393 134550926123183890027260295)
  ·
    refine ⟨201826389184775835040890443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134550926123183890027260295 201826389184775835040890443)
    ·
      refine ⟨302739583777163752561335665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201826389184775835040890443 302739583777163752561335665)
      ·
        refine ⟨227054687832872814421001749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302739583777163752561335665 227054687832872814421001749)
        ·
          refine ⟨10643188492165913175984457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227054687832872814421001749 10643188492165913175984457)
          ·
            refine ⟨7982391369124434881988343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10643188492165913175984457 7982391369124434881988343)
            ·
              refine ⟨11973587053686652322982515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982391369124434881988343 11973587053686652322982515)
              ·
                refine ⟨17960380580529978484473773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973587053686652322982515 17960380580529978484473773)
                ·
                  refine ⟨6735142717698741931677665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17960380580529978484473773 6735142717698741931677665)
                  ·
                    refine ⟨5051357038274056448758249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6735142717698741931677665 5051357038274056448758249)
                    ·
                      refine ⟨3788517778705542336568687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051357038274056448758249 3788517778705542336568687)
                      ·
                        rfl

theorem cell23_7378112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_7378112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378112 prefixEnd_7378112 := by exact prefixLift 7378112
  have htrace : WordTrace (prefixWord ++ tailWord_7378112) baseStart_7378112 baseEnd_7378112 := by
    simpa [prefixWord, tailWord_7378112, baseEnd_7378112] using wordTrace_append hprefix tailTrace_7378112
  have hstable : (prefixWord ++ tailWord_7378112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378112).length < 2 ^ (prefixWord ++ tailWord_7378112).sum := by decide
  have hdescent : baseEnd_7378112 < baseStart_7378112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378162 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7378162 : Nat := 118140960795 + 7378162 * 2 ^ 59
def prefixEnd_7378162 : Nat := 4983230072969 + 3 ^ 40 * 7378162 * 2
def baseEnd_7378162 : Nat := 3788543452738267140943457

theorem tailTrace_7378162 : CollatzResearch.WordTrace tailWord_7378162 prefixEnd_7378162 3788543452738267140943457 := by
  unfold tailWord_7378162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67275918974046659648460185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179402450597457759062560493 67275918974046659648460185)
  ·
    refine ⟨50456939230534994736345139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67275918974046659648460185 50456939230534994736345139)
    ·
      refine ⟨75685408845802492104517709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50456939230534994736345139 75685408845802492104517709)
      ·
        refine ⟨28382028317175934539194141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75685408845802492104517709 28382028317175934539194141)
        ·
          refine ⟨10643260618940975452197803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28382028317175934539194141 10643260618940975452197803)
          ·
            refine ⟨15964890928411463178296705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10643260618940975452197803 15964890928411463178296705)
            ·
              refine ⟨11973668196308597383722529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15964890928411463178296705 11973668196308597383722529)
              ·
                refine ⟨8980251147231448037791897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11973668196308597383722529 8980251147231448037791897)
                ·
                  refine ⟨6735188360423586028343923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8980251147231448037791897 6735188360423586028343923)
                  ·
                    refine ⟨10102782540635379042515885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6735188360423586028343923 10102782540635379042515885)
                    ·
                      refine ⟨3788543452738267140943457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10102782540635379042515885 3788543452738267140943457)
                      ·
                        rfl

theorem cell23_7378162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7378162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378162 prefixEnd_7378162 := by exact prefixLift 7378162
  have htrace : WordTrace (prefixWord ++ tailWord_7378162) baseStart_7378162 baseEnd_7378162 := by
    simpa [prefixWord, tailWord_7378162, baseEnd_7378162] using wordTrace_append hprefix tailTrace_7378162
  have hstable : (prefixWord ++ tailWord_7378162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378162).length < 2 ^ (prefixWord ++ tailWord_7378162).sum := by decide
  have hdescent : baseEnd_7378162 < baseStart_7378162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378181 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_7378181 : Nat := 118140960795 + 7378181 * 2 ^ 59
def prefixEnd_7378181 : Nat := 4983230072969 + 3 ^ 40 * 7378181 * 2
def baseEnd_7378181 : Nat := 3788553208870702566605869

theorem tailTrace_7378181 : CollatzResearch.WordTrace tailWord_7378181 prefixEnd_7378181 3788553208870702566605869 := by
  unfold tailWord_7378181
  simp only [CollatzResearch.WordTrace]
  refine ⟨269104368883117804838782397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179402912588745203225854931 269104368883117804838782397)
  ·
    refine ⟨100914138331169176814543399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269104368883117804838782397 100914138331169176814543399)
    ·
      refine ⟨151371207496753765221815099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100914138331169176814543399 151371207496753765221815099)
      ·
        refine ⟨227056811245130647832722649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151371207496753765221815099 227056811245130647832722649)
        ·
          refine ⟨170292608433847985874541987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227056811245130647832722649 170292608433847985874541987)
          ·
            refine ⟨255438912650771978811812981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170292608433847985874541987 255438912650771978811812981)
            ·
              refine ⟨23947398061009873013607467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255438912650771978811812981 23947398061009873013607467)
              ·
                refine ⟨35921097091514809520411201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23947398061009873013607467 35921097091514809520411201)
                ·
                  refine ⟨26940822818636107140308401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35921097091514809520411201 26940822818636107140308401)
                  ·
                    refine ⟨20205617113977080355231301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26940822818636107140308401 20205617113977080355231301)
                    ·
                      refine ⟨3788553208870702566605869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20205617113977080355231301 3788553208870702566605869)
                      ·
                        rfl

theorem cell23_7378181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_7378181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378181 prefixEnd_7378181 := by exact prefixLift 7378181
  have htrace : WordTrace (prefixWord ++ tailWord_7378181) baseStart_7378181 baseEnd_7378181 := by
    simpa [prefixWord, tailWord_7378181, baseEnd_7378181] using wordTrace_append hprefix tailTrace_7378181
  have hstable : (prefixWord ++ tailWord_7378181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378181).length < 2 ^ (prefixWord ++ tailWord_7378181).sum := by decide
  have hdescent : baseEnd_7378181 < baseStart_7378181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378185 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 2, 2, 2]
def baseStart_7378185 : Nat := 118140960795 + 7378185 * 2 ^ 59
def prefixEnd_7378185 : Nat := 4983230072969 + 3 ^ 40 * 7378185 * 2
def baseEnd_7378185 : Nat := 3788555262793320550955851

theorem tailTrace_7378185 : CollatzResearch.WordTrace tailWord_7378185 prefixEnd_7378185 3788555262793320550955851 := by
  unfold tailWord_7378185
  simp only [CollatzResearch.WordTrace]
  refine ⟨269104514775103313521928009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179403009850068875681285339 269104514775103313521928009)
  ·
    refine ⟨201828386081327485141446007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269104514775103313521928009 201828386081327485141446007)
    ·
      refine ⟨302742579121991227712169011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201828386081327485141446007 302742579121991227712169011)
      ·
        refine ⟨454113868682986841568253517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302742579121991227712169011 454113868682986841568253517)
        ·
          refine ⟨170292700756120065588095069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454113868682986841568253517 170292700756120065588095069)
          ·
            refine ⟨63859762783545024595535651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170292700756120065588095069 63859762783545024595535651)
            ·
              refine ⟨95789644175317536893303477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63859762783545024595535651 95789644175317536893303477)
              ·
                refine ⟨8980279141436019083747201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95789644175317536893303477 8980279141436019083747201)
                ·
                  refine ⟨6735209356077014312810401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8980279141436019083747201 6735209356077014312810401)
                  ·
                    refine ⟨5051407017057760734607801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6735209356077014312810401 5051407017057760734607801)
                    ·
                      refine ⟨3788555262793320550955851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051407017057760734607801 3788555262793320550955851)
                      ·
                        rfl

theorem cell23_7378185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 2, 2].length) (baseStart_7378185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378185 prefixEnd_7378185 := by exact prefixLift 7378185
  have htrace : WordTrace (prefixWord ++ tailWord_7378185) baseStart_7378185 baseEnd_7378185 := by
    simpa [prefixWord, tailWord_7378185, baseEnd_7378185] using wordTrace_append hprefix tailTrace_7378185
  have hstable : (prefixWord ++ tailWord_7378185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378185).length < 2 ^ (prefixWord ++ tailWord_7378185).sum := by decide
  have hdescent : baseEnd_7378185 < baseStart_7378185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378258 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7378258 : Nat := 118140960795 + 7378258 * 2 ^ 59
def prefixEnd_7378258 : Nat := 4983230072969 + 3 ^ 40 * 7378258 * 2
def baseEnd_7378258 : Nat := 3788592746881098765343015

theorem tailTrace_7378258 : CollatzResearch.WordTrace tailWord_7378258 prefixEnd_7378258 3788592746881098765343015 := by
  unfold tailWord_7378258
  simp only [CollatzResearch.WordTrace]
  refine ⟨67276794325959711747333857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179404784869225897992890285 67276794325959711747333857)
  ·
    refine ⟨50457595744469783810500393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67276794325959711747333857 50457595744469783810500393)
    ·
      refine ⟨37843196808352337857875295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50457595744469783810500393 37843196808352337857875295)
      ·
        refine ⟨56764795212528506786812943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37843196808352337857875295 56764795212528506786812943)
        ·
          refine ⟨85147192818792760180219415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56764795212528506786812943 85147192818792760180219415)
          ·
            refine ⟨127720789228189140270329123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85147192818792760180219415 127720789228189140270329123)
            ·
              refine ⟨191581183842283710405493685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127720789228189140270329123 191581183842283710405493685)
              ·
                refine ⟨17960735985214097850515033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191581183842283710405493685 17960735985214097850515033)
                ·
                  refine ⟨13470551988910573387886275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17960735985214097850515033 13470551988910573387886275)
                  ·
                    refine ⟨20205827983365860081829413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13470551988910573387886275 20205827983365860081829413)
                    ·
                      refine ⟨3788592746881098765343015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20205827983365860081829413 3788592746881098765343015)
                      ·
                        rfl

theorem cell23_7378258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7378258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378258 prefixEnd_7378258 := by exact prefixLift 7378258
  have htrace : WordTrace (prefixWord ++ tailWord_7378258) baseStart_7378258 baseEnd_7378258 := by
    simpa [prefixWord, tailWord_7378258, baseEnd_7378258] using wordTrace_append hprefix tailTrace_7378258
  have hstable : (prefixWord ++ tailWord_7378258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378258).length < 2 ^ (prefixWord ++ tailWord_7378258).sum := by decide
  have hdescent : baseEnd_7378258 < baseStart_7378258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378285 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_7378285 : Nat := 118140960795 + 7378285 * 2 ^ 59
def prefixEnd_7378285 : Nat := 4983230072969 + 3 ^ 40 * 7378285 * 2
def baseEnd_7378285 : Nat := 1262868870286256719901797

theorem tailTrace_7378285 : CollatzResearch.WordTrace tailWord_7378285 prefixEnd_7378285 1262868870286256719901797 := by
  unfold tailWord_7378285
  simp only [CollatzResearch.WordTrace]
  refine ⟨269108162074741030600568309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179405441383160687067045539 269108162074741030600568309)
  ·
    refine ⟨25228890194506971618803279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269108162074741030600568309 25228890194506971618803279)
    ·
      refine ⟨37843335291760457428204919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25228890194506971618803279 37843335291760457428204919)
      ·
        refine ⟨56765002937640686142307379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37843335291760457428204919 56765002937640686142307379)
        ·
          refine ⟨85147504406461029213461069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56765002937640686142307379 85147504406461029213461069)
          ·
            refine ⟨31930314152422885955047901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85147504406461029213461069 31930314152422885955047901)
            ·
              refine ⟨11973867807158582233142963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31930314152422885955047901 11973867807158582233142963)
              ·
                refine ⟨17960801710737873349714445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973867807158582233142963 17960801710737873349714445)
                ·
                  refine ⟨6735300641526702506142917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17960801710737873349714445 6735300641526702506142917)
                  ·
                    refine ⟨1262868870286256719901797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735300641526702506142917 1262868870286256719901797)
                    ·
                      rfl

theorem cell23_7378285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_7378285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378285 prefixEnd_7378285 := by exact prefixLift 7378285
  have htrace : WordTrace (prefixWord ++ tailWord_7378285) baseStart_7378285 baseEnd_7378285 := by
    simpa [prefixWord, tailWord_7378285, baseEnd_7378285] using wordTrace_append hprefix tailTrace_7378285
  have hstable : (prefixWord ++ tailWord_7378285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378285).length < 2 ^ (prefixWord ++ tailWord_7378285).sum := by decide
  have hdescent : baseEnd_7378285 < baseStart_7378285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378331 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4]
def baseStart_7378331 : Nat := 118140960795 + 7378331 * 2 ^ 59
def prefixEnd_7378331 : Nat := 4983230072969 + 3 ^ 40 * 7378331 * 2
def baseEnd_7378331 : Nat := 3788630230968876979730179

theorem tailTrace_7378331 : CollatzResearch.WordTrace tailWord_7378331 prefixEnd_7378331 3788630230968876979730179 := by
  unfold tailWord_7378331
  simp only [CollatzResearch.WordTrace]
  refine ⟨269109839832574380456742847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179406559888382920304495231 269109839832574380456742847)
  ·
    refine ⟨403664759748861570685114271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269109839832574380456742847 403664759748861570685114271)
    ·
      refine ⟨605497139623292356027671407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403664759748861570685114271 605497139623292356027671407)
      ·
        refine ⟨908245709434938534041507111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605497139623292356027671407 908245709434938534041507111)
        ·
          refine ⟨1362368564152407801062260667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908245709434938534041507111 1362368564152407801062260667)
          ·
            refine ⟨2043552846228611701593391001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362368564152407801062260667 2043552846228611701593391001)
            ·
              refine ⟨1532664634671458776195043251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043552846228611701593391001 1532664634671458776195043251)
              ·
                refine ⟨2298996952007188164292564877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532664634671458776195043251 2298996952007188164292564877)
                ·
                  refine ⟨862123857002695561609711829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2298996952007188164292564877 862123857002695561609711829)
                  ·
                    refine ⟨20206027898500677225227621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 862123857002695561609711829 20206027898500677225227621)
                    ·
                      refine ⟨3788630230968876979730179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20206027898500677225227621 3788630230968876979730179)
                      ·
                        rfl

theorem cell23_7378331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_7378331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378331 prefixEnd_7378331 := by exact prefixLift 7378331
  have htrace : WordTrace (prefixWord ++ tailWord_7378331) baseStart_7378331 baseEnd_7378331 := by
    simpa [prefixWord, tailWord_7378331, baseEnd_7378331] using wordTrace_append hprefix tailTrace_7378331
  have hstable : (prefixWord ++ tailWord_7378331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378331).length < 2 ^ (prefixWord ++ tailWord_7378331).sum := by decide
  have hdescent : baseEnd_7378331 < baseStart_7378331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378332 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 6]
def baseStart_7378332 : Nat := 118140960795 + 7378332 * 2 ^ 59
def prefixEnd_7378332 : Nat := 4983230072969 + 3 ^ 40 * 7378332 * 2
def baseEnd_7378332 : Nat := 420958971605503497313075

theorem tailTrace_7378332 : CollatzResearch.WordTrace tailWord_7378332 prefixEnd_7378332 420958971605503497313075 := by
  unfold tailWord_7378332
  simp only [CollatzResearch.WordTrace]
  refine ⟨134554938152785378813764625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179406584203713838418352833 134554938152785378813764625)
  ·
    refine ⟨100916203614589034110323469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134554938152785378813764625 100916203614589034110323469)
    ·
      refine ⟨37843576355470887791371301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100916203614589034110323469 37843576355470887791371301)
      ·
        refine ⟨7095670566650791460882119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37843576355470887791371301 7095670566650791460882119)
        ·
          refine ⟨10643505849976187191323179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095670566650791460882119 10643505849976187191323179)
          ·
            refine ⟨15965258774964280786984769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10643505849976187191323179 15965258774964280786984769)
            ·
              refine ⟨11973944081223210590238577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15965258774964280786984769 11973944081223210590238577)
              ·
                refine ⟨8980458060917407942678933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11973944081223210590238577 8980458060917407942678933)
                ·
                  refine ⟨420958971605503497313075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8980458060917407942678933 420958971605503497313075)
                  ·
                    rfl

theorem cell23_7378332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_7378332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378332 prefixEnd_7378332 := by exact prefixLift 7378332
  have htrace : WordTrace (prefixWord ++ tailWord_7378332) baseStart_7378332 baseEnd_7378332 := by
    simpa [prefixWord, tailWord_7378332, baseEnd_7378332] using wordTrace_append hprefix tailTrace_7378332
  have hstable : (prefixWord ++ tailWord_7378332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378332).length < 2 ^ (prefixWord ++ tailWord_7378332).sum := by decide
  have hdescent : baseEnd_7378332 < baseStart_7378332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378348 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_7378348 : Nat := 118140960795 + 7378348 * 2 ^ 59
def prefixEnd_7378348 : Nat := 4983230072969 + 3 ^ 40 * 7378348 * 2
def baseEnd_7378348 : Nat := 3788638960140003413217601

theorem tailTrace_7378348 : CollatzResearch.WordTrace tailWord_7378348 prefixEnd_7378348 3788638960140003413217601 := by
  unfold tailWord_7378348
  simp only [CollatzResearch.WordTrace]
  refine ⟨134555229936756396180055849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179406973249008528240074465 134555229936756396180055849)
  ·
    refine ⟨100916422452567297135041887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134555229936756396180055849 100916422452567297135041887)
    ·
      refine ⟨151374633678850945702562831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100916422452567297135041887 151374633678850945702562831)
      ·
        refine ⟨227061950518276418553844247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151374633678850945702562831 227061950518276418553844247)
        ·
          refine ⟨340592925777414627830766371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227061950518276418553844247 340592925777414627830766371)
          ·
            refine ⟨510889388666121941746149557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340592925777414627830766371 510889388666121941746149557)
            ·
              refine ⟨47895880187448932038701521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 510889388666121941746149557 47895880187448932038701521)
              ·
                refine ⟨35921910140586699029026141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47895880187448932038701521 35921910140586699029026141)
                ·
                  refine ⟨13470716302720012135884803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35921910140586699029026141 13470716302720012135884803)
                  ·
                    refine ⟨20206074454080018203827205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13470716302720012135884803 20206074454080018203827205)
                    ·
                      refine ⟨3788638960140003413217601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20206074454080018203827205 3788638960140003413217601)
                      ·
                        rfl

theorem cell23_7378348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_7378348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378348 prefixEnd_7378348 := by exact prefixLift 7378348
  have htrace : WordTrace (prefixWord ++ tailWord_7378348) baseStart_7378348 baseEnd_7378348 := by
    simpa [prefixWord, tailWord_7378348, baseEnd_7378348] using wordTrace_append hprefix tailTrace_7378348
  have hstable : (prefixWord ++ tailWord_7378348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378348).length < 2 ^ (prefixWord ++ tailWord_7378348).sum := by decide
  have hdescent : baseEnd_7378348 < baseStart_7378348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378365 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_7378365 : Nat := 118140960795 + 7378365 * 2 ^ 59
def prefixEnd_7378365 : Nat := 4983230072969 + 3 ^ 40 * 7378365 * 2
def baseEnd_7378365 : Nat := 3788647689311129846705023

theorem tailTrace_7378365 : CollatzResearch.WordTrace tailWord_7378365 prefixEnd_7378365 3788647689311129846705023 := by
  unfold tailWord_7378365
  simp only [CollatzResearch.WordTrace]
  refine ⟨269111079914451204263480549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179407386609634136175653699 269111079914451204263480549)
  ·
    refine ⟨50458327483959600799402603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269111079914451204263480549 50458327483959600799402603)
    ·
      refine ⟨75687491225939401199103905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50458327483959600799402603 75687491225939401199103905)
      ·
        refine ⟨56765618419454550899327929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75687491225939401199103905 56765618419454550899327929)
        ·
          refine ⟨42574213814590913174495947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56765618419454550899327929 42574213814590913174495947)
          ·
            refine ⟨63861320721886369761743921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42574213814590913174495947 63861320721886369761743921)
            ·
              refine ⟨47895990541414777321307941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63861320721886369761743921 47895990541414777321307941)
              ·
                refine ⟨8980498226515270747745239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47895990541414777321307941 8980498226515270747745239)
                ·
                  refine ⟨13470747339772906121617859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8980498226515270747745239 13470747339772906121617859)
                  ·
                    refine ⟨20206121009659359182426789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13470747339772906121617859 20206121009659359182426789)
                    ·
                      refine ⟨3788647689311129846705023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20206121009659359182426789 3788647689311129846705023)
                      ·
                        rfl

theorem cell23_7378365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_7378365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378365 prefixEnd_7378365 := by exact prefixLift 7378365
  have htrace : WordTrace (prefixWord ++ tailWord_7378365) baseStart_7378365 baseEnd_7378365 := by
    simpa [prefixWord, tailWord_7378365, baseEnd_7378365] using wordTrace_append hprefix tailTrace_7378365
  have hstable : (prefixWord ++ tailWord_7378365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378365).length < 2 ^ (prefixWord ++ tailWord_7378365).sum := by decide
  have hdescent : baseEnd_7378365 < baseStart_7378365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378370 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7378370 : Nat := 118140960795 + 7378370 * 2 ^ 59
def prefixEnd_7378370 : Nat := 4983230072969 + 3 ^ 40 * 7378370 * 2
def baseEnd_7378370 : Nat := 1262883418904800775714167

theorem tailTrace_7378370 : CollatzResearch.WordTrace tailWord_7378370 prefixEnd_7378370 1262883418904800775714167 := by
  unfold tailWord_7378370
  simp only [CollatzResearch.WordTrace]
  refine ⟨67277815569858272529353141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179407508186288726744941709 67277815569858272529353141)
  ·
    refine ⟨6307295209674213049626857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67277815569858272529353141 6307295209674213049626857)
    ·
      refine ⟨4730471407255659787220143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6307295209674213049626857 4730471407255659787220143)
      ·
        refine ⟨7095707110883489680830215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730471407255659787220143 7095707110883489680830215)
        ·
          refine ⟨10643560666325234521245323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095707110883489680830215 10643560666325234521245323)
          ·
            refine ⟨15965340999487851781867985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10643560666325234521245323 15965340999487851781867985)
            ·
              refine ⟨11974005749615888836400989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15965340999487851781867985 11974005749615888836400989)
              ·
                refine ⟨4490252156105958313650371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11974005749615888836400989 4490252156105958313650371)
                ·
                  refine ⟨6735378234158937470475557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490252156105958313650371 6735378234158937470475557)
                  ·
                    refine ⟨1262883418904800775714167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735378234158937470475557 1262883418904800775714167)
                    ·
                      rfl

theorem cell23_7378370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7378370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378370 prefixEnd_7378370 := by exact prefixLift 7378370
  have htrace : WordTrace (prefixWord ++ tailWord_7378370) baseStart_7378370 baseEnd_7378370 := by
    simpa [prefixWord, tailWord_7378370, baseEnd_7378370] using wordTrace_append hprefix tailTrace_7378370
  have hstable : (prefixWord ++ tailWord_7378370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378370).length < 2 ^ (prefixWord ++ tailWord_7378370).sum := by decide
  have hdescent : baseEnd_7378370 < baseStart_7378370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378371 : List Nat := [1, 1, 1, 3, 1, 1, 4, 11]
def baseStart_7378371 : Nat := 118140960795 + 7378371 * 2 ^ 59
def prefixEnd_7378371 : Nat := 4983230072969 + 3 ^ 40 * 7378371 * 2
def baseEnd_7378371 : Nat := 140320398896113215675185

theorem tailTrace_7378371 : CollatzResearch.WordTrace tailWord_7378371 prefixEnd_7378371 140320398896113215675185 := by
  unfold tailWord_7378371
  simp only [CollatzResearch.WordTrace]
  refine ⟨269111298752429467288198967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179407532501619644858799311 269111298752429467288198967)
  ·
    refine ⟨403666948128644200932298451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269111298752429467288198967 403666948128644200932298451)
    ·
      refine ⟨605500422192966301398447677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403666948128644200932298451 605500422192966301398447677)
      ·
        refine ⟨227062658322362363024417879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605500422192966301398447677 227062658322362363024417879)
        ·
          refine ⟨340593987483543544536626819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227062658322362363024417879 340593987483543544536626819)
          ·
            refine ⟨510890981225315316804940229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340593987483543544536626819 510890981225315316804940229)
            ·
              refine ⟨95792058979746621900926293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510890981225315316804940229 95792058979746621900926293)
              ·
                refine ⟨140320398896113215675185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95792058979746621900926293 140320398896113215675185)
                ·
                  rfl

theorem cell23_7378371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 11].length) (baseStart_7378371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378371 prefixEnd_7378371 := by exact prefixLift 7378371
  have htrace : WordTrace (prefixWord ++ tailWord_7378371) baseStart_7378371 baseEnd_7378371 := by
    simpa [prefixWord, tailWord_7378371, baseEnd_7378371] using wordTrace_append hprefix tailTrace_7378371
  have hstable : (prefixWord ++ tailWord_7378371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378371).length < 2 ^ (prefixWord ++ tailWord_7378371).sum := by decide
  have hdescent : baseEnd_7378371 < baseStart_7378371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378382 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_7378382 : Nat := 118140960795 + 7378382 * 2 ^ 59
def prefixEnd_7378382 : Nat := 4983230072969 + 3 ^ 40 * 7378382 * 2
def baseEnd_7378382 : Nat := 3788656418482256280192445

theorem tailTrace_7378382 : CollatzResearch.WordTrace tailWord_7378382 prefixEnd_7378382 3788656418482256280192445 := by
  unfold tailWord_7378382
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638962494423702020856175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179407799970259744111232933 33638962494423702020856175)
  ·
    refine ⟨50458443741635553031284263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33638962494423702020856175 50458443741635553031284263)
    ·
      refine ⟨75687665612453329546926395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50458443741635553031284263 75687665612453329546926395)
      ·
        refine ⟨113531498418679994320389593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75687665612453329546926395 113531498418679994320389593)
        ·
          refine ⟨85148623814009995740292195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113531498418679994320389593 85148623814009995740292195)
          ·
            refine ⟨127722935721014993610438293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85148623814009995740292195 127722935721014993610438293)
            ·
              refine ⟨5987012611922577825489295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127722935721014993610438293 5987012611922577825489295)
              ·
                refine ⟨8980518917883866738233943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987012611922577825489295 8980518917883866738233943)
                ·
                  refine ⟨13470778376825800107350915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8980518917883866738233943 13470778376825800107350915)
                  ·
                    refine ⟨20206167565238700161026373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13470778376825800107350915 20206167565238700161026373)
                    ·
                      refine ⟨3788656418482256280192445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20206167565238700161026373 3788656418482256280192445)
                      ·
                        rfl

theorem cell23_7378382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_7378382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378382 prefixEnd_7378382 := by exact prefixLift 7378382
  have htrace : WordTrace (prefixWord ++ tailWord_7378382) baseStart_7378382 baseEnd_7378382 := by
    simpa [prefixWord, tailWord_7378382, baseEnd_7378382] using wordTrace_append hprefix tailTrace_7378382
  have hstable : (prefixWord ++ tailWord_7378382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378382).length < 2 ^ (prefixWord ++ tailWord_7378382).sum := by decide
  have hdescent : baseEnd_7378382 < baseStart_7378382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378399 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 1, 2, 2]
def baseStart_7378399 : Nat := 118140960795 + 7378399 * 2 ^ 59
def prefixEnd_7378399 : Nat := 4983230072969 + 3 ^ 40 * 7378399 * 2
def baseEnd_7378399 : Nat := 3788665147653382713679867

theorem tailTrace_7378399 : CollatzResearch.WordTrace tailWord_7378399 prefixEnd_7378399 3788665147653382713679867 := by
  unfold tailWord_7378399
  simp only [CollatzResearch.WordTrace]
  refine ⟨269112319996328028070218251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179408213330885352046812167 269112319996328028070218251)
  ·
    refine ⟨403668479994492042105327377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269112319996328028070218251 403668479994492042105327377)
    ·
      refine ⟨302751359995869031578995533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403668479994492042105327377 302751359995869031578995533)
      ·
        refine ⟨113531759998450886842123325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302751359995869031578995533 113531759998450886842123325)
        ·
          refine ⟨42574409999419082565796247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113531759998450886842123325 42574409999419082565796247)
          ·
            refine ⟨63861614999128623848694371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42574409999419082565796247 63861614999128623848694371)
            ·
              refine ⟨95792422498692935773041557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63861614999128623848694371 95792422498692935773041557)
              ·
                refine ⟨4490269804626231364361323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95792422498692935773041557 4490269804626231364361323)
                ·
                  refine ⟨6735404706939347046541985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490269804626231364361323 6735404706939347046541985)
                  ·
                    refine ⟨5051553530204510284906489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6735404706939347046541985 5051553530204510284906489)
                    ·
                      refine ⟨3788665147653382713679867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051553530204510284906489 3788665147653382713679867)
                      ·
                        rfl

theorem cell23_7378399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_7378399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378399 prefixEnd_7378399 := by exact prefixLift 7378399
  have htrace : WordTrace (prefixWord ++ tailWord_7378399) baseStart_7378399 baseEnd_7378399 := by
    simpa [prefixWord, tailWord_7378399, baseEnd_7378399] using wordTrace_append hprefix tailTrace_7378399
  have hstable : (prefixWord ++ tailWord_7378399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378399).length < 2 ^ (prefixWord ++ tailWord_7378399).sum := by decide
  have hdescent : baseEnd_7378399 < baseStart_7378399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378415 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_7378415 : Nat := 118140960795 + 7378415 * 2 ^ 59
def prefixEnd_7378415 : Nat := 4983230072969 + 3 ^ 40 * 7378415 * 2
def baseEnd_7378415 : Nat := 3788673363343854651079793

theorem tailTrace_7378415 : CollatzResearch.WordTrace tailWord_7378415 prefixEnd_7378415 3788673363343854651079793 := by
  unfold tailWord_7378415
  simp only [CollatzResearch.WordTrace]
  refine ⟨269112903564270062802800699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179408602376180041868533799 269112903564270062802800699)
  ·
    refine ⟨403669355346405094204201049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269112903564270062802800699 403669355346405094204201049)
    ·
      refine ⟨302752016509803820653150787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403669355346405094204201049 302752016509803820653150787)
      ·
        refine ⟨454128024764705730979726181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302752016509803820653150787 454128024764705730979726181)
        ·
          refine ⟨85149004643382324558698659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454128024764705730979726181 85149004643382324558698659)
          ·
            refine ⟨127723506965073486838047989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85149004643382324558698659 127723506965073486838047989)
            ·
              refine ⟨11974078777975639391066999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127723506965073486838047989 11974078777975639391066999)
              ·
                refine ⟨17961118166963459086600499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11974078777975639391066999 17961118166963459086600499)
                ·
                  refine ⟨26941677250445188629900749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17961118166963459086600499 26941677250445188629900749)
                  ·
                    refine ⟨10103128968916945736212781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26941677250445188629900749 10103128968916945736212781)
                    ·
                      refine ⟨3788673363343854651079793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10103128968916945736212781 3788673363343854651079793)
                      ·
                        rfl

theorem cell23_7378415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_7378415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378415 prefixEnd_7378415 := by exact prefixLift 7378415
  have htrace : WordTrace (prefixWord ++ tailWord_7378415) baseStart_7378415 baseEnd_7378415 := by
    simpa [prefixWord, tailWord_7378415, baseEnd_7378415] using wordTrace_append hprefix tailTrace_7378415
  have hstable : (prefixWord ++ tailWord_7378415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378415).length < 2 ^ (prefixWord ++ tailWord_7378415).sum := by decide
  have hdescent : baseEnd_7378415 < baseStart_7378415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378422 : List Nat := [5, 1, 1, 1, 2, 4, 2, 7]
def baseStart_7378422 : Nat := 118140960795 + 7378422 * 2 ^ 59
def prefixEnd_7378422 : Nat := 4983230072969 + 3 ^ 40 * 7378422 * 2
def baseEnd_7378422 : Nat := 140321368804016152729343

theorem tailTrace_7378422 : CollatzResearch.WordTrace tailWord_7378422 prefixEnd_7378422 140321368804016152729343 := by
  unfold tailWord_7378422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819572429702793937394095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179408772583496468665537013 16819572429702793937394095)
  ·
    refine ⟨25229358644554190906091143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16819572429702793937394095 25229358644554190906091143)
    ·
      refine ⟨37844037966831286359136715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25229358644554190906091143 37844037966831286359136715)
      ·
        refine ⟨56766056950246929538705073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37844037966831286359136715 56766056950246929538705073)
        ·
          refine ⟨42574542712685197154028805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56766056950246929538705073 42574542712685197154028805)
          ·
            refine ⟨7982726758628474466380401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42574542712685197154028805 7982726758628474466380401)
            ·
              refine ⟨5987045068971355849785301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982726758628474466380401 5987045068971355849785301)
              ·
                refine ⟨140321368804016152729343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5987045068971355849785301 140321368804016152729343)
                ·
                  rfl

theorem cell23_7378422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_7378422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378422 prefixEnd_7378422 := by exact prefixLift 7378422
  have htrace : WordTrace (prefixWord ++ tailWord_7378422) baseStart_7378422 baseEnd_7378422 := by
    simpa [prefixWord, tailWord_7378422, baseEnd_7378422] using wordTrace_append hprefix tailTrace_7378422
  have hstable : (prefixWord ++ tailWord_7378422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378422).length < 2 ^ (prefixWord ++ tailWord_7378422).sum := by decide
  have hdescent : baseEnd_7378422 < baseStart_7378422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378428 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7378428 : Nat := 118140960795 + 7378428 * 2 ^ 59
def prefixEnd_7378428 : Nat := 4983230072969 + 3 ^ 40 * 7378428 * 2
def baseEnd_7378428 : Nat := 3788680038592363100217233

theorem tailTrace_7378428 : CollatzResearch.WordTrace tailWord_7378428 prefixEnd_7378428 3788680038592363100217233 := by
  unfold tailWord_7378428
  simp only [CollatzResearch.WordTrace]
  refine ⟨134556688856611483011511969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179408918475481977348682625 134556688856611483011511969)
  ·
    refine ⟨100917516642458612258633977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134556688856611483011511969 100917516642458612258633977)
    ·
      refine ⟨75688137481843959193975483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100917516642458612258633977 75688137481843959193975483)
      ·
        refine ⟨113532206222765938790963225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75688137481843959193975483 113532206222765938790963225)
        ·
          refine ⟨85149154667074454093222419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113532206222765938790963225 85149154667074454093222419)
          ·
            refine ⟨127723732000611681139833629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85149154667074454093222419 127723732000611681139833629)
            ·
              refine ⟨47896399500229380427437611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127723732000611681139833629 47896399500229380427437611)
              ·
                refine ⟨71844599250344070641156417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47896399500229380427437611 71844599250344070641156417)
                ·
                  refine ⟨53883449437758052980867313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71844599250344070641156417 53883449437758052980867313)
                  ·
                    refine ⟨40412587078318539735650485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53883449437758052980867313 40412587078318539735650485)
                    ·
                      refine ⟨3788680038592363100217233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40412587078318539735650485 3788680038592363100217233)
                      ·
                        rfl

theorem cell23_7378428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7378428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378428 prefixEnd_7378428 := by exact prefixLift 7378428
  have htrace : WordTrace (prefixWord ++ tailWord_7378428) baseStart_7378428 baseEnd_7378428 := by
    simpa [prefixWord, tailWord_7378428, baseEnd_7378428] using wordTrace_append hprefix tailTrace_7378428
  have hstable : (prefixWord ++ tailWord_7378428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378428).length < 2 ^ (prefixWord ++ tailWord_7378428).sum := by decide
  have hdescent : baseEnd_7378428 < baseStart_7378428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378433 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_7378433 : Nat := 118140960795 + 7378433 * 2 ^ 59
def prefixEnd_7378433 : Nat := 4983230072969 + 3 ^ 40 * 7378433 * 2
def baseEnd_7378433 : Nat := 3788682605995635580654711

theorem tailTrace_7378433 : CollatzResearch.WordTrace tailWord_7378433 prefixEnd_7378433 3788682605995635580654711 := by
  unfold tailWord_7378433
  simp only [CollatzResearch.WordTrace]
  refine ⟨269113560078204851876955953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179409040052136567917970635 269113560078204851876955953)
  ·
    refine ⟨201835170058653638907716965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269113560078204851876955953 201835170058653638907716965)
    ·
      refine ⟨37844094385997557295196931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201835170058653638907716965 37844094385997557295196931)
      ·
        refine ⟨56766141578996335942795397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37844094385997557295196931 56766141578996335942795397)
        ·
          refine ⟨10643651546061812989274137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56766141578996335942795397 10643651546061812989274137)
          ·
            refine ⟨7982738659546359741955603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10643651546061812989274137 7982738659546359741955603)
            ·
              refine ⟨11974107989319539612933405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982738659546359741955603 11974107989319539612933405)
              ·
                refine ⟨4490290495994827354850027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11974107989319539612933405 4490290495994827354850027)
                ·
                  refine ⟨6735435743992241032275041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490290495994827354850027 6735435743992241032275041)
                  ·
                    refine ⟨5051576807994180774206281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6735435743992241032275041 5051576807994180774206281)
                    ·
                      refine ⟨3788682605995635580654711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5051576807994180774206281 3788682605995635580654711)
                      ·
                        rfl

theorem cell23_7378433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_7378433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378433 prefixEnd_7378433 := by exact prefixLift 7378433
  have htrace : WordTrace (prefixWord ++ tailWord_7378433) baseStart_7378433 baseEnd_7378433 := by
    simpa [prefixWord, tailWord_7378433, baseEnd_7378433] using wordTrace_append hprefix tailTrace_7378433
  have hstable : (prefixWord ++ tailWord_7378433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378433).length < 2 ^ (prefixWord ++ tailWord_7378433).sum := by decide
  have hdescent : baseEnd_7378433 < baseStart_7378433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378458 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_7378458 : Nat := 118140960795 + 7378458 * 2 ^ 59
def prefixEnd_7378458 : Nat := 4983230072969 + 3 ^ 40 * 7378458 * 2
def baseEnd_7378458 : Nat := 3788695443011997982842095

theorem tailTrace_7378458 : CollatzResearch.WordTrace tailWord_7378458 prefixEnd_7378458 3788695443011997982842095 := by
  unfold tailWord_7378458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67278617975778570286654007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179409647935409520764410685 67278617975778570286654007)
  ·
    refine ⟨100917926963667855429981011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67278617975778570286654007 100917926963667855429981011)
    ·
      refine ⟨151376890445501783144971517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100917926963667855429981011 151376890445501783144971517)
      ·
        refine ⟨56766333917063168679364319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151376890445501783144971517 56766333917063168679364319)
        ·
          refine ⟨85149500875594753019046479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56766333917063168679364319 85149500875594753019046479)
          ·
            refine ⟨127724251313392129528569719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85149500875594753019046479 127724251313392129528569719)
            ·
              refine ⟨191586376970088194292854579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127724251313392129528569719 191586376970088194292854579)
              ·
                refine ⟨287379565455132291439281869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191586376970088194292854579 287379565455132291439281869)
                ·
                  refine ⟨107767337045674609289730701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287379565455132291439281869 107767337045674609289730701)
                  ·
                    refine ⟨40412751392127978483649013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107767337045674609289730701 40412751392127978483649013)
                    ·
                      refine ⟨3788695443011997982842095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40412751392127978483649013 3788695443011997982842095)
                      ·
                        rfl

theorem cell23_7378458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_7378458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378458 prefixEnd_7378458 := by exact prefixLift 7378458
  have htrace : WordTrace (prefixWord ++ tailWord_7378458) baseStart_7378458 baseEnd_7378458 := by
    simpa [prefixWord, tailWord_7378458, baseEnd_7378458] using wordTrace_append hprefix tailTrace_7378458
  have hstable : (prefixWord ++ tailWord_7378458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378458).length < 2 ^ (prefixWord ++ tailWord_7378458).sum := by decide
  have hdescent : baseEnd_7378458 < baseStart_7378458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378542 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_7378542 : Nat := 118140960795 + 7378542 * 2 ^ 59
def prefixEnd_7378542 : Nat := 4983230072969 + 3 ^ 40 * 7378542 * 2
def baseEnd_7378542 : Nat := 1262912858462325218063903

theorem tailTrace_7378542 : CollatzResearch.WordTrace tailWord_7378542 prefixEnd_7378542 1262912858462325218063903 := by
  unfold tailWord_7378542
  simp only [CollatzResearch.WordTrace]
  refine ⟨33639691954351245436584235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179411690423206642328449253 33639691954351245436584235)
  ·
    refine ⟨50459537931526868154876353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33639691954351245436584235 50459537931526868154876353)
    ·
      refine ⟨37844653448645151116157265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50459537931526868154876353 37844653448645151116157265)
      ·
        refine ⟨28383490086483863337117949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37844653448645151116157265 28383490086483863337117949)
        ·
          refine ⟨10643808782431448751419231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28383490086483863337117949 10643808782431448751419231)
          ·
            refine ⟨15965713173647173127128847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10643808782431448751419231 15965713173647173127128847)
            ·
              refine ⟨23948569760470759690693271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15965713173647173127128847 23948569760470759690693271)
              ·
                refine ⟨35922854640706139536039907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23948569760470759690693271 35922854640706139536039907)
                ·
                  refine ⟨53884281961059209304059861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35922854640706139536039907 53884281961059209304059861)
                  ·
                    refine ⟨1262912858462325218063903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53884281961059209304059861 1262912858462325218063903)
                    ·
                      rfl

theorem cell23_7378542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_7378542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378542 prefixEnd_7378542 := by exact prefixLift 7378542
  have htrace : WordTrace (prefixWord ++ tailWord_7378542) baseStart_7378542 baseEnd_7378542 := by
    simpa [prefixWord, tailWord_7378542, baseEnd_7378542] using wordTrace_append hprefix tailTrace_7378542
  have hstable : (prefixWord ++ tailWord_7378542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378542).length < 2 ^ (prefixWord ++ tailWord_7378542).sum := by decide
  have hdescent : baseEnd_7378542 < baseStart_7378542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378555 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 5, 4]
def baseStart_7378555 : Nat := 118140960795 + 7378555 * 2 ^ 59
def prefixEnd_7378555 : Nat := 4983230072969 + 3 ^ 40 * 7378555 * 2
def baseEnd_7378555 : Nat := 1262915083545161367776383

theorem tailTrace_7378555 : CollatzResearch.WordTrace tailWord_7378555 prefixEnd_7378555 1262915083545161367776383 := by
  unfold tailWord_7378555
  simp only [CollatzResearch.WordTrace]
  refine ⟨269118009783762866712897119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179412006522508577808598079 269118009783762866712897119)
  ·
    refine ⟨403677014675644300069345679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269118009783762866712897119 403677014675644300069345679)
    ·
      refine ⟨605515522013466450104018519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403677014675644300069345679 605515522013466450104018519)
      ·
        refine ⟨908273283020199675156027779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605515522013466450104018519 908273283020199675156027779)
        ·
          refine ⟨1362409924530299512734041669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908273283020199675156027779 1362409924530299512734041669)
          ·
            refine ⟨255451860849431158637632813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1362409924530299512734041669 255451860849431158637632813)
            ·
              refine ⟨95794447818536684489112305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255451860849431158637632813 95794447818536684489112305)
              ·
                refine ⟨71845835863902513366834229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95794447818536684489112305 71845835863902513366834229)
                ·
                  refine ⟨6735547112240860628140709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71845835863902513366834229 6735547112240860628140709)
                  ·
                    refine ⟨1262915083545161367776383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735547112240860628140709 1262915083545161367776383)
                    ·
                      rfl

theorem cell23_7378555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 4].length) (baseStart_7378555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378555 prefixEnd_7378555 := by exact prefixLift 7378555
  have htrace : WordTrace (prefixWord ++ tailWord_7378555) baseStart_7378555 baseEnd_7378555 := by
    simpa [prefixWord, tailWord_7378555, baseEnd_7378555] using wordTrace_append hprefix tailTrace_7378555
  have hstable : (prefixWord ++ tailWord_7378555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378555).length < 2 ^ (prefixWord ++ tailWord_7378555).sum := by decide
  have hdescent : baseEnd_7378555 < baseStart_7378555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378572 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_7378572 : Nat := 118140960795 + 7378572 * 2 ^ 59
def prefixEnd_7378572 : Nat := 4983230072969 + 3 ^ 40 * 7378572 * 2
def baseEnd_7378572 : Nat := 1262917993268870178938857

theorem tailTrace_7378572 : CollatzResearch.WordTrace tailWord_7378572 prefixEnd_7378572 1262917993268870178938857 := by
  unfold tailWord_7378572
  simp only [CollatzResearch.WordTrace]
  refine ⟨134559314912350639308132985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179412419883134185744177313 134559314912350639308132985)
  ·
    refine ⟨100919486184262979481099739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134559314912350639308132985 100919486184262979481099739)
    ·
      refine ⟨151379229276394469221649609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100919486184262979481099739 151379229276394469221649609)
      ·
        refine ⟨113534421957295851916237207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151379229276394469221649609 113534421957295851916237207)
        ·
          refine ⟨170301632935943777874355811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113534421957295851916237207 170301632935943777874355811)
          ·
            refine ⟨255452449403915666811533717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170301632935943777874355811 255452449403915666811533717)
            ·
              refine ⟨11974333565808546881790643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255452449403915666811533717 11974333565808546881790643)
              ·
                refine ⟨17961500348712820322685965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11974333565808546881790643 17961500348712820322685965)
                ·
                  refine ⟨6735562630767307621007237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17961500348712820322685965 6735562630767307621007237)
                  ·
                    refine ⟨1262917993268870178938857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735562630767307621007237 1262917993268870178938857)
                    ·
                      rfl

theorem cell23_7378572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_7378572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378572 prefixEnd_7378572 := by exact prefixLift 7378572
  have htrace : WordTrace (prefixWord ++ tailWord_7378572) baseStart_7378572 baseEnd_7378572 := by
    simpa [prefixWord, tailWord_7378572, baseEnd_7378572] using wordTrace_append hprefix tailTrace_7378572
  have hstable : (prefixWord ++ tailWord_7378572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378572).length < 2 ^ (prefixWord ++ tailWord_7378572).sum := by decide
  have hdescent : baseEnd_7378572 < baseStart_7378572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378595 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 3]
def baseStart_7378595 : Nat := 118140960795 + 7378595 * 2 ^ 59
def prefixEnd_7378595 : Nat := 4983230072969 + 3 ^ 40 * 7378595 * 2
def baseEnd_7378595 : Nat := 3788765789861663946828965

theorem tailTrace_7378595 : CollatzResearch.WordTrace tailWord_7378595 prefixEnd_7378595 3788765789861663946828965 := by
  unfold tailWord_7378595
  simp only [CollatzResearch.WordTrace]
  refine ⟨269119468703617953544353239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179412979135745302362902159 269119468703617953544353239)
  ·
    refine ⟨403679203055426930316529859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269119468703617953544353239 403679203055426930316529859)
    ·
      refine ⟨605518804583140395474794789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403679203055426930316529859 605518804583140395474794789)
      ·
        refine ⟨113534775859338824151524023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605518804583140395474794789 113534775859338824151524023)
        ·
          refine ⟨170302163789008236227286035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113534775859338824151524023 170302163789008236227286035)
          ·
            refine ⟨255453245683512354340929053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170302163789008236227286035 255453245683512354340929053)
            ·
              refine ⟨95794967131317132877848395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255453245683512354340929053 95794967131317132877848395)
              ·
                refine ⟨143692450696975699316772593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95794967131317132877848395 143692450696975699316772593)
                ·
                  refine ⟨107769338022731774487579445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143692450696975699316772593 107769338022731774487579445)
                  ·
                    refine ⟨10103375439631103858210573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107769338022731774487579445 10103375439631103858210573)
                    ·
                      refine ⟨3788765789861663946828965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10103375439631103858210573 3788765789861663946828965)
                      ·
                        rfl

theorem cell23_7378595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_7378595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378595 prefixEnd_7378595 := by exact prefixLift 7378595
  have htrace : WordTrace (prefixWord ++ tailWord_7378595) baseStart_7378595 baseEnd_7378595 := by
    simpa [prefixWord, tailWord_7378595, baseEnd_7378595] using wordTrace_append hprefix tailTrace_7378595
  have hstable : (prefixWord ++ tailWord_7378595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378595).length < 2 ^ (prefixWord ++ tailWord_7378595).sum := by decide
  have hdescent : baseEnd_7378595 < baseStart_7378595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378636 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 6]
def baseStart_7378636 : Nat := 118140960795 + 7378636 * 2 ^ 59
def prefixEnd_7378636 : Nat := 4983230072969 + 3 ^ 40 * 7378636 * 2
def baseEnd_7378636 : Nat := 420976315840944254046253

theorem tailTrace_7378636 : CollatzResearch.WordTrace tailWord_7378636 prefixEnd_7378636 420976315840944254046253 := by
  unfold tailWord_7378636
  simp only [CollatzResearch.WordTrace]
  refine ⟨134560482048234708773297881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179413976064312945031063841 134560482048234708773297881)
  ·
    refine ⟨100920361536176031579973411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134560482048234708773297881 100920361536176031579973411)
    ·
      refine ⟨151380542304264047369960117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100920361536176031579973411 151380542304264047369960117)
      ·
        refine ⟨14191925841024754440933761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151380542304264047369960117 14191925841024754440933761)
        ·
          refine ⟨10643944380768565830700321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14191925841024754440933761 10643944380768565830700321)
          ·
            refine ⟨7982958285576424373025241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10643944380768565830700321 7982958285576424373025241)
            ·
              refine ⟨5987218714182318279768931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982958285576424373025241 5987218714182318279768931)
              ·
                refine ⟨8980828071273477419653397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987218714182318279768931 8980828071273477419653397)
                ·
                  refine ⟨420976315840944254046253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8980828071273477419653397 420976315840944254046253)
                  ·
                    rfl

theorem cell23_7378636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_7378636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378636 prefixEnd_7378636 := by exact prefixLift 7378636
  have htrace : WordTrace (prefixWord ++ tailWord_7378636) baseStart_7378636 baseEnd_7378636 := by
    simpa [prefixWord, tailWord_7378636, baseEnd_7378636] using wordTrace_append hprefix tailTrace_7378636
  have hstable : (prefixWord ++ tailWord_7378636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378636).length < 2 ^ (prefixWord ++ tailWord_7378636).sum := by decide
  have hdescent : baseEnd_7378636 < baseStart_7378636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378649 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 1, 5]
def baseStart_7378649 : Nat := 118140960795 + 7378649 * 2 ^ 59
def prefixEnd_7378649 : Nat := 4983230072969 + 3 ^ 40 * 7378649 * 2
def baseEnd_7378649 : Nat := 1262931172605668911851239

theorem tailTrace_7378649 : CollatzResearch.WordTrace tailWord_7378649 prefixEnd_7378649 1262931172605668911851239 := by
  unfold tailWord_7378649
  simp only [CollatzResearch.WordTrace]
  refine ⟨269121438245422320766819001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179414292163614880511212667 269121438245422320766819001)
  ·
    refine ⟨201841078684066740575114251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269121438245422320766819001 201841078684066740575114251)
    ·
      refine ⟨302761618026100110862671377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201841078684066740575114251 302761618026100110862671377)
      ·
        refine ⟨227071213519575083147003533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302761618026100110862671377 227071213519575083147003533)
        ·
          refine ⟨85151705069840656180126325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227071213519575083147003533 85151705069840656180126325)
          ·
            refine ⟨7982972350297561516886843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85151705069840656180126325 7982972350297561516886843)
            ·
              refine ⟨11974458525446342275330265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982972350297561516886843 11974458525446342275330265)
              ·
                refine ⟨8980843894084756706497699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11974458525446342275330265 8980843894084756706497699)
                ·
                  refine ⟨13471265841127135059746549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8980843894084756706497699 13471265841127135059746549)
                  ·
                    refine ⟨1262931172605668911851239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13471265841127135059746549 1262931172605668911851239)
                    ·
                      rfl

theorem cell23_7378649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_7378649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378649 prefixEnd_7378649 := by exact prefixLift 7378649
  have htrace : WordTrace (prefixWord ++ tailWord_7378649) baseStart_7378649 baseEnd_7378649 := by
    simpa [prefixWord, tailWord_7378649, baseEnd_7378649] using wordTrace_append hprefix tailTrace_7378649
  have hstable : (prefixWord ++ tailWord_7378649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378649).length < 2 ^ (prefixWord ++ tailWord_7378649).sum := by decide
  have hdescent : baseEnd_7378649 < baseStart_7378649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378685 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_7378685 : Nat := 118140960795 + 7378685 * 2 ^ 59
def prefixEnd_7378685 : Nat := 4983230072969 + 3 ^ 40 * 7378685 * 2
def baseEnd_7378685 : Nat := 3788812003120568594703551

theorem tailTrace_7378685 : CollatzResearch.WordTrace tailWord_7378685 prefixEnd_7378685 3788812003120568594703551 := by
  unfold tailWord_7378685
  simp only [CollatzResearch.WordTrace]
  refine ⟨269122751273291898915129509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179415167515527932610086339 269122751273291898915129509)
  ·
    refine ⟨50460515863742231046586783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269122751273291898915129509 50460515863742231046586783)
    ·
      refine ⟨75690773795613346569880175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50460515863742231046586783 75690773795613346569880175)
      ·
        refine ⟨113536160693420019854820263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75690773795613346569880175 113536160693420019854820263)
        ·
          refine ⟨170304241040130029782230395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113536160693420019854820263 170304241040130029782230395)
          ·
            refine ⟨255456361560195044673345593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170304241040130029782230395 255456361560195044673345593)
            ·
              refine ⟨191592271170146283505009195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255456361560195044673345593 191592271170146283505009195)
              ·
                refine ⟨287388406755219425257513793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191592271170146283505009195 287388406755219425257513793)
                ·
                  refine ⟨215541305066414568943135345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287388406755219425257513793 215541305066414568943135345)
                  ·
                    refine ⟨161655978799810926707351509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215541305066414568943135345 161655978799810926707351509)
                    ·
                      refine ⟨3788812003120568594703551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161655978799810926707351509 3788812003120568594703551)
                      ·
                        rfl

theorem cell23_7378685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_7378685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378685 prefixEnd_7378685 := by exact prefixLift 7378685
  have htrace : WordTrace (prefixWord ++ tailWord_7378685) baseStart_7378685 baseEnd_7378685 := by
    simpa [prefixWord, tailWord_7378685, baseEnd_7378685] using wordTrace_append hprefix tailTrace_7378685
  have hstable : (prefixWord ++ tailWord_7378685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378685).length < 2 ^ (prefixWord ++ tailWord_7378685).sum := by decide
  have hdescent : baseEnd_7378685 < baseStart_7378685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378692 : List Nat := [2, 3, 2, 2, 1, 2, 3, 8]
def baseStart_7378692 : Nat := 118140960795 + 7378692 * 2 ^ 59
def prefixEnd_7378692 : Nat := 4983230072969 + 3 ^ 40 * 7378692 * 2
def baseEnd_7378692 : Nat := 140326503610561113604297

theorem tailTrace_7378692 : CollatzResearch.WordTrace tailWord_7378692 prefixEnd_7378692 140326503610561113604297 := by
  unfold tailWord_7378692
  simp only [CollatzResearch.WordTrace]
  refine ⟨134561503292133269555317165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179415337722844359407089553 134561503292133269555317165)
  ·
    refine ⟨50460563734549976083243937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134561503292133269555317165 50460563734549976083243937)
    ·
      refine ⟨37845422800912482062432953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50460563734549976083243937 37845422800912482062432953)
      ·
        refine ⟨28384067100684361546824715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37845422800912482062432953 28384067100684361546824715)
        ·
          refine ⟨42576100651026542320237073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28384067100684361546824715 42576100651026542320237073)
          ·
            refine ⟨31932075488269906740177805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42576100651026542320237073 31932075488269906740177805)
            ·
              refine ⟨11974528308101215027566677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31932075488269906740177805 11974528308101215027566677)
              ·
                refine ⟨140326503610561113604297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11974528308101215027566677 140326503610561113604297)
                ·
                  rfl

theorem cell23_7378692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 8].length) (baseStart_7378692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378692 prefixEnd_7378692 := by exact prefixLift 7378692
  have htrace : WordTrace (prefixWord ++ tailWord_7378692) baseStart_7378692 baseEnd_7378692 := by
    simpa [prefixWord, tailWord_7378692, baseEnd_7378692] using wordTrace_append hprefix tailTrace_7378692
  have hstable : (prefixWord ++ tailWord_7378692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378692).length < 2 ^ (prefixWord ++ tailWord_7378692).sum := by decide
  have hdescent : baseEnd_7378692 < baseStart_7378692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378705 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_7378705 : Nat := 118140960795 + 7378705 * 2 ^ 59
def prefixEnd_7378705 : Nat := 4983230072969 + 3 ^ 40 * 7378705 * 2
def baseEnd_7378705 : Nat := 1262940757577886172151153

theorem tailTrace_7378705 : CollatzResearch.WordTrace tailWord_7378705 prefixEnd_7378705 1262940757577886172151153 := by
  unfold tailWord_7378705
  simp only [CollatzResearch.WordTrace]
  refine ⟨269123480733219442330857569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179415653822146294887238379 269123480733219442330857569)
  ·
    refine ⟨201842610549914581748143177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269123480733219442330857569 201842610549914581748143177)
    ·
      refine ⟨151381957912435936311107383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201842610549914581748143177 151381957912435936311107383)
      ·
        refine ⟨227072936868653904466661075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151381957912435936311107383 227072936868653904466661075)
        ·
          refine ⟨340609405302980856699991613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227072936868653904466661075 340609405302980856699991613)
          ·
            refine ⟨127728526988617821262496855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340609405302980856699991613 127728526988617821262496855)
            ·
              refine ⟨191592790482926731893745283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127728526988617821262496855 191592790482926731893745283)
              ·
                refine ⟨287389185724390097840617925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191592790482926731893745283 287389185724390097840617925)
                ·
                  refine ⟨53885472323323143345115861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287389185724390097840617925 53885472323323143345115861)
                  ·
                    refine ⟨1262940757577886172151153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53885472323323143345115861 1262940757577886172151153)
                    ·
                      rfl

theorem cell23_7378705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_7378705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378705 prefixEnd_7378705 := by exact prefixLift 7378705
  have htrace : WordTrace (prefixWord ++ tailWord_7378705) baseStart_7378705 baseEnd_7378705 := by
    simpa [prefixWord, tailWord_7378705, baseEnd_7378705] using wordTrace_append hprefix tailTrace_7378705
  have hstable : (prefixWord ++ tailWord_7378705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378705).length < 2 ^ (prefixWord ++ tailWord_7378705).sum := by decide
  have hdescent : baseEnd_7378705 < baseStart_7378705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378706 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7378706 : Nat := 118140960795 + 7378706 * 2 ^ 59
def prefixEnd_7378706 : Nat := 4983230072969 + 3 ^ 40 * 7378706 * 2
def baseEnd_7378706 : Nat := 3788822786214313012540955

theorem tailTrace_7378706 : CollatzResearch.WordTrace tailWord_7378706 prefixEnd_7378706 3788822786214313012540955 := by
  unfold tailWord_7378706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67280879301553954875410993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179415678137477213001095981 67280879301553954875410993)
  ·
    refine ⟨50460659476165466156558245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67280879301553954875410993 50460659476165466156558245)
    ·
      refine ⟨9461373651781024904354671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50460659476165466156558245 9461373651781024904354671)
      ·
        refine ⟨14192060477671537356532007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9461373651781024904354671 14192060477671537356532007)
        ·
          refine ⟨21288090716507306034798011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14192060477671537356532007 21288090716507306034798011)
          ·
            refine ⟨31932136074760959052197017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21288090716507306034798011 31932136074760959052197017)
            ·
              refine ⟨23949102056070719289147763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31932136074760959052197017 23949102056070719289147763)
              ·
                refine ⟨35923653084106078933721645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23949102056070719289147763 35923653084106078933721645)
                ·
                  refine ⟨13471369906539779600145617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35923653084106078933721645 13471369906539779600145617)
                  ·
                    refine ⟨10103527429904834700109213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13471369906539779600145617 10103527429904834700109213)
                    ·
                      refine ⟨3788822786214313012540955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10103527429904834700109213 3788822786214313012540955)
                      ·
                        rfl

theorem cell23_7378706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7378706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378706 prefixEnd_7378706 := by exact prefixLift 7378706
  have htrace : WordTrace (prefixWord ++ tailWord_7378706) baseStart_7378706 baseEnd_7378706 := by
    simpa [prefixWord, tailWord_7378706, baseEnd_7378706] using wordTrace_append hprefix tailTrace_7378706
  have hstable : (prefixWord ++ tailWord_7378706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378706).length < 2 ^ (prefixWord ++ tailWord_7378706).sum := by decide
  have hdescent : baseEnd_7378706 < baseStart_7378706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378715 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_7378715 : Nat := 118140960795 + 7378715 * 2 ^ 59
def prefixEnd_7378715 : Nat := 4983230072969 + 3 ^ 40 * 7378715 * 2
def baseEnd_7378715 : Nat := 3788827407540203477328413

theorem tailTrace_7378715 : CollatzResearch.WordTrace tailWord_7378715 prefixEnd_7378715 3788827407540203477328413 := by
  unfold tailWord_7378715
  simp only [CollatzResearch.WordTrace]
  refine ⟨269123845463183214038721599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179415896975455476025814399 269123845463183214038721599)
  ·
    refine ⟨403685768194774821058082399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269123845463183214038721599 403685768194774821058082399)
    ·
      refine ⟨605528652292162231587123599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403685768194774821058082399 605528652292162231587123599)
      ·
        refine ⟨908292978438243347380685399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605528652292162231587123599 908292978438243347380685399)
        ·
          refine ⟨1362439467657365021071028099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908292978438243347380685399 1362439467657365021071028099)
          ·
            refine ⟨2043659201486047531606542149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362439467657365021071028099 2043659201486047531606542149)
            ·
              refine ⟨383186100278633912176226653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2043659201486047531606542149 383186100278633912176226653)
              ·
                refine ⟨143694787604487717066084995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383186100278633912176226653 143694787604487717066084995)
                ·
                  refine ⟨215542181406731575599127493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143694787604487717066084995 215542181406731575599127493)
                  ·
                    refine ⟨40414159013762170424836405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215542181406731575599127493 40414159013762170424836405)
                    ·
                      refine ⟨3788827407540203477328413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40414159013762170424836405 3788827407540203477328413)
                      ·
                        rfl

theorem cell23_7378715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_7378715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378715 prefixEnd_7378715 := by exact prefixLift 7378715
  have htrace : WordTrace (prefixWord ++ tailWord_7378715) baseStart_7378715 baseEnd_7378715 := by
    simpa [prefixWord, tailWord_7378715, baseEnd_7378715] using wordTrace_append hprefix tailTrace_7378715
  have hstable : (prefixWord ++ tailWord_7378715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378715).length < 2 ^ (prefixWord ++ tailWord_7378715).sum := by decide
  have hdescent : baseEnd_7378715 < baseStart_7378715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378719 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 3]
def baseStart_7378719 : Nat := 118140960795 + 7378719 * 2 ^ 59
def prefixEnd_7378719 : Nat := 4983230072969 + 3 ^ 40 * 7378719 * 2
def baseEnd_7378719 : Nat := 3788829461462821461678395

theorem tailTrace_7378719 : CollatzResearch.WordTrace tailWord_7378719 prefixEnd_7378719 3788829461462821461678395 := by
  unfold tailWord_7378719
  simp only [CollatzResearch.WordTrace]
  refine ⟨269123991355168722721867211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179415994236779148481244807 269123991355168722721867211)
  ·
    refine ⟨403685987032753084082800817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269123991355168722721867211 403685987032753084082800817)
    ·
      refine ⟨302764490274564813062100613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403685987032753084082800817 302764490274564813062100613)
      ·
        refine ⟨56768341926480902449143865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302764490274564813062100613 56768341926480902449143865)
        ·
          refine ⟨42576256444860676836857899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56768341926480902449143865 42576256444860676836857899)
          ·
            refine ⟨63864384667291015255286849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42576256444860676836857899 63864384667291015255286849)
            ·
              refine ⟨47898288500468261441465137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63864384667291015255286849 47898288500468261441465137)
              ·
                refine ⟨35923716375351196081098853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47898288500468261441465137 35923716375351196081098853)
                ·
                  refine ⟨6735696820378349265206035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35923716375351196081098853 6735696820378349265206035)
                  ·
                    refine ⟨10103545230567523897809053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6735696820378349265206035 10103545230567523897809053)
                    ·
                      refine ⟨3788829461462821461678395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10103545230567523897809053 3788829461462821461678395)
                      ·
                        rfl

theorem cell23_7378719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_7378719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378719 prefixEnd_7378719 := by exact prefixLift 7378719
  have htrace : WordTrace (prefixWord ++ tailWord_7378719) baseStart_7378719 baseEnd_7378719 := by
    simpa [prefixWord, tailWord_7378719, baseEnd_7378719] using wordTrace_append hprefix tailTrace_7378719
  have hstable : (prefixWord ++ tailWord_7378719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378719).length < 2 ^ (prefixWord ++ tailWord_7378719).sum := by decide
  have hdescent : baseEnd_7378719 < baseStart_7378719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378735 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 8]
def baseStart_7378735 : Nat := 118140960795 + 7378735 * 2 ^ 59
def prefixEnd_7378735 : Nat := 4983230072969 + 3 ^ 40 * 7378735 * 2
def baseEnd_7378735 : Nat := 1262945892384431133026107

theorem tailTrace_7378735 : CollatzResearch.WordTrace tailWord_7378735 prefixEnd_7378735 1262945892384431133026107 := by
  unfold tailWord_7378735
  simp only [CollatzResearch.WordTrace]
  refine ⟨269124574923110757454449659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179416383282073838302966439 269124574923110757454449659)
  ·
    refine ⟨403686862384666136181674489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269124574923110757454449659 403686862384666136181674489)
    ·
      refine ⟨302765146788499602136255867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403686862384666136181674489 302765146788499602136255867)
      ·
        refine ⟨454147720182749403204383801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302765146788499602136255867 454147720182749403204383801)
        ·
          refine ⟨340610790137062052403287851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454147720182749403204383801 340610790137062052403287851)
          ·
            refine ⟨510916185205593078604931777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340610790137062052403287851 510916185205593078604931777)
            ·
              refine ⟨383187138904194808953698833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510916185205593078604931777 383187138904194808953698833)
              ·
                refine ⟨287390354178146106715274125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383187138904194808953698833 287390354178146106715274125)
                ·
                  refine ⟨107771382816804790018227797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287390354178146106715274125 107771382816804790018227797)
                  ·
                    refine ⟨1262945892384431133026107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107771382816804790018227797 1262945892384431133026107)
                    ·
                      rfl

theorem cell23_7378735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_7378735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378735 prefixEnd_7378735 := by exact prefixLift 7378735
  have htrace : WordTrace (prefixWord ++ tailWord_7378735) baseStart_7378735 baseEnd_7378735 := by
    simpa [prefixWord, tailWord_7378735, baseEnd_7378735] using wordTrace_append hprefix tailTrace_7378735
  have hstable : (prefixWord ++ tailWord_7378735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378735).length < 2 ^ (prefixWord ++ tailWord_7378735).sum := by decide
  have hdescent : baseEnd_7378735 < baseStart_7378735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378762 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_7378762 : Nat := 118140960795 + 7378762 * 2 ^ 59
def prefixEnd_7378762 : Nat := 4983230072969 + 3 ^ 40 * 7378762 * 2
def baseEnd_7378762 : Nat := 3788851541130964793440697

theorem tailTrace_7378762 : CollatzResearch.WordTrace tailWord_7378762 prefixEnd_7378762 3788851541130964793440697 := by
  unfold tailWord_7378762
  simp only [CollatzResearch.WordTrace]
  refine ⟨67281389923503235266420635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179417039796008627377121693 67281389923503235266420635)
  ·
    refine ⟨100922084885254852899630953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67281389923503235266420635 100922084885254852899630953)
    ·
      refine ⟨75691563663941139674723215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100922084885254852899630953 75691563663941139674723215)
      ·
        refine ⟨113537345495911709512084823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75691563663941139674723215 113537345495911709512084823)
        ·
          refine ⟨170306018243867564268127235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113537345495911709512084823 170306018243867564268127235)
          ·
            refine ⟨255459027365801346402190853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170306018243867564268127235 255459027365801346402190853)
            ·
              refine ⟨47898567631087752450410785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255459027365801346402190853 47898567631087752450410785)
              ·
                refine ⟨35923925723315814337808089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47898567631087752450410785 35923925723315814337808089)
                ·
                  refine ⟨26942944292486860753356067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35923925723315814337808089 26942944292486860753356067)
                  ·
                    refine ⟨40414416438730291130034101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26942944292486860753356067 40414416438730291130034101)
                    ·
                      refine ⟨3788851541130964793440697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40414416438730291130034101 3788851541130964793440697)
                      ·
                        rfl

theorem cell23_7378762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_7378762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378762 prefixEnd_7378762 := by exact prefixLift 7378762
  have htrace : WordTrace (prefixWord ++ tailWord_7378762) baseStart_7378762 baseEnd_7378762 := by
    simpa [prefixWord, tailWord_7378762, baseEnd_7378762] using wordTrace_append hprefix tailTrace_7378762
  have hstable : (prefixWord ++ tailWord_7378762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378762).length < 2 ^ (prefixWord ++ tailWord_7378762).sum := by decide
  have hdescent : baseEnd_7378762 < baseStart_7378762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378792 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7378792 : Nat := 118140960795 + 7378792 * 2 ^ 59
def prefixEnd_7378792 : Nat := 4983230072969 + 3 ^ 40 * 7378792 * 2
def baseEnd_7378792 : Nat := 3788866945550599676065559

theorem tailTrace_7378792 : CollatzResearch.WordTrace tailWord_7378792 prefixEnd_7378792 3788866945550599676065559 := by
  unfold tailWord_7378792
  simp only [CollatzResearch.WordTrace]
  refine ⟨134563326941952128094637315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179417769255936170792849753 134563326941952128094637315)
  ·
    refine ⟨201844990412928192141955973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134563326941952128094637315 201844990412928192141955973)
    ·
      refine ⟨37845935702424036026616745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201844990412928192141955973 37845935702424036026616745)
      ·
        refine ⟨28384451776818027019962559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37845935702424036026616745 28384451776818027019962559)
        ·
          refine ⟨42576677665227040529943839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28384451776818027019962559 42576677665227040529943839)
          ·
            refine ⟨63865016497840560794915759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42576677665227040529943839 63865016497840560794915759)
            ·
              refine ⟨95797524746760841192373639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63865016497840560794915759 95797524746760841192373639)
              ·
                refine ⟨143696287120141261788560459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95797524746760841192373639 143696287120141261788560459)
                ·
                  refine ⟨215544430680211892682840689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143696287120141261788560459 215544430680211892682840689)
                  ·
                    refine ⟨161658323010158919512130517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215544430680211892682840689 161658323010158919512130517)
                    ·
                      refine ⟨3788866945550599676065559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161658323010158919512130517 3788866945550599676065559)
                      ·
                        rfl

theorem cell23_7378792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7378792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378792 prefixEnd_7378792 := by exact prefixLift 7378792
  have htrace : WordTrace (prefixWord ++ tailWord_7378792) baseStart_7378792 baseEnd_7378792 := by
    simpa [prefixWord, tailWord_7378792, baseEnd_7378792] using wordTrace_append hprefix tailTrace_7378792
  have hstable : (prefixWord ++ tailWord_7378792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378792).length < 2 ^ (prefixWord ++ tailWord_7378792).sum := by decide
  have hdescent : baseEnd_7378792 < baseStart_7378792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378850 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_7378850 : Nat := 118140960795 + 7378850 * 2 ^ 59
def prefixEnd_7378850 : Nat := 4983230072969 + 3 ^ 40 * 7378850 * 2
def baseEnd_7378850 : Nat := 420988525269840049904477

theorem tailTrace_7378850 : CollatzResearch.WordTrace tailWord_7378850 prefixEnd_7378850 420988525269840049904477 := by
  unfold tailWord_7378850
  simp only [CollatzResearch.WordTrace]
  refine ⟨67282192329423533023721501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179419179545129421396590669 67282192329423533023721501)
  ·
    refine ⟨25230822123533824883895563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67282192329423533023721501 25230822123533824883895563)
    ·
      refine ⟨37846233185300737325843345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25230822123533824883895563 37846233185300737325843345)
      ·
        refine ⟨28384674888975552994382509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37846233185300737325843345 28384674888975552994382509)
        ·
          refine ⟨10644253083365832372893441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28384674888975552994382509 10644253083365832372893441)
          ·
            refine ⟨7983189812524374279670081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10644253083365832372893441 7983189812524374279670081)
            ·
              refine ⟨5987392359393280709752561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7983189812524374279670081 5987392359393280709752561)
              ·
                refine ⟨4490544269544960532314421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5987392359393280709752561 4490544269544960532314421)
                ·
                  refine ⟨420988525269840049904477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4490544269544960532314421 420988525269840049904477)
                  ·
                    rfl

theorem cell23_7378850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_7378850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378850 prefixEnd_7378850 := by exact prefixLift 7378850
  have htrace : WordTrace (prefixWord ++ tailWord_7378850) baseStart_7378850 baseEnd_7378850 := by
    simpa [prefixWord, tailWord_7378850, baseEnd_7378850] using wordTrace_append hprefix tailTrace_7378850
  have hstable : (prefixWord ++ tailWord_7378850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378850).length < 2 ^ (prefixWord ++ tailWord_7378850).sum := by decide
  have hdescent : baseEnd_7378850 < baseStart_7378850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378939 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 4]
def baseStart_7378939 : Nat := 118140960795 + 7378939 * 2 ^ 59
def prefixEnd_7378939 : Nat := 4983230072969 + 3 ^ 40 * 7378939 * 2
def baseEnd_7378939 : Nat := 3788942427206810600927383

theorem tailTrace_7378939 : CollatzResearch.WordTrace tailWord_7378939 prefixEnd_7378939 3788942427206810600927383 := by
  unfold tailWord_7378939
  simp only [CollatzResearch.WordTrace]
  refine ⟨269132015414371700294875871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179421343609581133529917247 269132015414371700294875871)
  ·
    refine ⟨403698023121557550442313807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269132015414371700294875871 403698023121557550442313807)
    ·
      refine ⟨605547034682336325663470711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403698023121557550442313807 605547034682336325663470711)
      ·
        refine ⟨908320552023504488495206067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605547034682336325663470711 908320552023504488495206067)
        ·
          refine ⟨1362480828035256732742809101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908320552023504488495206067 1362480828035256732742809101)
          ·
            refine ⟨510930310513221274778553413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1362480828035256732742809101 510930310513221274778553413)
            ·
              refine ⟨95799433221228989020978765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510930310513221274778553413 95799433221228989020978765)
              ·
                refine ⟨35924787457960870882867037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95799433221228989020978765 35924787457960870882867037)
                ·
                  refine ⟨13471795296735326581075139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35924787457960870882867037 13471795296735326581075139)
                  ·
                    refine ⟨20207692945102989871612709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13471795296735326581075139 20207692945102989871612709)
                    ·
                      refine ⟨3788942427206810600927383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20207692945102989871612709 3788942427206810600927383)
                      ·
                        rfl

theorem cell23_7378939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 4].length) (baseStart_7378939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378939 prefixEnd_7378939 := by exact prefixLift 7378939
  have htrace : WordTrace (prefixWord ++ tailWord_7378939) baseStart_7378939 baseEnd_7378939 := by
    simpa [prefixWord, tailWord_7378939, baseEnd_7378939] using wordTrace_append hprefix tailTrace_7378939
  have hstable : (prefixWord ++ tailWord_7378939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378939).length < 2 ^ (prefixWord ++ tailWord_7378939).sum := by decide
  have hdescent : baseEnd_7378939 < baseStart_7378939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378956 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_7378956 : Nat := 118140960795 + 7378956 * 2 ^ 59
def prefixEnd_7378956 : Nat := 4983230072969 + 3 ^ 40 * 7378956 * 2
def baseEnd_7378956 : Nat := 3788951156377937034414805

theorem tailTrace_7378956 : CollatzResearch.WordTrace tailWord_7378956 prefixEnd_7378956 3788951156377937034414805 := by
  unfold tailWord_7378956
  simp only [CollatzResearch.WordTrace]
  refine ⟨134566317727655056099122361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179421756970206741465496481 134566317727655056099122361)
  ·
    refine ⟨100924738295741292074341771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134566317727655056099122361 100924738295741292074341771)
    ·
      refine ⟨151387107443611938111512657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100924738295741292074341771 151387107443611938111512657)
      ·
        refine ⟨113540330582708953583634493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151387107443611938111512657 113540330582708953583634493)
        ·
          refine ⟨42577623968515857593862935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113540330582708953583634493 42577623968515857593862935)
          ·
            refine ⟨63866435952773786390794403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42577623968515857593862935 63866435952773786390794403)
            ·
              refine ⟨95799653929160679586191605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63866435952773786390794403 95799653929160679586191605)
              ·
                refine ⟨8981217555858813711205463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95799653929160679586191605 8981217555858813711205463)
                ·
                  refine ⟨13471826333788220566808195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8981217555858813711205463 13471826333788220566808195)
                  ·
                    refine ⟨20207739500682330850212293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13471826333788220566808195 20207739500682330850212293)
                    ·
                      refine ⟨3788951156377937034414805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20207739500682330850212293 3788951156377937034414805)
                      ·
                        rfl

theorem cell23_7378956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_7378956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378956 prefixEnd_7378956 := by exact prefixLift 7378956
  have htrace : WordTrace (prefixWord ++ tailWord_7378956) baseStart_7378956 baseEnd_7378956 := by
    simpa [prefixWord, tailWord_7378956, baseEnd_7378956] using wordTrace_append hprefix tailTrace_7378956
  have hstable : (prefixWord ++ tailWord_7378956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378956).length < 2 ^ (prefixWord ++ tailWord_7378956).sum := by decide
  have hdescent : baseEnd_7378956 < baseStart_7378956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378967 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7378967 : Nat := 118140960795 + 7378967 * 2 ^ 59
def prefixEnd_7378967 : Nat := 4983230072969 + 3 ^ 40 * 7378967 * 2
def baseEnd_7378967 : Nat := 3788956804665136491377255

theorem tailTrace_7378967 : CollatzResearch.WordTrace tailWord_7378967 prefixEnd_7378967 3788956804665136491377255 := by
  unfold tailWord_7378967
  simp only [CollatzResearch.WordTrace]
  refine ⟨269133036658270261076895155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179422024438846840717930103 269133036658270261076895155)
  ·
    refine ⟨403699554987405391615342733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269133036658270261076895155 403699554987405391615342733)
    ·
      refine ⟨151387333120277021855753525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403699554987405391615342733 151387333120277021855753525)
      ·
        refine ⟨14192562480025970798976893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151387333120277021855753525 14192562480025970798976893)
        ·
          refine ⟨5322210930009739049616335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14192562480025970798976893 5322210930009739049616335)
          ·
            refine ⟨7983316395014608574424503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322210930009739049616335 7983316395014608574424503)
            ·
              refine ⟨11974974592521912861636755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983316395014608574424503 11974974592521912861636755)
              ·
                refine ⟨17962461888782869292455133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11974974592521912861636755 17962461888782869292455133)
                ·
                  refine ⟨6735923208293575984670675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17962461888782869292455133 6735923208293575984670675)
                  ·
                    refine ⟨10103884812440363977006013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6735923208293575984670675 10103884812440363977006013)
                    ·
                      refine ⟨3788956804665136491377255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10103884812440363977006013 3788956804665136491377255)
                      ·
                        rfl

theorem cell23_7378967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7378967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378967 prefixEnd_7378967 := by exact prefixLift 7378967
  have htrace : WordTrace (prefixWord ++ tailWord_7378967) baseStart_7378967 baseEnd_7378967 := by
    simpa [prefixWord, tailWord_7378967, baseEnd_7378967] using wordTrace_append hprefix tailTrace_7378967
  have hstable : (prefixWord ++ tailWord_7378967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378967).length < 2 ^ (prefixWord ++ tailWord_7378967).sum := by decide
  have hdescent : baseEnd_7378967 < baseStart_7378967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378979 : List Nat := [1, 1, 1, 4, 3, 1, 4, 8]
def baseStart_7378979 : Nat := 118140960795 + 7378979 * 2 ^ 59
def prefixEnd_7378979 : Nat := 4983230072969 + 3 ^ 40 * 7378979 * 2
def baseEnd_7378979 : Nat := 140331961719740386830637

theorem tailTrace_7378979 : CollatzResearch.WordTrace tailWord_7378979 prefixEnd_7378979 140331961719740386830637 := by
  unfold tailWord_7378979
  simp only [CollatzResearch.WordTrace]
  refine ⟨269133474334226787126331991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179422316222817858084221327 269133474334226787126331991)
  ·
    refine ⟨403700211501340180689497987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269133474334226787126331991 403700211501340180689497987)
    ·
      refine ⟨605550317252010271034246981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403700211501340180689497987 605550317252010271034246981)
      ·
        refine ⟨113540684484751925818921309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605550317252010271034246981 113540684484751925818921309)
        ·
          refine ⟨42577756681781972182095491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113540684484751925818921309 42577756681781972182095491)
          ·
            refine ⟨63866635022672958273143237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42577756681781972182095491 63866635022672958273143237)
            ·
              refine ⟨11974994066751179676214357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63866635022672958273143237 11974994066751179676214357)
              ·
                refine ⟨140331961719740386830637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11974994066751179676214357 140331961719740386830637)
                ·
                  rfl

theorem cell23_7378979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 8].length) (baseStart_7378979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378979 prefixEnd_7378979 := by exact prefixLift 7378979
  have htrace : WordTrace (prefixWord ++ tailWord_7378979) baseStart_7378979 baseEnd_7378979 := by
    simpa [prefixWord, tailWord_7378979, baseEnd_7378979] using wordTrace_append hprefix tailTrace_7378979
  have hstable : (prefixWord ++ tailWord_7378979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378979).length < 2 ^ (prefixWord ++ tailWord_7378979).sum := by decide
  have hdescent : baseEnd_7378979 < baseStart_7378979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378986 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7378986 : Nat := 118140960795 + 7378986 * 2 ^ 59
def prefixEnd_7378986 : Nat := 4983230072969 + 3 ^ 40 * 7378986 * 2
def baseEnd_7378986 : Nat := 3788966560797571917039667

theorem tailTrace_7378986 : CollatzResearch.WordTrace tailWord_7378986 prefixEnd_7378986 3788966560797571917039667 := by
  unfold tailWord_7378986
  simp only [CollatzResearch.WordTrace]
  refine ⟨67283432411300356830459203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179422486430134284881224541 67283432411300356830459203)
  ·
    refine ⟨100925148616950535245688805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67283432411300356830459203 100925148616950535245688805)
    ·
      refine ⟨18923465365678225358566651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100925148616950535245688805 18923465365678225358566651)
      ·
        refine ⟨28385198048517338037849977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18923465365678225358566651 28385198048517338037849977)
        ·
          refine ⟨21288898536388003528387483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28385198048517338037849977 21288898536388003528387483)
          ·
            refine ⟨31933347804582005292581225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21288898536388003528387483 31933347804582005292581225)
            ·
              refine ⟨23950010853436503969435919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31933347804582005292581225 23950010853436503969435919)
              ·
                refine ⟨35925016280154755954153879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23950010853436503969435919 35925016280154755954153879)
                ·
                  refine ⟨53887524420232133931230819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35925016280154755954153879 53887524420232133931230819)
                  ·
                    refine ⟨80831286630348200896846229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53887524420232133931230819 80831286630348200896846229)
                    ·
                      refine ⟨3788966560797571917039667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80831286630348200896846229 3788966560797571917039667)
                      ·
                        rfl

theorem cell23_7378986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7378986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378986 prefixEnd_7378986 := by exact prefixLift 7378986
  have htrace : WordTrace (prefixWord ++ tailWord_7378986) baseStart_7378986 baseEnd_7378986 := by
    simpa [prefixWord, tailWord_7378986, baseEnd_7378986] using wordTrace_append hprefix tailTrace_7378986
  have hstable : (prefixWord ++ tailWord_7378986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378986).length < 2 ^ (prefixWord ++ tailWord_7378986).sum := by decide
  have hdescent : baseEnd_7378986 < baseStart_7378986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378990 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_7378990 : Nat := 118140960795 + 7378990 * 2 ^ 59
def prefixEnd_7378990 : Nat := 4983230072969 + 3 ^ 40 * 7378990 * 2
def baseEnd_7378990 : Nat := 3788968614720189901389649

theorem tailTrace_7378990 : CollatzResearch.WordTrace tailWord_7378990 prefixEnd_7378990 3788968614720189901389649 := by
  unfold tailWord_7378990
  simp only [CollatzResearch.WordTrace]
  refine ⟨33641734442148367000622803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179422583691457957336654949 33641734442148367000622803)
  ·
    refine ⟨50462601663222550500934205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33641734442148367000622803 50462601663222550500934205)
    ·
      refine ⟨18923475623708456437850327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50462601663222550500934205 18923475623708456437850327)
      ·
        refine ⟨28385213435562684656775491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18923475623708456437850327 28385213435562684656775491)
        ·
          refine ⟨42577820153344026985163237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28385213435562684656775491 42577820153344026985163237)
          ·
            refine ⟨7983341278752005059718107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42577820153344026985163237 7983341278752005059718107)
            ·
              refine ⟨11975011918128007589577161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983341278752005059718107 11975011918128007589577161)
              ·
                refine ⟨8981258938596005692182871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11975011918128007589577161 8981258938596005692182871)
                ·
                  refine ⟨13471888407894008538274307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8981258938596005692182871 13471888407894008538274307)
                  ·
                    refine ⟨20207832611841012807411461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13471888407894008538274307 20207832611841012807411461)
                    ·
                      refine ⟨3788968614720189901389649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20207832611841012807411461 3788968614720189901389649)
                      ·
                        rfl

theorem cell23_7378990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_7378990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378990 prefixEnd_7378990 := by exact prefixLift 7378990
  have htrace : WordTrace (prefixWord ++ tailWord_7378990) baseStart_7378990 baseEnd_7378990 := by
    simpa [prefixWord, tailWord_7378990, baseEnd_7378990] using wordTrace_append hprefix tailTrace_7378990
  have hstable : (prefixWord ++ tailWord_7378990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378990).length < 2 ^ (prefixWord ++ tailWord_7378990).sum := by decide
  have hdescent : baseEnd_7378990 < baseStart_7378990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7378993 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_7378993 : Nat := 118140960795 + 7378993 * 2 ^ 59
def prefixEnd_7378993 : Nat := 4983230072969 + 3 ^ 40 * 7378993 * 2
def baseEnd_7378993 : Nat := 3788970155162153389652135

theorem tailTrace_7378993 : CollatzResearch.WordTrace tailWord_7378993 prefixEnd_7378993 3788970155162153389652135 := by
  unfold tailWord_7378993
  simp only [CollatzResearch.WordTrace]
  refine ⟨269133984956176067517341633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179422656637450711678227755 269133984956176067517341633)
  ·
    refine ⟨201850488717132050638006225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269133984956176067517341633 201850488717132050638006225)
    ·
      refine ⟨151387866537849037978504669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201850488717132050638006225 151387866537849037978504669)
      ·
        refine ⟨56770449951693389241939251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151387866537849037978504669 56770449951693389241939251)
        ·
          refine ⟨85155674927540083862908877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56770449951693389241939251 85155674927540083862908877)
          ·
            refine ⟨31933378097827531448590829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85155674927540083862908877 31933378097827531448590829)
            ·
              refine ⟨11975016786685324293221561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31933378097827531448590829 11975016786685324293221561)
              ·
                refine ⟨8981262590013993219916171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11975016786685324293221561 8981262590013993219916171)
                ·
                  refine ⟨13471893885020989829874257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8981262590013993219916171 13471893885020989829874257)
                  ·
                    refine ⟨10103920413765742372405693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13471893885020989829874257 10103920413765742372405693)
                    ·
                      refine ⟨3788970155162153389652135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10103920413765742372405693 3788970155162153389652135)
                      ·
                        rfl

theorem cell23_7378993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_7378993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7378993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7378993 prefixEnd_7378993 := by exact prefixLift 7378993
  have htrace : WordTrace (prefixWord ++ tailWord_7378993) baseStart_7378993 baseEnd_7378993 := by
    simpa [prefixWord, tailWord_7378993, baseEnd_7378993] using wordTrace_append hprefix tailTrace_7378993
  have hstable : (prefixWord ++ tailWord_7378993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7378993).length < 2 ^ (prefixWord ++ tailWord_7378993).sum := by decide
  have hdescent : baseEnd_7378993 < baseStart_7378993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7378993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379030 : List Nat := [5, 2, 2, 1, 1, 3, 1, 8]
def baseStart_7379030 : Nat := 118140960795 + 7379030 * 2 ^ 59
def prefixEnd_7379030 : Nat := 4983230072969 + 3 ^ 40 * 7379030 * 2
def baseEnd_7379030 : Nat := 140332931627643323884795

theorem tailTrace_7379030 : CollatzResearch.WordTrace tailWord_7379030 prefixEnd_7379030 140332931627643323884795 := by
  unfold tailWord_7379030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820958403565126427277409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179423556304694681890959029 16820958403565126427277409)
  ·
    refine ⟨12615718802673844820458057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16820958403565126427277409 12615718802673844820458057)
    ·
      refine ⟨9461789102005383615343543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12615718802673844820458057 9461789102005383615343543)
      ·
        refine ⟨14192683653008075423015315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9461789102005383615343543 14192683653008075423015315)
        ·
          refine ⟨21289025479512113134522973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14192683653008075423015315 21289025479512113134522973)
          ·
            refine ⟨7983384554817042425446115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21289025479512113134522973 7983384554817042425446115)
            ·
              refine ⟨11975076832225563638169173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983384554817042425446115 11975076832225563638169173)
              ·
                refine ⟨140332931627643323884795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11975076832225563638169173 140332931627643323884795)
                ·
                  rfl

theorem cell23_7379030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_7379030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379030 prefixEnd_7379030 := by exact prefixLift 7379030
  have htrace : WordTrace (prefixWord ++ tailWord_7379030) baseStart_7379030 baseEnd_7379030 := by
    simpa [prefixWord, tailWord_7379030, baseEnd_7379030] using wordTrace_append hprefix tailTrace_7379030
  have hstable : (prefixWord ++ tailWord_7379030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379030).length < 2 ^ (prefixWord ++ tailWord_7379030).sum := by decide
  have hdescent : baseEnd_7379030 < baseStart_7379030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379063 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 1, 4, 2]
def baseStart_7379063 : Nat := 118140960795 + 7379063 * 2 ^ 59
def prefixEnd_7379063 : Nat := 4983230072969 + 3 ^ 40 * 7379063 * 2
def baseEnd_7379063 : Nat := 3789006098807968115776813

theorem tailTrace_7379063 : CollatzResearch.WordTrace tailWord_7379063 prefixEnd_7379063 3789006098807968115776813 := by
  unfold tailWord_7379063
  simp only [CollatzResearch.WordTrace]
  refine ⟨269136538065922469472389843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179424358710614979648259895 269136538065922469472389843)
  ·
    refine ⟨403704807098883704208584765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269136538065922469472389843 403704807098883704208584765)
    ·
      refine ⟨151389302662081389078219287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403704807098883704208584765 151389302662081389078219287)
      ·
        refine ⟨227083953993122083617328931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151389302662081389078219287 227083953993122083617328931)
        ·
          refine ⟨340625930989683125425993397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227083953993122083617328931 340625930989683125425993397)
          ·
            refine ⟨31933681030282793008686881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 340625930989683125425993397 31933681030282793008686881)
            ·
              refine ⟨23950260772712094756515161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31933681030282793008686881 23950260772712094756515161)
              ·
                refine ⟨17962695579534071067386371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23950260772712094756515161 17962695579534071067386371)
                ·
                  refine ⟨26944043369301106601079557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17962695579534071067386371 26944043369301106601079557)
                  ·
                    refine ⟨5052008131743957487702417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26944043369301106601079557 5052008131743957487702417)
                    ·
                      refine ⟨3789006098807968115776813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052008131743957487702417 3789006098807968115776813)
                      ·
                        rfl

theorem cell23_7379063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_7379063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379063 prefixEnd_7379063 := by exact prefixLift 7379063
  have htrace : WordTrace (prefixWord ++ tailWord_7379063) baseStart_7379063 baseEnd_7379063 := by
    simpa [prefixWord, tailWord_7379063, baseEnd_7379063] using wordTrace_append hprefix tailTrace_7379063
  have hstable : (prefixWord ++ tailWord_7379063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379063).length < 2 ^ (prefixWord ++ tailWord_7379063).sum := by decide
  have hdescent : baseEnd_7379063 < baseStart_7379063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379076 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7379076 : Nat := 118140960795 + 7379076 * 2 ^ 59
def prefixEnd_7379076 : Nat := 4983230072969 + 3 ^ 40 * 7379076 * 2
def baseEnd_7379076 : Nat := 3789012774056476564914253

theorem tailTrace_7379076 : CollatzResearch.WordTrace tailWord_7379076 prefixEnd_7379076 3789012774056476564914253 := by
  unfold tailWord_7379076
  simp only [CollatzResearch.WordTrace]
  refine ⟨134568506107437686346306541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179424674809916915128408721 134568506107437686346306541)
  ·
    refine ⟨50463189790289132379864953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134568506107437686346306541 50463189790289132379864953)
    ·
      refine ⟨37847392342716849284898715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50463189790289132379864953 37847392342716849284898715)
      ·
        refine ⟨56771088514075273927348073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37847392342716849284898715 56771088514075273927348073)
        ·
          refine ⟨42578316385556455445511055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56771088514075273927348073 42578316385556455445511055)
          ·
            refine ⟨63867474578334683168266583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42578316385556455445511055 63867474578334683168266583)
            ·
              refine ⟨95801211867502024752399875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63867474578334683168266583 95801211867502024752399875)
              ·
                refine ⟨143701817801253037128599813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95801211867502024752399875 143701817801253037128599813)
                ·
                  refine ⟨26944090837734944461612465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143701817801253037128599813 26944090837734944461612465)
                  ·
                    refine ⟨20208068128301208346209349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26944090837734944461612465 20208068128301208346209349)
                    ·
                      refine ⟨3789012774056476564914253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20208068128301208346209349 3789012774056476564914253)
                      ·
                        rfl

theorem cell23_7379076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7379076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379076 prefixEnd_7379076 := by exact prefixLift 7379076
  have htrace : WordTrace (prefixWord ++ tailWord_7379076) baseStart_7379076 baseEnd_7379076 := by
    simpa [prefixWord, tailWord_7379076, baseEnd_7379076] using wordTrace_append hprefix tailTrace_7379076
  have hstable : (prefixWord ++ tailWord_7379076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379076).length < 2 ^ (prefixWord ++ tailWord_7379076).sum := by decide
  have hdescent : baseEnd_7379076 < baseStart_7379076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379099 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 3, 7]
def baseStart_7379099 : Nat := 118140960795 + 7379099 * 2 ^ 59
def prefixEnd_7379099 : Nat := 4983230072969 + 3 ^ 40 * 7379099 * 2
def baseEnd_7379099 : Nat := 1263008194703843324975549

theorem tailTrace_7379099 : CollatzResearch.WordTrace tailWord_7379099 prefixEnd_7379099 1263008194703843324975549 := by
  unfold tailWord_7379099
  simp only [CollatzResearch.WordTrace]
  refine ⟨269137851093792047620700351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179425234062528031747133567 269137851093792047620700351)
  ·
    refine ⟨403706776640688071431050527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269137851093792047620700351 403706776640688071431050527)
    ·
      refine ⟨605560164961032107146575791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403706776640688071431050527 605560164961032107146575791)
      ·
        refine ⟨908340247441548160719863687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605560164961032107146575791 908340247441548160719863687)
        ·
          refine ⟨1362510371162322241079795531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908340247441548160719863687 1362510371162322241079795531)
          ·
            refine ⟨2043765556743483361619693297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362510371162322241079795531 2043765556743483361619693297)
            ·
              refine ⟨1532824167557612521214769973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043765556743483361619693297 1532824167557612521214769973)
              ·
                refine ⟨143702265708526173863884685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1532824167557612521214769973 143702265708526173863884685)
                ·
                  refine ⟨53888349640697315198956757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143702265708526173863884685 53888349640697315198956757)
                  ·
                    refine ⟨1263008194703843324975549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53888349640697315198956757 1263008194703843324975549)
                    ·
                      rfl

theorem cell23_7379099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_7379099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379099 prefixEnd_7379099 := by exact prefixLift 7379099
  have htrace : WordTrace (prefixWord ++ tailWord_7379099) baseStart_7379099 baseEnd_7379099 := by
    simpa [prefixWord, tailWord_7379099, baseEnd_7379099] using wordTrace_append hprefix tailTrace_7379099
  have hstable : (prefixWord ++ tailWord_7379099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379099).length < 2 ^ (prefixWord ++ tailWord_7379099).sum := by decide
  have hdescent : baseEnd_7379099 < baseStart_7379099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379137 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 7]
def baseStart_7379137 : Nat := 118140960795 + 7379137 * 2 ^ 59
def prefixEnd_7379137 : Nat := 4983230072969 + 3 ^ 40 * 7379137 * 2
def baseEnd_7379137 : Nat := 421004899597377869583497

theorem tailTrace_7379137 : CollatzResearch.WordTrace tailWord_7379137 prefixEnd_7379137 421004899597377869583497 := by
  unfold tailWord_7379137
  simp only [CollatzResearch.WordTrace]
  refine ⟨269139237067654380110583665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179426158045102920073722443 269139237067654380110583665)
  ·
    refine ⟨201854427800740785082937749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269139237067654380110583665 201854427800740785082937749)
    ·
      refine ⟨9461926303159724300762707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201854427800740785082937749 9461926303159724300762707)
      ·
        refine ⟨14192889454739586451144061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9461926303159724300762707 14192889454739586451144061)
        ·
          refine ⟨5322333545527344919179023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14192889454739586451144061 5322333545527344919179023)
          ·
            refine ⟨7983500318291017378768535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322333545527344919179023 7983500318291017378768535)
            ·
              refine ⟨11975250477436526068152803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983500318291017378768535 11975250477436526068152803)
              ·
                refine ⟨17962875716154789102229205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11975250477436526068152803 17962875716154789102229205)
                ·
                  refine ⟨421004899597377869583497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17962875716154789102229205 421004899597377869583497)
                  ·
                    rfl

theorem cell23_7379137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 7].length) (baseStart_7379137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379137 prefixEnd_7379137 := by exact prefixLift 7379137
  have htrace : WordTrace (prefixWord ++ tailWord_7379137) baseStart_7379137 baseEnd_7379137 := by
    simpa [prefixWord, tailWord_7379137, baseEnd_7379137] using wordTrace_append hprefix tailTrace_7379137
  have hstable : (prefixWord ++ tailWord_7379137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379137).length < 2 ^ (prefixWord ++ tailWord_7379137).sum := by decide
  have hdescent : baseEnd_7379137 < baseStart_7379137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379148 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7379148 : Nat := 118140960795 + 7379148 * 2 ^ 59
def prefixEnd_7379148 : Nat := 4983230072969 + 3 ^ 40 * 7379148 * 2
def baseEnd_7379148 : Nat := 3789049744663600283213923

theorem tailTrace_7379148 : CollatzResearch.WordTrace tailWord_7379148 prefixEnd_7379148 3789049744663600283213923 := by
  unfold tailWord_7379148
  simp only [CollatzResearch.WordTrace]
  refine ⟨134569819135307264494617049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179426425513743019326156065 134569819135307264494617049)
  ·
    refine ⟨100927364351480448370962787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134569819135307264494617049 100927364351480448370962787)
    ·
      refine ⟨151391046527220672556444181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100927364351480448370962787 151391046527220672556444181)
      ·
        refine ⟨7096455305963469026083321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151391046527220672556444181 7096455305963469026083321)
        ·
          refine ⟨5322341479472601769562491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7096455305963469026083321 5322341479472601769562491)
          ·
            refine ⟨7983512219208902654343737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322341479472601769562491 7983512219208902654343737)
            ·
              refine ⟨5987634164406676990757803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7983512219208902654343737 5987634164406676990757803)
              ·
                refine ⟨8981451246610015486136705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987634164406676990757803 8981451246610015486136705)
                ·
                  refine ⟨6736088434957511614602529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8981451246610015486136705 6736088434957511614602529)
                  ·
                    refine ⟨5052066326218133710951897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6736088434957511614602529 5052066326218133710951897)
                    ·
                      refine ⟨3789049744663600283213923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052066326218133710951897 3789049744663600283213923)
                      ·
                        rfl

theorem cell23_7379148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7379148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379148 prefixEnd_7379148 := by exact prefixLift 7379148
  have htrace : WordTrace (prefixWord ++ tailWord_7379148) baseStart_7379148 baseEnd_7379148 := by
    simpa [prefixWord, tailWord_7379148, baseEnd_7379148] using wordTrace_append hprefix tailTrace_7379148
  have hstable : (prefixWord ++ tailWord_7379148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379148).length < 2 ^ (prefixWord ++ tailWord_7379148).sum := by decide
  have hdescent : baseEnd_7379148 < baseStart_7379148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379153 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 2, 4, 2]
def baseStart_7379153 : Nat := 118140960795 + 7379153 * 2 ^ 59
def prefixEnd_7379153 : Nat := 4983230072969 + 3 ^ 40 * 7379153 * 2
def baseEnd_7379153 : Nat := 3789052312066872763651399

theorem tailTrace_7379153 : CollatzResearch.WordTrace tailWord_7379153 prefixEnd_7379153 3789052312066872763651399 := by
  unfold tailWord_7379153
  simp only [CollatzResearch.WordTrace]
  refine ⟨269139820635596414843166113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179426547090397609895444075 269139820635596414843166113)
  ·
    refine ⟨201854865476697311132374585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269139820635596414843166113 201854865476697311132374585)
    ·
      refine ⟨151391149107522983349280939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201854865476697311132374585 151391149107522983349280939)
      ·
        refine ⟨227086723661284475023921409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151391149107522983349280939 227086723661284475023921409)
        ·
          refine ⟨170315042745963356267941057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227086723661284475023921409 170315042745963356267941057)
          ·
            refine ⟨127736282059472517200955793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170315042745963356267941057 127736282059472517200955793)
            ·
              refine ⟨95802211544604387900716845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127736282059472517200955793 95802211544604387900716845)
              ·
                refine ⟨35925829329226645462768817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95802211544604387900716845 35925829329226645462768817)
                ·
                  refine ⟨26944371996919984097076613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35925829329226645462768817 26944371996919984097076613)
                  ·
                    refine ⟨5052069749422497018201865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26944371996919984097076613 5052069749422497018201865)
                    ·
                      refine ⟨3789052312066872763651399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052069749422497018201865 3789052312066872763651399)
                      ·
                        rfl

theorem cell23_7379153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_7379153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379153 prefixEnd_7379153 := by exact prefixLift 7379153
  have htrace : WordTrace (prefixWord ++ tailWord_7379153) baseStart_7379153 baseEnd_7379153 := by
    simpa [prefixWord, tailWord_7379153, baseEnd_7379153] using wordTrace_append hprefix tailTrace_7379153
  have hstable : (prefixWord ++ tailWord_7379153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379153).length < 2 ^ (prefixWord ++ tailWord_7379153).sum := by decide
  have hdescent : baseEnd_7379153 < baseStart_7379153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379180 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_7379180 : Nat := 118140960795 + 7379180 * 2 ^ 59
def prefixEnd_7379180 : Nat := 4983230072969 + 3 ^ 40 * 7379180 * 2
def baseEnd_7379180 : Nat := 1263022058681514719337925

theorem tailTrace_7379180 : CollatzResearch.WordTrace tailWord_7379180 prefixEnd_7379180 1263022058681514719337925 := by
  unfold tailWord_7379180
  simp only [CollatzResearch.WordTrace]
  refine ⟨134570402703249299227199497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179427203604332398969599329 134570402703249299227199497)
  ·
    refine ⟨100927802027436974420399623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134570402703249299227199497 100927802027436974420399623)
    ·
      refine ⟨151391703041155461630599435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100927802027436974420399623 151391703041155461630599435)
      ·
        refine ⟨227087554561733192445899153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151391703041155461630599435 227087554561733192445899153)
        ·
          refine ⟨170315665921299894334424365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227087554561733192445899153 170315665921299894334424365)
          ·
            refine ⟨63868374720487460375409137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170315665921299894334424365 63868374720487460375409137)
            ·
              refine ⟨47901281040365595281556853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63868374720487460375409137 47901281040365595281556853)
              ·
                refine ⟨4490745097534274557645955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47901281040365595281556853 4490745097534274557645955)
                ·
                  refine ⟨6736117646301411836468933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490745097534274557645955 6736117646301411836468933)
                  ·
                    refine ⟨1263022058681514719337925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736117646301411836468933 1263022058681514719337925)
                    ·
                      rfl

theorem cell23_7379180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_7379180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379180 prefixEnd_7379180 := by exact prefixLift 7379180
  have htrace : WordTrace (prefixWord ++ tailWord_7379180) baseStart_7379180 baseEnd_7379180 := by
    simpa [prefixWord, tailWord_7379180, baseEnd_7379180] using wordTrace_append hprefix tailTrace_7379180
  have hstable : (prefixWord ++ tailWord_7379180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379180).length < 2 ^ (prefixWord ++ tailWord_7379180).sum := by decide
  have hdescent : baseEnd_7379180 < baseStart_7379180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379190 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7379190 : Nat := 118140960795 + 7379190 * 2 ^ 59
def prefixEnd_7379190 : Nat := 4983230072969 + 3 ^ 40 * 7379190 * 2
def baseEnd_7379190 : Nat := 3789071310851089118888729

theorem tailTrace_7379190 : CollatzResearch.WordTrace tailWord_7379190 prefixEnd_7379190 3789071310851089118888729 := by
  unfold tailWord_7379190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16821323133528898135141439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179427446757641580108175349 16821323133528898135141439)
  ·
    refine ⟨25231984700293347202712159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16821323133528898135141439 25231984700293347202712159)
    ·
      refine ⟨37847977050440020804068239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25231984700293347202712159 37847977050440020804068239)
      ·
        refine ⟨56771965575660031206102359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37847977050440020804068239 56771965575660031206102359)
        ·
          refine ⟨85157948363490046809153539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56771965575660031206102359 85157948363490046809153539)
          ·
            refine ⟨127736922545235070213730309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85157948363490046809153539 127736922545235070213730309)
            ·
              refine ⟨23950672977231575665074433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127736922545235070213730309 23950672977231575665074433)
              ·
                refine ⟨17963004732923681748805825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23950672977231575665074433 17963004732923681748805825)
                ·
                  refine ⟨13472253549692761311604369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17963004732923681748805825 13472253549692761311604369)
                  ·
                    refine ⟨10104190162269570983703277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13472253549692761311604369 10104190162269570983703277)
                    ·
                      refine ⟨3789071310851089118888729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10104190162269570983703277 3789071310851089118888729)
                      ·
                        rfl

theorem cell23_7379190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7379190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379190 prefixEnd_7379190 := by exact prefixLift 7379190
  have htrace : WordTrace (prefixWord ++ tailWord_7379190) baseStart_7379190 baseEnd_7379190 := by
    simpa [prefixWord, tailWord_7379190, baseEnd_7379190] using wordTrace_append hprefix tailTrace_7379190
  have hstable : (prefixWord ++ tailWord_7379190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379190).length < 2 ^ (prefixWord ++ tailWord_7379190).sum := by decide
  have hdescent : baseEnd_7379190 < baseStart_7379190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379223 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 3, 5]
def baseStart_7379223 : Nat := 118140960795 + 7379223 * 2 ^ 59
def prefixEnd_7379223 : Nat := 4983230072969 + 3 ^ 40 * 7379223 * 2
def baseEnd_7379223 : Nat := 1263029418570895829925359

theorem tailTrace_7379223 : CollatzResearch.WordTrace tailWord_7379223 prefixEnd_7379223 1263029418570895829925359 := by
  unfold tailWord_7379223
  simp only [CollatzResearch.WordTrace]
  refine ⟨269142373745342816798214323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179428249163561877865476215 269142373745342816798214323)
  ·
    refine ⟨403713560618014225197321485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269142373745342816798214323 403713560618014225197321485)
    ·
      refine ⟨151392585231755334448995557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403713560618014225197321485 151392585231755334448995557)
      ·
        refine ⟨28386109730954125209186667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151392585231755334448995557 28386109730954125209186667)
        ·
          refine ⟨42579164596431187813780001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28386109730954125209186667 42579164596431187813780001)
          ·
            refine ⟨31934373447323390860335001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42579164596431187813780001 31934373447323390860335001)
            ·
              refine ⟨23950780085492543145251251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31934373447323390860335001 23950780085492543145251251)
              ·
                refine ⟨35926170128238814717876877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23950780085492543145251251 35926170128238814717876877)
                ·
                  refine ⟨13472313798089555519203829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35926170128238814717876877 13472313798089555519203829)
                  ·
                    refine ⟨1263029418570895829925359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13472313798089555519203829 1263029418570895829925359)
                    ·
                      rfl

theorem cell23_7379223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_7379223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379223 prefixEnd_7379223 := by exact prefixLift 7379223
  have htrace : WordTrace (prefixWord ++ tailWord_7379223) baseStart_7379223 baseEnd_7379223 := by
    simpa [prefixWord, tailWord_7379223, baseEnd_7379223] using wordTrace_append hprefix tailTrace_7379223
  have hstable : (prefixWord ++ tailWord_7379223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379223).length < 2 ^ (prefixWord ++ tailWord_7379223).sum := by decide
  have hdescent : baseEnd_7379223 < baseStart_7379223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379263 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_7379263 : Nat := 118140960795 + 7379263 * 2 ^ 59
def prefixEnd_7379263 : Nat := 4983230072969 + 3 ^ 40 * 7379263 * 2
def baseEnd_7379263 : Nat := 3789108794938867333275893

theorem tailTrace_7379263 : CollatzResearch.WordTrace tailWord_7379263 prefixEnd_7379263 3789108794938867333275893 := by
  unfold tailWord_7379263
  simp only [CollatzResearch.WordTrace]
  refine ⟨269143832665197903629670443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179429221776798602419780295 269143832665197903629670443)
  ·
    refine ⟨403715748997796855444505665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269143832665197903629670443 403715748997796855444505665)
    ·
      refine ⟨302786811748347641583379249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403715748997796855444505665 302786811748347641583379249)
      ·
        refine ⟨227090108811260731187534437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302786811748347641583379249 227090108811260731187534437)
        ·
          refine ⟨42579395402111387097662707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227090108811260731187534437 42579395402111387097662707)
          ·
            refine ⟨63869093103167080646494061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42579395402111387097662707 63869093103167080646494061)
            ·
              refine ⟨23950909913687655242435273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63869093103167080646494061 23950909913687655242435273)
              ·
                refine ⟨17963182435265741431826455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23950909913687655242435273 17963182435265741431826455)
                ·
                  refine ⟨26944773652898612147739683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17963182435265741431826455 26944773652898612147739683)
                  ·
                    refine ⟨40417160479347918221609525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26944773652898612147739683 40417160479347918221609525)
                    ·
                      refine ⟨3789108794938867333275893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40417160479347918221609525 3789108794938867333275893)
                      ·
                        rfl

theorem cell23_7379263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_7379263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379263 prefixEnd_7379263 := by exact prefixLift 7379263
  have htrace : WordTrace (prefixWord ++ tailWord_7379263) baseStart_7379263 baseEnd_7379263 := by
    simpa [prefixWord, tailWord_7379263, baseEnd_7379263] using wordTrace_append hprefix tailTrace_7379263
  have hstable : (prefixWord ++ tailWord_7379263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379263).length < 2 ^ (prefixWord ++ tailWord_7379263).sum := by decide
  have hdescent : baseEnd_7379263 < baseStart_7379263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379280 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3]
def baseStart_7379280 : Nat := 118140960795 + 7379280 * 2 ^ 59
def prefixEnd_7379280 : Nat := 4983230072969 + 3 ^ 40 * 7379280 * 2
def baseEnd_7379280 : Nat := 3789117524109993766763315

theorem tailTrace_7379280 : CollatzResearch.WordTrace tailWord_7379280 prefixEnd_7379280 3789117524109993766763315 := by
  unfold tailWord_7379280
  simp only [CollatzResearch.WordTrace]
  refine ⟨134572226353068157766519647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179429635137424210355359529 134572226353068157766519647)
  ·
    refine ⟨201858339529602236649779471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134572226353068157766519647 201858339529602236649779471)
    ·
      refine ⟨302787509294403354974669207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201858339529602236649779471 302787509294403354974669207)
      ·
        refine ⟨454181263941605032462003811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302787509294403354974669207 454181263941605032462003811)
        ·
          refine ⟨681271895912407548693005717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454181263941605032462003811 681271895912407548693005717)
          ·
            refine ⟨31934620120894103844984643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 681271895912407548693005717 31934620120894103844984643)
            ·
              refine ⟨47901930181341155767476965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31934620120894103844984643 47901930181341155767476965)
              ·
                refine ⟨8981611909001466706401931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47901930181341155767476965 8981611909001466706401931)
                ·
                  refine ⟨13472417863502200059602897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8981611909001466706401931 13472417863502200059602897)
                  ·
                    refine ⟨10104313397626650044702173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13472417863502200059602897 10104313397626650044702173)
                    ·
                      refine ⟨3789117524109993766763315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10104313397626650044702173 3789117524109993766763315)
                      ·
                        rfl

theorem cell23_7379280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_7379280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379280 prefixEnd_7379280 := by exact prefixLift 7379280
  have htrace : WordTrace (prefixWord ++ tailWord_7379280) baseStart_7379280 baseEnd_7379280 := by
    simpa [prefixWord, tailWord_7379280, baseEnd_7379280] using wordTrace_append hprefix tailTrace_7379280
  have hstable : (prefixWord ++ tailWord_7379280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379280).length < 2 ^ (prefixWord ++ tailWord_7379280).sum := by decide
  have hdescent : baseEnd_7379280 < baseStart_7379280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379337 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 3, 3, 2]
def baseStart_7379337 : Nat := 118140960795 + 7379337 * 2 ^ 59
def prefixEnd_7379337 : Nat := 4983230072969 + 3 ^ 40 * 7379337 * 2
def baseEnd_7379337 : Nat := 3789146792507300043750553

theorem tailTrace_7379337 : CollatzResearch.WordTrace tailWord_7379337 prefixEnd_7379337 3789146792507300043750553 := by
  unfold tailWord_7379337
  simp only [CollatzResearch.WordTrace]
  refine ⟨269146531666929814267864265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179431021111286542845242843 269146531666929814267864265)
  ·
    refine ⟨201859898750197360700898199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269146531666929814267864265 201859898750197360700898199)
    ·
      refine ⟨302789848125296041051347299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201859898750197360700898199 302789848125296041051347299)
      ·
        refine ⟨454184772187944061577020949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302789848125296041051347299 454184772187944061577020949)
        ·
          refine ⟨21289911196309877886422857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 454184772187944061577020949 21289911196309877886422857)
          ·
            refine ⟨15967433397232408414817143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21289911196309877886422857 15967433397232408414817143)
            ·
              refine ⟨23951150095848612622225715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15967433397232408414817143 23951150095848612622225715)
              ·
                refine ⟨35926725143772918933338573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23951150095848612622225715 35926725143772918933338573)
                ·
                  refine ⟨13472521928914844600001965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35926725143772918933338573 13472521928914844600001965)
                  ·
                    refine ⟨5052195723343066725000737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13472521928914844600001965 5052195723343066725000737)
                    ·
                      refine ⟨3789146792507300043750553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052195723343066725000737 3789146792507300043750553)
                      ·
                        rfl

theorem cell23_7379337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 3, 2].length) (baseStart_7379337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379337 prefixEnd_7379337 := by exact prefixLift 7379337
  have htrace : WordTrace (prefixWord ++ tailWord_7379337) baseStart_7379337 baseEnd_7379337 := by
    simpa [prefixWord, tailWord_7379337, baseEnd_7379337] using wordTrace_append hprefix tailTrace_7379337
  have hstable : (prefixWord ++ tailWord_7379337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379337).length < 2 ^ (prefixWord ++ tailWord_7379337).sum := by decide
  have hdescent : baseEnd_7379337 < baseStart_7379337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379353 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_7379353 : Nat := 118140960795 + 7379353 * 2 ^ 59
def prefixEnd_7379353 : Nat := 4983230072969 + 3 ^ 40 * 7379353 * 2
def baseEnd_7379353 : Nat := 3789155008197771981150479

theorem tailTrace_7379353 : CollatzResearch.WordTrace tailWord_7379353 prefixEnd_7379353 3789155008197771981150479 := by
  unfold tailWord_7379353
  simp only [CollatzResearch.WordTrace]
  refine ⟨269147115234871849000446713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179431410156581232666964475 269147115234871849000446713)
  ·
    refine ⟨201860336426153886750335035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269147115234871849000446713 201860336426153886750335035)
    ·
      refine ⟨302790504639230830125502553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201860336426153886750335035 302790504639230830125502553)
      ·
        refine ⟨227092878479423122594126915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302790504639230830125502553 227092878479423122594126915)
        ·
          refine ⟨340639317719134683891190373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227092878479423122594126915 340639317719134683891190373)
          ·
            refine ⟨63869872072337753229598195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340639317719134683891190373 63869872072337753229598195)
            ·
              refine ⟨95804808108506629844397293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63869872072337753229598195 95804808108506629844397293)
              ·
                refine ⟨35926803040689986191648985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95804808108506629844397293 35926803040689986191648985)
                ·
                  refine ⟨26945102280517489643736739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35926803040689986191648985 26945102280517489643736739)
                  ·
                    refine ⟨40417653420776234465605109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26945102280517489643736739 40417653420776234465605109)
                    ·
                      refine ⟨3789155008197771981150479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40417653420776234465605109 3789155008197771981150479)
                      ·
                        rfl

theorem cell23_7379353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_7379353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379353 prefixEnd_7379353 := by exact prefixLift 7379353
  have htrace : WordTrace (prefixWord ++ tailWord_7379353) baseStart_7379353 baseEnd_7379353 := by
    simpa [prefixWord, tailWord_7379353, baseEnd_7379353] using wordTrace_append hprefix tailTrace_7379353
  have hstable : (prefixWord ++ tailWord_7379353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379353).length < 2 ^ (prefixWord ++ tailWord_7379353).sum := by decide
  have hdescent : baseEnd_7379353 < baseStart_7379353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379361 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7379361 : Nat := 118140960795 + 7379361 * 2 ^ 59
def prefixEnd_7379361 : Nat := 4983230072969 + 3 ^ 40 * 7379361 * 2
def baseEnd_7379361 : Nat := 3789159116043007949850443

theorem tailTrace_7379361 : CollatzResearch.WordTrace tailWord_7379361 prefixEnd_7379361 3789159116043007949850443 := by
  unfold tailWord_7379361
  simp only [CollatzResearch.WordTrace]
  refine ⟨269147407018842866366737937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179431604679228577577825291 269147407018842866366737937)
  ·
    refine ⟨201860555264132149775053453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269147407018842866366737937 201860555264132149775053453)
    ·
      refine ⟨75697708224049556165645045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201860555264132149775053453 75697708224049556165645045)
      ·
        refine ⟨7096660146004645890529223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75697708224049556165645045 7096660146004645890529223)
        ·
          refine ⟨10644990219006968835793835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7096660146004645890529223 10644990219006968835793835)
          ·
            refine ⟨15967485328510453253690753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10644990219006968835793835 15967485328510453253690753)
            ·
              refine ⟨11975613996382839940268065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15967485328510453253690753 11975613996382839940268065)
              ·
                refine ⟨8981710497287129955201049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11975613996382839940268065 8981710497287129955201049)
                ·
                  refine ⟨6736282872965347466400787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8981710497287129955201049 6736282872965347466400787)
                  ·
                    refine ⟨10104424309448021199601181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6736282872965347466400787 10104424309448021199601181)
                    ·
                      refine ⟨3789159116043007949850443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10104424309448021199601181 3789159116043007949850443)
                      ·
                        rfl

theorem cell23_7379361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7379361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379361 prefixEnd_7379361 := by exact prefixLift 7379361
  have htrace : WordTrace (prefixWord ++ tailWord_7379361) baseStart_7379361 baseEnd_7379361 := by
    simpa [prefixWord, tailWord_7379361, baseEnd_7379361] using wordTrace_append hprefix tailTrace_7379361
  have hstable : (prefixWord ++ tailWord_7379361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379361).length < 2 ^ (prefixWord ++ tailWord_7379361).sum := by decide
  have hdescent : baseEnd_7379361 < baseStart_7379361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379450 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_7379450 : Nat := 118140960795 + 7379450 * 2 ^ 59
def prefixEnd_7379450 : Nat := 4983230072969 + 3 ^ 40 * 7379450 * 2
def baseEnd_7379450 : Nat := 1263068271940419367212511

theorem tailTrace_7379450 : CollatzResearch.WordTrace tailWord_7379450 prefixEnd_7379450 1263068271940419367212511 := by
  unfold tailWord_7379450
  simp only [CollatzResearch.WordTrace]
  refine ⟨67287663278880108641681951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179433768743680289711151869 67287663278880108641681951)
  ·
    refine ⟨100931494918320162962522927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67287663278880108641681951 100931494918320162962522927)
    ·
      refine ⟨151397242377480244443784391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100931494918320162962522927 151397242377480244443784391)
      ·
        refine ⟨227095863566220366665676587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151397242377480244443784391 227095863566220366665676587)
        ·
          refine ⟨340643795349330549998514881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227095863566220366665676587 340643795349330549998514881)
          ·
            refine ⟨255482846511997912498886161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340643795349330549998514881 255482846511997912498886161)
            ·
              refine ⟨191612134883998434374164621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255482846511997912498886161 191612134883998434374164621)
              ·
                refine ⟨71854550581499412890311733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191612134883998434374164621 71854550581499412890311733)
                ·
                  refine ⟨6736364117015569958466725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71854550581499412890311733 6736364117015569958466725)
                  ·
                    refine ⟨1263068271940419367212511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736364117015569958466725 1263068271940419367212511)
                    ·
                      rfl

theorem cell23_7379450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_7379450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379450 prefixEnd_7379450 := by exact prefixLift 7379450
  have htrace : WordTrace (prefixWord ++ tailWord_7379450) baseStart_7379450 baseEnd_7379450 := by
    simpa [prefixWord, tailWord_7379450, baseEnd_7379450] using wordTrace_append hprefix tailTrace_7379450
  have hstable : (prefixWord ++ tailWord_7379450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379450).length < 2 ^ (prefixWord ++ tailWord_7379450).sum := by decide
  have hdescent : baseEnd_7379450 < baseStart_7379450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379458 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_7379458 : Nat := 118140960795 + 7379458 * 2 ^ 59
def prefixEnd_7379458 : Nat := 4983230072969 + 3 ^ 40 * 7379458 * 2
def baseEnd_7379458 : Nat := 421023213740721563370833

theorem tailTrace_7379458 : CollatzResearch.WordTrace tailWord_7379458 prefixEnd_7379458 421023213740721563370833 := by
  unfold tailWord_7379458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67287736224872862983254757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179433963266327634622012685 67287736224872862983254757)
  ·
    refine ⟨12616450542163661809360267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67287736224872862983254757 12616450542163661809360267)
    ·
      refine ⟨18924675813245492714040401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12616450542163661809360267 18924675813245492714040401)
      ·
        refine ⟨14193506859934119535530301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18924675813245492714040401 14193506859934119535530301)
        ·
          refine ⟨5322565072475294825823863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14193506859934119535530301 5322565072475294825823863)
          ·
            refine ⟨7983847608712942238735795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322565072475294825823863 7983847608712942238735795)
            ·
              refine ⟨11975771413069413358103693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983847608712942238735795 11975771413069413358103693)
              ·
                refine ⟨4490914279901030009288885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11975771413069413358103693 4490914279901030009288885)
                ·
                  refine ⟨421023213740721563370833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4490914279901030009288885 421023213740721563370833)
                  ·
                    rfl

theorem cell23_7379458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_7379458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379458 prefixEnd_7379458 := by exact prefixLift 7379458
  have htrace : WordTrace (prefixWord ++ tailWord_7379458) baseStart_7379458 baseEnd_7379458 := by
    simpa [prefixWord, tailWord_7379458, baseEnd_7379458] using wordTrace_append hprefix tailTrace_7379458
  have hstable : (prefixWord ++ tailWord_7379458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379458).length < 2 ^ (prefixWord ++ tailWord_7379458).sum := by decide
  have hdescent : baseEnd_7379458 < baseStart_7379458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379477 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_7379477 : Nat := 118140960795 + 7379477 * 2 ^ 59
def prefixEnd_7379477 : Nat := 4983230072969 + 3 ^ 40 * 7379477 * 2
def baseEnd_7379477 : Nat := 3789218679798929495999909

theorem tailTrace_7379477 : CollatzResearch.WordTrace tailWord_7379477 prefixEnd_7379477 3789218679798929495999909 := by
  unfold tailWord_7379477
  simp only [CollatzResearch.WordTrace]
  refine ⟨269151637886422618177960685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179434425257615078785307123 269151637886422618177960685)
  ·
    refine ⟨100931864207408481816735257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269151637886422618177960685 100931864207408481816735257)
    ·
      refine ⟨75698898155556361362551443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100931864207408481816735257 75698898155556361362551443)
      ·
        refine ⟨113548347233334542043827165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75698898155556361362551443 113548347233334542043827165)
        ·
          refine ⟨42580630212500453266435187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113548347233334542043827165 42580630212500453266435187)
          ·
            refine ⟨63870945318750679899652781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42580630212500453266435187 63870945318750679899652781)
            ·
              refine ⟨23951604494531504962369793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63870945318750679899652781 23951604494531504962369793)
              ·
                refine ⟨17963703370898628721777345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23951604494531504962369793 17963703370898628721777345)
                ·
                  refine ⟨13472777528173971541333009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17963703370898628721777345 13472777528173971541333009)
                  ·
                    refine ⟨10104583146130478655999757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13472777528173971541333009 10104583146130478655999757)
                    ·
                      refine ⟨3789218679798929495999909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10104583146130478655999757 3789218679798929495999909)
                      ·
                        rfl

theorem cell23_7379477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_7379477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379477 prefixEnd_7379477 := by exact prefixLift 7379477
  have htrace : WordTrace (prefixWord ++ tailWord_7379477) baseStart_7379477 baseEnd_7379477 := by
    simpa [prefixWord, tailWord_7379477, baseEnd_7379477] using wordTrace_append hprefix tailTrace_7379477
  have hstable : (prefixWord ++ tailWord_7379477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379477).length < 2 ^ (prefixWord ++ tailWord_7379477).sum := by decide
  have hdescent : baseEnd_7379477 < baseStart_7379477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379480 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 8]
def baseStart_7379480 : Nat := 118140960795 + 7379480 * 2 ^ 59
def prefixEnd_7379480 : Nat := 4983230072969 + 3 ^ 40 * 7379480 * 2
def baseEnd_7379480 : Nat := 421024468915654776029155

theorem tailTrace_7379480 : CollatzResearch.WordTrace tailWord_7379480 prefixEnd_7379480 421024468915654776029155 := by
  unfold tailWord_7379480
  simp only [CollatzResearch.WordTrace]
  refine ⟨134575873652705874845159947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179434498203607833126879929 134575873652705874845159947)
  ·
    refine ⟨201863810479058812267739921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134575873652705874845159947 201863810479058812267739921)
    ·
      refine ⟨151397857859294109200804941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201863810479058812267739921 151397857859294109200804941)
      ·
        refine ⟨56774196697235290950301853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151397857859294109200804941 56774196697235290950301853)
        ·
          refine ⟨21290323761463234106363195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56774196697235290950301853 21290323761463234106363195)
          ·
            refine ⟨31935485642194851159544793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21290323761463234106363195 31935485642194851159544793)
            ·
              refine ⟨23951614231646138369658595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31935485642194851159544793 23951614231646138369658595)
              ·
                refine ⟨35927421347469207554487893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23951614231646138369658595 35927421347469207554487893)
                ·
                  refine ⟨421024468915654776029155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35927421347469207554487893 421024468915654776029155)
                  ·
                    rfl

theorem cell23_7379480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_7379480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379480 prefixEnd_7379480 := by exact prefixLift 7379480
  have htrace : WordTrace (prefixWord ++ tailWord_7379480) baseStart_7379480 baseEnd_7379480 := by
    simpa [prefixWord, tailWord_7379480, baseEnd_7379480] using wordTrace_append hprefix tailTrace_7379480
  have hstable : (prefixWord ++ tailWord_7379480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379480).length < 2 ^ (prefixWord ++ tailWord_7379480).sum := by decide
  have hdescent : baseEnd_7379480 < baseStart_7379480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379484 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_7379484 : Nat := 118140960795 + 7379484 * 2 ^ 59
def prefixEnd_7379484 : Nat := 4983230072969 + 3 ^ 40 * 7379484 * 2
def baseEnd_7379484 : Nat := 1263074091387836989537459

theorem tailTrace_7379484 : CollatzResearch.WordTrace tailWord_7379484 prefixEnd_7379484 1263074091387836989537459 := by
  unfold tailWord_7379484
  simp only [CollatzResearch.WordTrace]
  refine ⟨134575946598698629186732753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179434595464931505582310337 134575946598698629186732753)
  ·
    refine ⟨100931959949023971890049565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134575946598698629186732753 100931959949023971890049565)
    ·
      refine ⟨37849484980883989458768587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100931959949023971890049565 37849484980883989458768587)
      ·
        refine ⟨56774227471325984188152881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37849484980883989458768587 56774227471325984188152881)
        ·
          refine ⟨42580670603494488141114661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56774227471325984188152881 42580670603494488141114661)
          ·
            refine ⟨7983875738155216526458999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42580670603494488141114661 7983875738155216526458999)
            ·
              refine ⟨11975813607232824789688499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983875738155216526458999 11975813607232824789688499)
              ·
                refine ⟨17963720410849237184532749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11975813607232824789688499 17963720410849237184532749)
                ·
                  refine ⟨6736395154068463944199781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17963720410849237184532749 6736395154068463944199781)
                  ·
                    refine ⟨1263074091387836989537459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736395154068463944199781 1263074091387836989537459)
                    ·
                      rfl

theorem cell23_7379484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_7379484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379484 prefixEnd_7379484 := by exact prefixLift 7379484
  have htrace : WordTrace (prefixWord ++ tailWord_7379484) baseStart_7379484 baseEnd_7379484 := by
    simpa [prefixWord, tailWord_7379484, baseEnd_7379484] using wordTrace_append hprefix tailTrace_7379484
  have hstable : (prefixWord ++ tailWord_7379484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379484).length < 2 ^ (prefixWord ++ tailWord_7379484).sum := by decide
  have hdescent : baseEnd_7379484 < baseStart_7379484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379507 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 3]
def baseStart_7379507 : Nat := 118140960795 + 7379507 * 2 ^ 59
def prefixEnd_7379507 : Nat := 4983230072969 + 3 ^ 40 * 7379507 * 2
def baseEnd_7379507 : Nat := 3789234084218564378624771

theorem tailTrace_7379507 : CollatzResearch.WordTrace tailWord_7379507 prefixEnd_7379507 3789234084218564378624771 := by
  unfold tailWord_7379507
  simp only [CollatzResearch.WordTrace]
  refine ⟨269152732076313933301552775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179435154717542622201035183 269152732076313933301552775)
  ·
    refine ⟨403729098114470899952329163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269152732076313933301552775 403729098114470899952329163)
    ·
      refine ⟨605593647171706349928493745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403729098114470899952329163 605593647171706349928493745)
      ·
        refine ⟨454195235378779762446370309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605593647171706349928493745 454195235378779762446370309)
        ·
          refine ⟨85161606633521205458694433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454195235378779762446370309 85161606633521205458694433)
          ·
            refine ⟨63871204975140904094020825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85161606633521205458694433 63871204975140904094020825)
            ·
              refine ⟨47903403731355678070515619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63871204975140904094020825 47903403731355678070515619)
              ·
                refine ⟨71855105597033517105773429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47903403731355678070515619 71855105597033517105773429)
                ·
                  refine ⟨6736416149721892228666259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71855105597033517105773429 6736416149721892228666259)
                  ·
                    refine ⟨10104624224582838342999389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6736416149721892228666259 10104624224582838342999389)
                    ·
                      refine ⟨3789234084218564378624771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10104624224582838342999389 3789234084218564378624771)
                      ·
                        rfl

theorem cell23_7379507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_7379507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379507 prefixEnd_7379507 := by exact prefixLift 7379507
  have htrace : WordTrace (prefixWord ++ tailWord_7379507) baseStart_7379507 baseEnd_7379507 := by
    simpa [prefixWord, tailWord_7379507, baseEnd_7379507] using wordTrace_append hprefix tailTrace_7379507
  have hstable : (prefixWord ++ tailWord_7379507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379507).length < 2 ^ (prefixWord ++ tailWord_7379507).sum := by decide
  have hdescent : baseEnd_7379507 < baseStart_7379507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379534 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_7379534 : Nat := 118140960795 + 7379534 * 2 ^ 59
def prefixEnd_7379534 : Nat := 4983230072969 + 3 ^ 40 * 7379534 * 2
def baseEnd_7379534 : Nat := 3789247948196235772987147

theorem tailTrace_7379534 : CollatzResearch.WordTrace tailWord_7379534 prefixEnd_7379534 3789247948196235772987147 := by
  unfold tailWord_7379534
  simp only [CollatzResearch.WordTrace]
  refine ⟨33644214605902014614098207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179435811231477411275190437 33644214605902014614098207)
  ·
    refine ⟨50466321908853021921147311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33644214605902014614098207 50466321908853021921147311)
    ·
      refine ⟨75699482863279532881720967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50466321908853021921147311 75699482863279532881720967)
      ·
        refine ⟨113549224294919299322581451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75699482863279532881720967 113549224294919299322581451)
        ·
          refine ⟨170323836442378948983872177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113549224294919299322581451 170323836442378948983872177)
          ·
            refine ⟨127742877331784211737904133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170323836442378948983872177 127742877331784211737904133)
            ·
              refine ⟨23951789499709539700857025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127742877331784211737904133 23951789499709539700857025)
              ·
                refine ⟨17963842124782154775642769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23951789499709539700857025 17963842124782154775642769)
                ·
                  refine ⟨13472881593586616081732077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17963842124782154775642769 13472881593586616081732077)
                  ·
                    refine ⟨5052330597594981030649529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13472881593586616081732077 5052330597594981030649529)
                    ·
                      refine ⟨3789247948196235772987147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052330597594981030649529 3789247948196235772987147)
                      ·
                        rfl

theorem cell23_7379534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_7379534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379534 prefixEnd_7379534 := by exact prefixLift 7379534
  have htrace : WordTrace (prefixWord ++ tailWord_7379534) baseStart_7379534 baseEnd_7379534 := by
    simpa [prefixWord, tailWord_7379534, baseEnd_7379534] using wordTrace_append hprefix tailTrace_7379534
  have hstable : (prefixWord ++ tailWord_7379534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379534).length < 2 ^ (prefixWord ++ tailWord_7379534).sum := by decide
  have hdescent : baseEnd_7379534 < baseStart_7379534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379564 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 5, 2, 2]
def baseStart_7379564 : Nat := 118140960795 + 7379564 * 2 ^ 59
def prefixEnd_7379564 : Nat := 4983230072969 + 3 ^ 40 * 7379564 * 2
def baseEnd_7379564 : Nat := 3789263352615870655612009

theorem tailTrace_7379564 : CollatzResearch.WordTrace tailWord_7379564 prefixEnd_7379564 3789263352615870655612009 := by
  unfold tailWord_7379564
  simp only [CollatzResearch.WordTrace]
  refine ⟨134577405518553716018188873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179436540691404954690918497 134577405518553716018188873)
  ·
    refine ⟨100933054138915287013641655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134577405518553716018188873 100933054138915287013641655)
    ·
      refine ⟨151399581208372930520462483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100933054138915287013641655 151399581208372930520462483)
      ·
        refine ⟨227099371812559395780693725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151399581208372930520462483 227099371812559395780693725)
        ·
          refine ⟨85162264429709773417760147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227099371812559395780693725 85162264429709773417760147)
          ·
            refine ⟨127743396644564660126640221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85162264429709773417760147 127743396644564660126640221)
            ·
              refine ⟨47903773741711747547490083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127743396644564660126640221 47903773741711747547490083)
              ·
                refine ⟨71855660612567621321235125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47903773741711747547490083 71855660612567621321235125)
                ·
                  refine ⟨6736468182428214498865793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71855660612567621321235125 6736468182428214498865793)
                  ·
                    refine ⟨5052351136821160874149345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6736468182428214498865793 5052351136821160874149345)
                    ·
                      refine ⟨3789263352615870655612009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052351136821160874149345 3789263352615870655612009)
                      ·
                        rfl

theorem cell23_7379564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_7379564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379564 prefixEnd_7379564 := by exact prefixLift 7379564
  have htrace : WordTrace (prefixWord ++ tailWord_7379564) baseStart_7379564 baseEnd_7379564 := by
    simpa [prefixWord, tailWord_7379564, baseEnd_7379564] using wordTrace_append hprefix tailTrace_7379564
  have hstable : (prefixWord ++ tailWord_7379564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379564).length < 2 ^ (prefixWord ++ tailWord_7379564).sum := by decide
  have hdescent : baseEnd_7379564 < baseStart_7379564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379567 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_7379567 : Nat := 118140960795 + 7379567 * 2 ^ 59
def prefixEnd_7379567 : Nat := 4983230072969 + 3 ^ 40 * 7379567 * 2
def baseEnd_7379567 : Nat := 3789264893057834143874495

theorem tailTrace_7379567 : CollatzResearch.WordTrace tailWord_7379567 prefixEnd_7379567 3789264893057834143874495 := by
  unfold tailWord_7379567
  simp only [CollatzResearch.WordTrace]
  refine ⟨269154920456096563548736955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179436613637397709032491303 269154920456096563548736955)
  ·
    refine ⟨403732380684144845323105433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269154920456096563548736955 403732380684144845323105433)
    ·
      refine ⟨302799285513108633992329075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403732380684144845323105433 302799285513108633992329075)
      ·
        refine ⟨454198928269662950988493613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302799285513108633992329075 454198928269662950988493613)
        ·
          refine ⟨170324598101123606620685105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454198928269662950988493613 170324598101123606620685105)
          ·
            refine ⟨127743448575842704965513829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170324598101123606620685105 127743448575842704965513829)
            ·
              refine ⟨23951896607970507181033843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127743448575842704965513829 23951896607970507181033843)
              ·
                refine ⟨35927844911955760771550765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23951896607970507181033843 35927844911955760771550765)
                ·
                  refine ⟨13472941841983410289331537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35927844911955760771550765 13472941841983410289331537)
                  ·
                    refine ⟨10104706381487557716998653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13472941841983410289331537 10104706381487557716998653)
                    ·
                      refine ⟨3789264893057834143874495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10104706381487557716998653 3789264893057834143874495)
                      ·
                        rfl

theorem cell23_7379567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_7379567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379567 prefixEnd_7379567 := by exact prefixLift 7379567
  have htrace : WordTrace (prefixWord ++ tailWord_7379567) baseStart_7379567 baseEnd_7379567 := by
    simpa [prefixWord, tailWord_7379567, baseEnd_7379567] using wordTrace_append hprefix tailTrace_7379567
  have hstable : (prefixWord ++ tailWord_7379567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379567).length < 2 ^ (prefixWord ++ tailWord_7379567).sum := by decide
  have hdescent : baseEnd_7379567 < baseStart_7379567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379568 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 2, 3, 2]
def baseStart_7379568 : Nat := 118140960795 + 7379568 * 2 ^ 59
def prefixEnd_7379568 : Nat := 4983230072969 + 3 ^ 40 * 7379568 * 2
def baseEnd_7379568 : Nat := 3789265406538488639961991

theorem tailTrace_7379568 : CollatzResearch.WordTrace tailWord_7379568 prefixEnd_7379568 3789265406538488639961991 := by
  unfold tailWord_7379568
  simp only [CollatzResearch.WordTrace]
  refine ⟨134577478464546470359761679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179436637952728627146348905 134577478464546470359761679)
  ·
    refine ⟨201866217696819705539642519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134577478464546470359761679 201866217696819705539642519)
    ·
      refine ⟨302799326545229558309463779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201866217696819705539642519 302799326545229558309463779)
      ·
        refine ⟨454198989817844337464195669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302799326545229558309463779 454198989817844337464195669)
        ·
          refine ⟨5322644411927863329658543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 454198989817844337464195669 5322644411927863329658543)
          ·
            refine ⟨7983966617891794994487815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322644411927863329658543 7983966617891794994487815)
            ·
              refine ⟨11975949926837692491731723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983966617891794994487815 11975949926837692491731723)
              ·
                refine ⟨17963924890256538737597585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11975949926837692491731723 17963924890256538737597585)
                ·
                  refine ⟨13472943667692404053198189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17963924890256538737597585 13472943667692404053198189)
                  ·
                    refine ⟨5052353875384651519949321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13472943667692404053198189 5052353875384651519949321)
                    ·
                      refine ⟨3789265406538488639961991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052353875384651519949321 3789265406538488639961991)
                      ·
                        rfl

theorem cell23_7379568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 3, 2].length) (baseStart_7379568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379568 prefixEnd_7379568 := by exact prefixLift 7379568
  have htrace : WordTrace (prefixWord ++ tailWord_7379568) baseStart_7379568 baseEnd_7379568 := by
    simpa [prefixWord, tailWord_7379568, baseEnd_7379568] using wordTrace_append hprefix tailTrace_7379568
  have hstable : (prefixWord ++ tailWord_7379568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379568).length < 2 ^ (prefixWord ++ tailWord_7379568).sum := by decide
  have hdescent : baseEnd_7379568 < baseStart_7379568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379577 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7379577 : Nat := 118140960795 + 7379577 * 2 ^ 59
def prefixEnd_7379577 : Nat := 4983230072969 + 3 ^ 40 * 7379577 * 2
def baseEnd_7379577 : Nat := 3789270027864379104749449

theorem tailTrace_7379577 : CollatzResearch.WordTrace tailWord_7379577 prefixEnd_7379577 3789270027864379104749449 := by
  unfold tailWord_7379577
  simp only [CollatzResearch.WordTrace]
  refine ⟨269155285186060335256600985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179436856790706890171067323 269155285186060335256600985)
  ·
    refine ⟨201866463889545251442450739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269155285186060335256600985 201866463889545251442450739)
    ·
      refine ⟨302799695834317877163676109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201866463889545251442450739 302799695834317877163676109)
      ·
        refine ⟨113549885937869203936378541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302799695834317877163676109 113549885937869203936378541)
        ·
          refine ⟨42581207226700951476141953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113549885937869203936378541 42581207226700951476141953)
          ·
            refine ⟨31935905420025713607106465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42581207226700951476141953 31935905420025713607106465)
            ·
              refine ⟨23951929065019285205329849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31935905420025713607106465 23951929065019285205329849)
              ·
                refine ⟨17963946798764463903997387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23951929065019285205329849 17963946798764463903997387)
                ·
                  refine ⟨26945920198146695855996081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17963946798764463903997387 26945920198146695855996081)
                  ·
                    refine ⟨20209440148610021891997061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26945920198146695855996081 20209440148610021891997061)
                    ·
                      refine ⟨3789270027864379104749449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20209440148610021891997061 3789270027864379104749449)
                      ·
                        rfl

theorem cell23_7379577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7379577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379577 prefixEnd_7379577 := by exact prefixLift 7379577
  have htrace : WordTrace (prefixWord ++ tailWord_7379577) baseStart_7379577 baseEnd_7379577 := by
    simpa [prefixWord, tailWord_7379577, baseEnd_7379577] using wordTrace_append hprefix tailTrace_7379577
  have hstable : (prefixWord ++ tailWord_7379577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379577).length < 2 ^ (prefixWord ++ tailWord_7379577).sum := by decide
  have hdescent : baseEnd_7379577 < baseStart_7379577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379584 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3]
def baseStart_7379584 : Nat := 118140960795 + 7379584 * 2 ^ 59
def prefixEnd_7379584 : Nat := 4983230072969 + 3 ^ 40 * 7379584 * 2
def baseEnd_7379584 : Nat := 3789273622228960577361917

theorem tailTrace_7379584 : CollatzResearch.WordTrace tailWord_7379584 prefixEnd_7379584 3789273622228960577361917 := by
  unfold tailWord_7379584
  simp only [CollatzResearch.WordTrace]
  refine ⟨134577770248517487726052903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179437026998023316968070537 134577770248517487726052903)
  ·
    refine ⟨201866655372776231589079355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134577770248517487726052903 201866655372776231589079355)
    ·
      refine ⟨302799983059164347383619033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201866655372776231589079355 302799983059164347383619033)
      ·
        refine ⟨227099987294373260537714275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302799983059164347383619033 227099987294373260537714275)
        ·
          refine ⟨340649980941559890806571413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227099987294373260537714275 340649980941559890806571413)
          ·
            refine ⟨15967967856635619881558035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340649980941559890806571413 15967967856635619881558035)
            ·
              refine ⟨23951951784953429822337053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15967967856635619881558035 23951951784953429822337053)
              ·
                refine ⟨8981981919357536183376395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23951951784953429822337053 8981981919357536183376395)
                ·
                  refine ⟨13472972879036304275064593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8981981919357536183376395 13472972879036304275064593)
                  ·
                    refine ⟨10104729659277228206298445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13472972879036304275064593 10104729659277228206298445)
                    ·
                      refine ⟨3789273622228960577361917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10104729659277228206298445 3789273622228960577361917)
                      ·
                        rfl

theorem cell23_7379584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_7379584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379584 prefixEnd_7379584 := by exact prefixLift 7379584
  have htrace : WordTrace (prefixWord ++ tailWord_7379584) baseStart_7379584 baseEnd_7379584 := by
    simpa [prefixWord, tailWord_7379584, baseEnd_7379584] using wordTrace_append hprefix tailTrace_7379584
  have hstable : (prefixWord ++ tailWord_7379584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379584).length < 2 ^ (prefixWord ++ tailWord_7379584).sum := by decide
  have hdescent : baseEnd_7379584 < baseStart_7379584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379598 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7379598 : Nat := 118140960795 + 7379598 * 2 ^ 59
def prefixEnd_7379598 : Nat := 4983230072969 + 3 ^ 40 * 7379598 * 2
def baseEnd_7379598 : Nat := 3789280810958123522586853

theorem tailTrace_7379598 : CollatzResearch.WordTrace tailWord_7379598 prefixEnd_7379598 3789280810958123522586853 := by
  unfold tailWord_7379598
  simp only [CollatzResearch.WordTrace]
  refine ⟨33644506389873031980389431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179437367412656170562076965 33644506389873031980389431)
  ·
    refine ⟨50466759584809547970584147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33644506389873031980389431 50466759584809547970584147)
    ·
      refine ⟨75700139377214321955876221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50466759584809547970584147 75700139377214321955876221)
      ·
        refine ⟨28387552266455370733453583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75700139377214321955876221 28387552266455370733453583)
        ·
          refine ⟨42581328399683056100180375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28387552266455370733453583 42581328399683056100180375)
          ·
            refine ⟨63871992599524584150270563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42581328399683056100180375 63871992599524584150270563)
            ·
              refine ⟨95807988899286876225405845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63871992599524584150270563 95807988899286876225405845)
              ·
                refine ⟨4490999479654072323065899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95807988899286876225405845 4490999479654072323065899)
                ·
                  refine ⟨6736499219481108484598849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490999479654072323065899 6736499219481108484598849)
                  ·
                    refine ⟨5052374414610831363449137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6736499219481108484598849 5052374414610831363449137)
                    ·
                      refine ⟨3789280810958123522586853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052374414610831363449137 3789280810958123522586853)
                      ·
                        rfl

theorem cell23_7379598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7379598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379598 prefixEnd_7379598 := by exact prefixLift 7379598
  have htrace : WordTrace (prefixWord ++ tailWord_7379598) baseStart_7379598 baseEnd_7379598 := by
    simpa [prefixWord, tailWord_7379598, baseEnd_7379598] using wordTrace_append hprefix tailTrace_7379598
  have hstable : (prefixWord ++ tailWord_7379598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379598).length < 2 ^ (prefixWord ++ tailWord_7379598).sum := by decide
  have hdescent : baseEnd_7379598 < baseStart_7379598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379649 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7379649 : Nat := 118140960795 + 7379649 * 2 ^ 59
def prefixEnd_7379649 : Nat := 4983230072969 + 3 ^ 40 * 7379649 * 2
def baseEnd_7379649 : Nat := 3789306998471502823049119

theorem tailTrace_7379649 : CollatzResearch.WordTrace tailWord_7379649 prefixEnd_7379649 3789306998471502823049119 := by
  unfold tailWord_7379649
  simp only [CollatzResearch.WordTrace]
  refine ⟨269157911241799491553222001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179438607494532994368814667 269157911241799491553222001)
  ·
    refine ⟨201868433431349618664916501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269157911241799491553222001 201868433431349618664916501)
    ·
      refine ⟨9462582817094513374917961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201868433431349618664916501 9462582817094513374917961)
      ·
        refine ⟨7096937112820885031188471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9462582817094513374917961 7096937112820885031188471)
        ·
          refine ⟨10645405669231327546782707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7096937112820885031188471 10645405669231327546782707)
          ·
            refine ⟨15968108503846991320174061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10645405669231327546782707 15968108503846991320174061)
            ·
              refine ⟨5988040688942621745065273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15968108503846991320174061 5988040688942621745065273)
              ·
                refine ⟨4491030516706966308798955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988040688942621745065273 4491030516706966308798955)
                ·
                  refine ⟨6736545775060449463198433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491030516706966308798955 6736545775060449463198433)
                  ·
                    refine ⟨5052409331295337097398825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6736545775060449463198433 5052409331295337097398825)
                    ·
                      refine ⟨3789306998471502823049119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052409331295337097398825 3789306998471502823049119)
                      ·
                        rfl

theorem cell23_7379649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7379649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379649 prefixEnd_7379649 := by exact prefixLift 7379649
  have htrace : WordTrace (prefixWord ++ tailWord_7379649) baseStart_7379649 baseEnd_7379649 := by
    simpa [prefixWord, tailWord_7379649, baseEnd_7379649] using wordTrace_append hprefix tailTrace_7379649
  have hstable : (prefixWord ++ tailWord_7379649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379649).length < 2 ^ (prefixWord ++ tailWord_7379649).sum := by decide
  have hdescent : baseEnd_7379649 < baseStart_7379649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379727 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_7379727 : Nat := 118140960795 + 7379727 * 2 ^ 59
def prefixEnd_7379727 : Nat := 4983230072969 + 3 ^ 40 * 7379727 * 2
def baseEnd_7379727 : Nat := 3789347049962553517873759

theorem tailTrace_7379727 : CollatzResearch.WordTrace tailWord_7379727 prefixEnd_7379727 3789347049962553517873759 := by
  unfold tailWord_7379727
  simp only [CollatzResearch.WordTrace]
  refine ⟨269160756135516910874561435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179440504090344607249707623 269160756135516910874561435)
  ·
    refine ⟨403741134203275366311842153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269160756135516910874561435 403741134203275366311842153)
    ·
      refine ⟨302805850652456524733881615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403741134203275366311842153 302805850652456524733881615)
      ·
        refine ⟨454208775978684787100822423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302805850652456524733881615 454208775978684787100822423)
        ·
          refine ⟨681313163968027180651233635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454208775978684787100822423 681313163968027180651233635)
          ·
            refine ⟨1021969745952040770976850453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681313163968027180651233635 1021969745952040770976850453)
            ·
              refine ⟨47904831841501911139539865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1021969745952040770976850453 47904831841501911139539865)
              ·
                refine ⟨35928623881126433354654899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47904831841501911139539865 35928623881126433354654899)
                ·
                  refine ⟨53892935821689650031982349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35928623881126433354654899 53892935821689650031982349)
                  ·
                    refine ⟨20209850933133618761993381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53892935821689650031982349 20209850933133618761993381)
                    ·
                      refine ⟨3789347049962553517873759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20209850933133618761993381 3789347049962553517873759)
                      ·
                        rfl

theorem cell23_7379727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_7379727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379727 prefixEnd_7379727 := by exact prefixLift 7379727
  have htrace : WordTrace (prefixWord ++ tailWord_7379727) baseStart_7379727 baseEnd_7379727 := by
    simpa [prefixWord, tailWord_7379727, baseEnd_7379727] using wordTrace_append hprefix tailTrace_7379727
  have hstable : (prefixWord ++ tailWord_7379727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379727).length < 2 ^ (prefixWord ++ tailWord_7379727).sum := by decide
  have hdescent : baseEnd_7379727 < baseStart_7379727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379741 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_7379741 : Nat := 118140960795 + 7379741 * 2 ^ 59
def prefixEnd_7379741 : Nat := 4983230072969 + 3 ^ 40 * 7379741 * 2
def baseEnd_7379741 : Nat := 1263118079563905487699565

theorem tailTrace_7379741 : CollatzResearch.WordTrace tailWord_7379741 prefixEnd_7379741 1263118079563905487699565 := by
  unfold tailWord_7379741
  simp only [CollatzResearch.WordTrace]
  refine ⟨269161266757466191265571077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179440844504977460843714051 269161266757466191265571077)
  ·
    refine ⟨50467737517024910862294577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269161266757466191265571077 50467737517024910862294577)
    ·
      refine ⟨37850803137768683146720933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50467737517024910862294577 37850803137768683146720933)
      ·
        refine ⟨7097025588331628090010175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37850803137768683146720933 7097025588331628090010175)
        ·
          refine ⟨10645538382497442135015263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097025588331628090010175 10645538382497442135015263)
          ·
            refine ⟨15968307573746163202522895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10645538382497442135015263 15968307573746163202522895)
            ·
              refine ⟨23952461360619244803784343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15968307573746163202522895 23952461360619244803784343)
              ·
                refine ⟨35928692040928867205676515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23952461360619244803784343 35928692040928867205676515)
                ·
                  refine ⟨53893038061393300808514773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35928692040928867205676515 53893038061393300808514773)
                  ·
                    refine ⟨1263118079563905487699565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53893038061393300808514773 1263118079563905487699565)
                    ·
                      rfl

theorem cell23_7379741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_7379741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379741 prefixEnd_7379741 := by exact prefixLift 7379741
  have htrace : WordTrace (prefixWord ++ tailWord_7379741) baseStart_7379741 baseEnd_7379741 := by
    simpa [prefixWord, tailWord_7379741, baseEnd_7379741] using wordTrace_append hprefix tailTrace_7379741
  have hstable : (prefixWord ++ tailWord_7379741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379741).length < 2 ^ (prefixWord ++ tailWord_7379741).sum := by decide
  have hdescent : baseEnd_7379741 < baseStart_7379741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379744 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7379744 : Nat := 118140960795 + 7379744 * 2 ^ 59
def prefixEnd_7379744 : Nat := 4983230072969 + 3 ^ 40 * 7379744 * 2
def baseEnd_7379744 : Nat := 3789355779133679951361181

theorem tailTrace_7379744 : CollatzResearch.WordTrace tailWord_7379744 prefixEnd_7379744 3789355779133679951361181 := by
  unfold tailWord_7379744
  simp only [CollatzResearch.WordTrace]
  refine ⟨134580688088227661388965143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179440917450970215185286857 134580688088227661388965143)
  ·
    refine ⟨201871032132341492083447715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134580688088227661388965143 201871032132341492083447715)
    ·
      refine ⟨302806548198512238125171573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201871032132341492083447715 302806548198512238125171573)
      ·
        refine ⟨28388113893610522324234835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302806548198512238125171573 28388113893610522324234835)
        ·
          refine ⟨42582170840415783486352253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28388113893610522324234835 42582170840415783486352253)
          ·
            refine ⟨15968314065155918807382095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42582170840415783486352253 15968314065155918807382095)
            ·
              refine ⟨23952471097733878211073143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15968314065155918807382095 23952471097733878211073143)
              ·
                refine ⟨35928706646600817316609715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23952471097733878211073143 35928706646600817316609715)
                ·
                  refine ⟨53893059969901225974914573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35928706646600817316609715 53893059969901225974914573)
                  ·
                    refine ⟨20209897488712959740592965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53893059969901225974914573 20209897488712959740592965)
                    ·
                      refine ⟨3789355779133679951361181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20209897488712959740592965 3789355779133679951361181)
                      ·
                        rfl

theorem cell23_7379744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7379744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379744 prefixEnd_7379744 := by exact prefixLift 7379744
  have htrace : WordTrace (prefixWord ++ tailWord_7379744) baseStart_7379744 baseEnd_7379744 := by
    simpa [prefixWord, tailWord_7379744, baseEnd_7379744] using wordTrace_append hprefix tailTrace_7379744
  have hstable : (prefixWord ++ tailWord_7379744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379744).length < 2 ^ (prefixWord ++ tailWord_7379744).sum := by decide
  have hdescent : baseEnd_7379744 < baseStart_7379744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379767 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 8]
def baseStart_7379767 : Nat := 118140960795 + 7379767 * 2 ^ 59
def prefixEnd_7379767 : Nat := 4983230072969 + 3 ^ 40 * 7379767 * 2
def baseEnd_7379767 : Nat := 421040843243192595708175

theorem tailTrace_7379767 : CollatzResearch.WordTrace tailWord_7379767 prefixEnd_7379767 421040843243192595708175 := by
  unfold tailWord_7379767
  simp only [CollatzResearch.WordTrace]
  refine ⟨269162215055371997706017555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179441476703581331804011703 269162215055371997706017555)
  ·
    refine ⟨403743322583057996559026333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269162215055371997706017555 403743322583057996559026333)
    ·
      refine ⟨151403745968646748709634875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403743322583057996559026333 151403745968646748709634875)
      ·
        refine ⟨227105618952970123064452313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151403745968646748709634875 227105618952970123064452313)
        ·
          refine ⟨170329214214727592298339235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227105618952970123064452313 170329214214727592298339235)
          ·
            refine ⟨255493821322091388447508853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170329214214727592298339235 255493821322091388447508853)
            ·
              refine ⟨23952545748946067666953955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255493821322091388447508853 23952545748946067666953955)
              ·
                refine ⟨35928818623419101500430933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23952545748946067666953955 35928818623419101500430933)
                ·
                  refine ⟨421040843243192595708175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35928818623419101500430933 421040843243192595708175)
                  ·
                    rfl

theorem cell23_7379767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 8].length) (baseStart_7379767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379767 prefixEnd_7379767 := by exact prefixLift 7379767
  have htrace : WordTrace (prefixWord ++ tailWord_7379767) baseStart_7379767 baseEnd_7379767 := by
    simpa [prefixWord, tailWord_7379767, baseEnd_7379767] using wordTrace_append hprefix tailTrace_7379767
  have hstable : (prefixWord ++ tailWord_7379767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379767).length < 2 ^ (prefixWord ++ tailWord_7379767).sum := by decide
  have hdescent : baseEnd_7379767 < baseStart_7379767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379794 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_7379794 : Nat := 118140960795 + 7379794 * 2 ^ 59
def prefixEnd_7379794 : Nat := 4983230072969 + 3 ^ 40 * 7379794 * 2
def baseEnd_7379794 : Nat := 3789381453166404755735951

theorem tailTrace_7379794 : CollatzResearch.WordTrace tailWord_7379794 prefixEnd_7379794 3789381453166404755735951 := by
  unfold tailWord_7379794
  simp only [CollatzResearch.WordTrace]
  refine ⟨67290799956568545329312609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179442133217516120878166957 67290799956568545329312609)
  ·
    refine ⟨50468099967426408996984457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67290799956568545329312609 50468099967426408996984457)
    ·
      refine ⟨37851074975569806747738343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50468099967426408996984457 37851074975569806747738343)
      ·
        refine ⟨56776612463354710121607515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37851074975569806747738343 56776612463354710121607515)
        ·
          refine ⟨85164918695032065182411273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56776612463354710121607515 85164918695032065182411273)
          ·
            refine ⟨63873689021274048886808455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85164918695032065182411273 63873689021274048886808455)
            ·
              refine ⟨95810533531911073330212683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63873689021274048886808455 95810533531911073330212683)
              ·
                refine ⟨143715800297866609995319025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95810533531911073330212683 143715800297866609995319025)
                ·
                  refine ⟨107786850223399957496489269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143715800297866609995319025 107786850223399957496489269)
                  ·
                    refine ⟨10105017208443746015295869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107786850223399957496489269 10105017208443746015295869)
                    ·
                      refine ⟨3789381453166404755735951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105017208443746015295869 3789381453166404755735951)
                      ·
                        rfl

theorem cell23_7379794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_7379794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379794 prefixEnd_7379794 := by exact prefixLift 7379794
  have htrace : WordTrace (prefixWord ++ tailWord_7379794) baseStart_7379794 baseEnd_7379794 := by
    simpa [prefixWord, tailWord_7379794, baseEnd_7379794] using wordTrace_append hprefix tailTrace_7379794
  have hstable : (prefixWord ++ tailWord_7379794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379794).length < 2 ^ (prefixWord ++ tailWord_7379794).sum := by decide
  have hdescent : baseEnd_7379794 < baseStart_7379794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379822 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_7379822 : Nat := 118140960795 + 7379822 * 2 ^ 59
def prefixEnd_7379822 : Nat := 4983230072969 + 3 ^ 40 * 7379822 * 2
def baseEnd_7379822 : Nat := 1263131943541576882061941

theorem tailTrace_7379822 : CollatzResearch.WordTrace tailWord_7379822 prefixEnd_7379822 1263131943541576882061941 := by
  unfold tailWord_7379822
  simp only [CollatzResearch.WordTrace]
  refine ⟨33645527633771592762408715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179442814046781828066179813 33645527633771592762408715)
  ·
    refine ⟨50468291450657389143613073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33645527633771592762408715 50468291450657389143613073)
    ·
      refine ⟨37851218587993041857709805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50468291450657389143613073 37851218587993041857709805)
      ·
        refine ⟨14194206970497390696641177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37851218587993041857709805 14194206970497390696641177)
        ·
          refine ⟨10645655227873043022480883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14194206970497390696641177 10645655227873043022480883)
          ·
            refine ⟨15968482841809564533721325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10645655227873043022480883 15968482841809564533721325)
            ·
              refine ⟨5988181065678586700145497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15968482841809564533721325 5988181065678586700145497)
              ·
                refine ⟨4491135799258940025109123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988181065678586700145497 4491135799258940025109123)
                ·
                  refine ⟨6736703698888410037663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491135799258940025109123 6736703698888410037663685)
                  ·
                    refine ⟨1263131943541576882061941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736703698888410037663685 1263131943541576882061941)
                    ·
                      rfl

theorem cell23_7379822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_7379822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379822 prefixEnd_7379822 := by exact prefixLift 7379822
  have htrace : WordTrace (prefixWord ++ tailWord_7379822) baseStart_7379822 baseEnd_7379822 := by
    simpa [prefixWord, tailWord_7379822, baseEnd_7379822] using wordTrace_append hprefix tailTrace_7379822
  have hstable : (prefixWord ++ tailWord_7379822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379822).length < 2 ^ (prefixWord ++ tailWord_7379822).sum := by decide
  have hdescent : baseEnd_7379822 < baseStart_7379822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379834 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_7379834 : Nat := 118140960795 + 7379834 * 2 ^ 59
def prefixEnd_7379834 : Nat := 4983230072969 + 3 ^ 40 * 7379834 * 2
def baseEnd_7379834 : Nat := 3789401992392584599235767

theorem tailTrace_7379834 : CollatzResearch.WordTrace tailWord_7379834 prefixEnd_7379834 3789401992392584599235767 := by
  unfold tailWord_7379834
  simp only [CollatzResearch.WordTrace]
  refine ⟨67291164686532317037176639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179443105830752845432471037 67291164686532317037176639)
  ·
    refine ⟨100936747029798475555764959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67291164686532317037176639 100936747029798475555764959)
    ·
      refine ⟨151405120544697713333647439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100936747029798475555764959 151405120544697713333647439)
      ·
        refine ⟨227107680817046570000471159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151405120544697713333647439 227107680817046570000471159)
        ·
          refine ⟨340661521225569855000706739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227107680817046570000471159 340661521225569855000706739)
          ·
            refine ⟨510992281838354782501060109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340661521225569855000706739 510992281838354782501060109)
            ·
              refine ⟨191622105689383043437897541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510992281838354782501060109 191622105689383043437897541)
              ·
                refine ⟨35929144816759320644605789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191622105689383043437897541 35929144816759320644605789)
                ·
                  refine ⟨13473429306284745241727171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35929144816759320644605789 13473429306284745241727171)
                  ·
                    refine ⟨20210143959427117862590757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13473429306284745241727171 20210143959427117862590757)
                    ·
                      refine ⟨3789401992392584599235767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20210143959427117862590757 3789401992392584599235767)
                      ·
                        rfl

theorem cell23_7379834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_7379834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379834 prefixEnd_7379834 := by exact prefixLift 7379834
  have htrace : WordTrace (prefixWord ++ tailWord_7379834) baseStart_7379834 baseEnd_7379834 := by
    simpa [prefixWord, tailWord_7379834, baseEnd_7379834] using wordTrace_append hprefix tailTrace_7379834
  have hstable : (prefixWord ++ tailWord_7379834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379834).length < 2 ^ (prefixWord ++ tailWord_7379834).sum := by decide
  have hdescent : baseEnd_7379834 < baseStart_7379834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379844 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_7379844 : Nat := 118140960795 + 7379844 * 2 ^ 59
def prefixEnd_7379844 : Nat := 4983230072969 + 3 ^ 40 * 7379844 * 2
def baseEnd_7379844 : Nat := 1263135709066376520036907

theorem tailTrace_7379844 : CollatzResearch.WordTrace tailWord_7379844 prefixEnd_7379844 1263135709066376520036907 := by
  unfold tailWord_7379844
  simp only [CollatzResearch.WordTrace]
  refine ⟨134582511738046519928285293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179443348984062026571047057 134582511738046519928285293)
  ·
    refine ⟨50468441901767444973106985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134582511738046519928285293 50468441901767444973106985)
    ·
      refine ⟨37851331426325583729830239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50468441901767444973106985 37851331426325583729830239)
      ·
        refine ⟨56776997139488375594745359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37851331426325583729830239 56776997139488375594745359)
        ·
          refine ⟨85165495709232563392118039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56776997139488375594745359 85165495709232563392118039)
          ·
            refine ⟨127748243563848845088177059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85165495709232563392118039 127748243563848845088177059)
            ·
              refine ⟨191622365345773267632265589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127748243563848845088177059 191622365345773267632265589)
              ·
                refine ⟨17964596751166243840524899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191622365345773267632265589 17964596751166243840524899)
                ·
                  refine ⟨26946895126749365760787349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17964596751166243840524899 26946895126749365760787349)
                  ·
                    refine ⟨1263135709066376520036907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26946895126749365760787349 1263135709066376520036907)
                    ·
                      rfl

theorem cell23_7379844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_7379844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379844 prefixEnd_7379844 := by exact prefixLift 7379844
  have htrace : WordTrace (prefixWord ++ tailWord_7379844) baseStart_7379844 baseEnd_7379844 := by
    simpa [prefixWord, tailWord_7379844, baseEnd_7379844] using wordTrace_append hprefix tailTrace_7379844
  have hstable : (prefixWord ++ tailWord_7379844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379844).length < 2 ^ (prefixWord ++ tailWord_7379844).sum := by decide
  have hdescent : baseEnd_7379844 < baseStart_7379844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379848 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 1, 5]
def baseStart_7379848 : Nat := 118140960795 + 7379848 * 2 ^ 59
def prefixEnd_7379848 : Nat := 4983230072969 + 3 ^ 40 * 7379848 * 2
def baseEnd_7379848 : Nat := 1263136393707249181486901

theorem tailTrace_7379848 : CollatzResearch.WordTrace tailWord_7379848 prefixEnd_7379848 1263136393707249181486901 := by
  unfold tailWord_7379848
  simp only [CollatzResearch.WordTrace]
  refine ⟨134582584684039274269858099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179443446245385699026477465 134582584684039274269858099)
  ·
    refine ⟨201873877026058911404787149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134582584684039274269858099 201873877026058911404787149)
    ·
      refine ⟨75702703884772091776795181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201873877026058911404787149 75702703884772091776795181)
      ·
        refine ⟨28388513956789534416298193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75702703884772091776795181 28388513956789534416298193)
        ·
          refine ⟨21291385467592150812223645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28388513956789534416298193 21291385467592150812223645)
          ·
            refine ⟨7984269550347056554583867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21291385467592150812223645 7984269550347056554583867)
            ·
              refine ⟨11976404325520584831875801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984269550347056554583867 11976404325520584831875801)
              ·
                refine ⟨8982303244140438623906851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11976404325520584831875801 8982303244140438623906851)
                ·
                  refine ⟨13473454866210657935860277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982303244140438623906851 13473454866210657935860277)
                  ·
                    refine ⟨1263136393707249181486901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13473454866210657935860277 1263136393707249181486901)
                    ·
                      rfl

theorem cell23_7379848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_7379848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379848 prefixEnd_7379848 := by exact prefixLift 7379848
  have htrace : WordTrace (prefixWord ++ tailWord_7379848) baseStart_7379848 baseEnd_7379848 := by
    simpa [prefixWord, tailWord_7379848, baseEnd_7379848] using wordTrace_append hprefix tailTrace_7379848
  have hstable : (prefixWord ++ tailWord_7379848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379848).length < 2 ^ (prefixWord ++ tailWord_7379848).sum := by decide
  have hdescent : baseEnd_7379848 < baseStart_7379848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379851 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 4]
def baseStart_7379851 : Nat := 118140960795 + 7379851 * 2 ^ 59
def prefixEnd_7379851 : Nat := 4983230072969 + 3 ^ 40 * 7379851 * 2
def baseEnd_7379851 : Nat := 3789410721563711032723189

theorem tailTrace_7379851 : CollatzResearch.WordTrace tailWord_7379851 prefixEnd_7379851 3789410721563711032723189 := by
  unfold tailWord_7379851
  simp only [CollatzResearch.WordTrace]
  refine ⟨269165278787067680052075407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179443519191378453368050271 269165278787067680052075407)
  ·
    refine ⟨403747918180601520078113111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269165278787067680052075407 403747918180601520078113111)
    ·
      refine ⟨605621877270902280117169667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403747918180601520078113111 605621877270902280117169667)
      ·
        refine ⟨908432815906353420175754501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605621877270902280117169667 908432815906353420175754501)
        ·
          refine ⟨170331152982441266282953969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 908432815906353420175754501 170331152982441266282953969)
          ·
            refine ⟨127748364736830949712215477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170331152982441266282953969 127748364736830949712215477)
            ·
              refine ⟨11976409194077901535520201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127748364736830949712215477 11976409194077901535520201)
              ·
                refine ⟨8982306895558426151640151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11976409194077901535520201 8982306895558426151640151)
                ·
                  refine ⟨13473460343337639227460227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982306895558426151640151 13473460343337639227460227)
                  ·
                    refine ⟨20210190515006458841190341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13473460343337639227460227 20210190515006458841190341)
                    ·
                      refine ⟨3789410721563711032723189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20210190515006458841190341 3789410721563711032723189)
                      ·
                        rfl

theorem cell23_7379851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 4].length) (baseStart_7379851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379851 prefixEnd_7379851 := by exact prefixLift 7379851
  have htrace : WordTrace (prefixWord ++ tailWord_7379851) baseStart_7379851 baseEnd_7379851 := by
    simpa [prefixWord, tailWord_7379851, baseEnd_7379851] using wordTrace_append hprefix tailTrace_7379851
  have hstable : (prefixWord ++ tailWord_7379851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379851).length < 2 ^ (prefixWord ++ tailWord_7379851).sum := by decide
  have hdescent : baseEnd_7379851 < baseStart_7379851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379871 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7379871 : Nat := 118140960795 + 7379871 * 2 ^ 59
def prefixEnd_7379871 : Nat := 4983230072969 + 3 ^ 40 * 7379871 * 2
def baseEnd_7379871 : Nat := 3789420991176800954473097

theorem tailTrace_7379871 : CollatzResearch.WordTrace tailWord_7379871 prefixEnd_7379871 3789420991176800954473097 := by
  unfold tailWord_7379871
  simp only [CollatzResearch.WordTrace]
  refine ⟨269166008246995223467803467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179444005497996815645202311 269166008246995223467803467)
  ·
    refine ⟨403749012370492835201705201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269166008246995223467803467 403749012370492835201705201)
    ·
      refine ⟨302811759277869626401278901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403749012370492835201705201 302811759277869626401278901)
      ·
        refine ⟨28388602432300277475119897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302811759277869626401278901 28388602432300277475119897)
        ·
          refine ⟨21291451824225208106339923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28388602432300277475119897 21291451824225208106339923)
          ·
            refine ⟨31937177736337812159509885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21291451824225208106339923 31937177736337812159509885)
            ·
              refine ⟨11976441651126679559816207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31937177736337812159509885 11976441651126679559816207)
              ·
                refine ⟨17964662476690019339724311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976441651126679559816207 17964662476690019339724311)
                ·
                  refine ⟨26946993715035029009586467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17964662476690019339724311 26946993715035029009586467)
                  ·
                    refine ⟨40420490572552543514379701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26946993715035029009586467 40420490572552543514379701)
                    ·
                      refine ⟨3789420991176800954473097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40420490572552543514379701 3789420991176800954473097)
                      ·
                        rfl

theorem cell23_7379871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7379871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379871 prefixEnd_7379871 := by exact prefixLift 7379871
  have htrace : WordTrace (prefixWord ++ tailWord_7379871) baseStart_7379871 baseEnd_7379871 := by
    simpa [prefixWord, tailWord_7379871, baseEnd_7379871] using wordTrace_append hprefix tailTrace_7379871
  have hstable : (prefixWord ++ tailWord_7379871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379871).length < 2 ^ (prefixWord ++ tailWord_7379871).sum := by decide
  have hdescent : baseEnd_7379871 < baseStart_7379871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379874 : List Nat := [3, 3, 1, 2, 2, 12]
def baseStart_7379874 : Nat := 118140960795 + 7379874 * 2 ^ 59
def prefixEnd_7379874 : Nat := 4983230072969 + 3 ^ 40 * 7379874 * 2
def baseEnd_7379874 : Nat := 15594331405838536801381

theorem tailTrace_7379874 : CollatzResearch.WordTrace tailWord_7379874 prefixEnd_7379874 15594331405838536801381 := by
  unfold tailWord_7379874
  simp only [CollatzResearch.WordTrace]
  refine ⟨67291529416496088745040669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179444078443989569986775117 67291529416496088745040669)
  ·
    refine ⟨25234323531186033279390251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67291529416496088745040669 25234323531186033279390251)
    ·
      refine ⟨37851485296779049919085377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25234323531186033279390251 37851485296779049919085377)
      ·
        refine ⟨28388613972584287439314033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37851485296779049919085377 28388613972584287439314033)
        ·
          refine ⟨21291460479438215579485525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28388613972584287439314033 21291460479438215579485525)
          ·
            refine ⟨15594331405838536801381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21291460479438215579485525 15594331405838536801381)
            ·
              rfl

theorem cell23_7379874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 12].length) (baseStart_7379874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379874 prefixEnd_7379874 := by exact prefixLift 7379874
  have htrace : WordTrace (prefixWord ++ tailWord_7379874) baseStart_7379874 baseEnd_7379874 := by
    simpa [prefixWord, tailWord_7379874, baseEnd_7379874] using wordTrace_append hprefix tailTrace_7379874
  have hstable : (prefixWord ++ tailWord_7379874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379874).length < 2 ^ (prefixWord ++ tailWord_7379874).sum := by decide
  have hdescent : baseEnd_7379874 < baseStart_7379874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379879 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_7379879 : Nat := 118140960795 + 7379879 * 2 ^ 59
def prefixEnd_7379879 : Nat := 4983230072969 + 3 ^ 40 * 7379879 * 2
def baseEnd_7379879 : Nat := 3789425099022036923173061

theorem tailTrace_7379879 : CollatzResearch.WordTrace tailWord_7379879 prefixEnd_7379879 3789425099022036923173061 := by
  unfold tailWord_7379879
  simp only [CollatzResearch.WordTrace]
  refine ⟨269166300030966240834094691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179444200020644160556063127 269166300030966240834094691)
  ·
    refine ⟨403749450046449361251142037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269166300030966240834094691 403749450046449361251142037)
    ·
      refine ⟨18925755470927313808647283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 403749450046449361251142037 18925755470927313808647283)
      ·
        refine ⟨28388633206390970712970925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18925755470927313808647283 28388633206390970712970925)
        ·
          refine ⟨10645737452396614017364097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28388633206390970712970925 10645737452396614017364097)
          ·
            refine ⟨7984303089297460513023073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10645737452396614017364097 7984303089297460513023073)
            ·
              refine ⟨5988227316973095384767305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984303089297460513023073 5988227316973095384767305)
              ·
                refine ⟨4491170487729821538575479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988227316973095384767305 4491170487729821538575479)
                ·
                  refine ⟨6736755731594732307863219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491170487729821538575479 6736755731594732307863219)
                  ·
                    refine ⟨10105133597392098461794829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6736755731594732307863219 10105133597392098461794829)
                    ·
                      refine ⟨3789425099022036923173061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105133597392098461794829 3789425099022036923173061)
                      ·
                        rfl

theorem cell23_7379879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_7379879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379879 prefixEnd_7379879 := by exact prefixLift 7379879
  have htrace : WordTrace (prefixWord ++ tailWord_7379879) baseStart_7379879 baseEnd_7379879 := by
    simpa [prefixWord, tailWord_7379879, baseEnd_7379879] using wordTrace_append hprefix tailTrace_7379879
  have hstable : (prefixWord ++ tailWord_7379879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379879).length < 2 ^ (prefixWord ++ tailWord_7379879).sum := by decide
  have hdescent : baseEnd_7379879 < baseStart_7379879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379914 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_7379914 : Nat := 118140960795 + 7379914 * 2 ^ 59
def prefixEnd_7379914 : Nat := 4983230072969 + 3 ^ 40 * 7379914 * 2
def baseEnd_7379914 : Nat := 3789443070844944286235399

theorem tailTrace_7379914 : CollatzResearch.WordTrace tailWord_7379914 prefixEnd_7379914 3789443070844944286235399 := by
  unfold tailWord_7379914
  simp only [CollatzResearch.WordTrace]
  refine ⟨67291894146459860452904699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179445051057226294541079197 67291894146459860452904699)
  ·
    refine ⟨100937841219689790679357049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67291894146459860452904699 100937841219689790679357049)
    ·
      refine ⟨75703380914767343009517787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100937841219689790679357049 75703380914767343009517787)
      ·
        refine ⟨113555071372151014514276681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75703380914767343009517787 113555071372151014514276681)
        ·
          refine ⟨85166303529113260885707511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113555071372151014514276681 85166303529113260885707511)
          ·
            refine ⟨127749455293669891328561267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85166303529113260885707511 127749455293669891328561267)
            ·
              refine ⟨191624182940504836992841901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127749455293669891328561267 191624182940504836992841901)
              ·
                refine ⟨71859068602689313872315713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191624182940504836992841901 71859068602689313872315713)
                ·
                  refine ⟨53894301452016985404236785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71859068602689313872315713 53894301452016985404236785)
                  ·
                    refine ⟨40420726089012739053177589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53894301452016985404236785 40420726089012739053177589)
                    ·
                      refine ⟨3789443070844944286235399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40420726089012739053177589 3789443070844944286235399)
                      ·
                        rfl

theorem cell23_7379914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_7379914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379914 prefixEnd_7379914 := by exact prefixLift 7379914
  have htrace : WordTrace (prefixWord ++ tailWord_7379914) baseStart_7379914 baseEnd_7379914 := by
    simpa [prefixWord, tailWord_7379914, baseEnd_7379914] using wordTrace_append hprefix tailTrace_7379914
  have hstable : (prefixWord ++ tailWord_7379914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379914).length < 2 ^ (prefixWord ++ tailWord_7379914).sum := by decide
  have hdescent : baseEnd_7379914 < baseStart_7379914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379922 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7379922 : Nat := 118140960795 + 7379922 * 2 ^ 59
def prefixEnd_7379922 : Nat := 4983230072969 + 3 ^ 40 * 7379922 * 2
def baseEnd_7379922 : Nat := 3789447178690180254935363

theorem tailTrace_7379922 : CollatzResearch.WordTrace tailWord_7379922 prefixEnd_7379922 3789447178690180254935363 := by
  unfold tailWord_7379922
  simp only [CollatzResearch.WordTrace]
  refine ⟨67291967092452614794477505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179445245579873639451940013 67291967092452614794477505)
  ·
    refine ⟨50468975319339461095858129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67291967092452614794477505 50468975319339461095858129)
    ·
      refine ⟨37851731489504595821893597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50468975319339461095858129 37851731489504595821893597)
      ·
        refine ⟨14194399308564223433210099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37851731489504595821893597 14194399308564223433210099)
        ·
          refine ⟨21291598962846335149815149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14194399308564223433210099 21291598962846335149815149)
          ·
            refine ⟨7984349611067375681180681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21291598962846335149815149 7984349611067375681180681)
            ·
              refine ⟨5988262208300531760885511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984349611067375681180681 5988262208300531760885511)
              ·
                refine ⟨8982393312450797641328267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988262208300531760885511 8982393312450797641328267)
                ·
                  refine ⟨13473589968676196461992401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982393312450797641328267 13473589968676196461992401)
                  ·
                    refine ⟨10105192476507147346494301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13473589968676196461992401 10105192476507147346494301)
                    ·
                      refine ⟨3789447178690180254935363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105192476507147346494301 3789447178690180254935363)
                      ·
                        rfl

theorem cell23_7379922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7379922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379922 prefixEnd_7379922 := by exact prefixLift 7379922
  have htrace : WordTrace (prefixWord ++ tailWord_7379922) baseStart_7379922 baseEnd_7379922 := by
    simpa [prefixWord, tailWord_7379922, baseEnd_7379922] using wordTrace_append hprefix tailTrace_7379922
  have hstable : (prefixWord ++ tailWord_7379922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379922).length < 2 ^ (prefixWord ++ tailWord_7379922).sum := by decide
  have hdescent : baseEnd_7379922 < baseStart_7379922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7379956 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7379956 : Nat := 118140960795 + 7379956 * 2 ^ 59
def prefixEnd_7379956 : Nat := 4983230072969 + 3 ^ 40 * 7379956 * 2
def baseEnd_7379956 : Nat := 3789464637032433121910207

theorem tailTrace_7379956 : CollatzResearch.WordTrace tailWord_7379956 prefixEnd_7379956 3789464637032433121910207 := by
  unfold tailWord_7379956
  simp only [CollatzResearch.WordTrace]
  refine ⟨134584554225843641492323861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179446072301124855323098481 134584554225843641492323861)
  ·
    refine ⟨6308650979336420694952681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134584554225843641492323861 6308650979336420694952681)
    ·
      refine ⟨4731488234502315521214511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6308650979336420694952681 4731488234502315521214511)
      ·
        refine ⟨7097232351753473281821767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731488234502315521214511 7097232351753473281821767)
        ·
          refine ⟨10645848527630209922732651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097232351753473281821767 10645848527630209922732651)
          ·
            refine ⟨15968772791445314884098977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10645848527630209922732651 15968772791445314884098977)
            ·
              refine ⟨11976579593583986163074233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15968772791445314884098977 11976579593583986163074233)
              ·
                refine ⟨8982434695187989622305675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11976579593583986163074233 8982434695187989622305675)
                ·
                  refine ⟨13473652042781984433458513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982434695187989622305675 13473652042781984433458513)
                  ·
                    refine ⟨10105239032086488325093885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13473652042781984433458513 10105239032086488325093885)
                    ·
                      refine ⟨3789464637032433121910207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105239032086488325093885 3789464637032433121910207)
                      ·
                        rfl

theorem cell23_7379956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7379956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7379956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7379956 prefixEnd_7379956 := by exact prefixLift 7379956
  have htrace : WordTrace (prefixWord ++ tailWord_7379956) baseStart_7379956 baseEnd_7379956 := by
    simpa [prefixWord, tailWord_7379956, baseEnd_7379956] using wordTrace_append hprefix tailTrace_7379956
  have hstable : (prefixWord ++ tailWord_7379956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7379956).length < 2 ^ (prefixWord ++ tailWord_7379956).sum := by decide
  have hdescent : baseEnd_7379956 < baseStart_7379956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7379956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380028 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_7380028 : Nat := 118140960795 + 7380028 * 2 ^ 59
def prefixEnd_7380028 : Nat := 4983230072969 + 3 ^ 40 * 7380028 * 2
def baseEnd_7380028 : Nat := 1263167202546518946736625

theorem tailTrace_7380028 : CollatzResearch.WordTrace tailWord_7380028 prefixEnd_7380028 1263167202546518946736625 := by
  unfold tailWord_7380028
  simp only [CollatzResearch.WordTrace]
  refine ⟨134585867253713219640634369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179447823004950959520845825 134585867253713219640634369)
  ·
    refine ⟨100939400440284914730475777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134585867253713219640634369 100939400440284914730475777)
    ·
      refine ⟨75704550330213686047856833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100939400440284914730475777 75704550330213686047856833)
      ·
        refine ⟨56778412747660264535892625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75704550330213686047856833 56778412747660264535892625)
        ·
          refine ⟨42583809560745198401919469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56778412747660264535892625 42583809560745198401919469)
          ·
            refine ⟨15968928585279449400719801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42583809560745198401919469 15968928585279449400719801)
            ·
              refine ⟨11976696438959587050539851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15968928585279449400719801 11976696438959587050539851)
              ·
                refine ⟨17965044658439380575809777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976696438959587050539851 17965044658439380575809777)
                ·
                  refine ⟨13473783493829535431857333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17965044658439380575809777 13473783493829535431857333)
                  ·
                    refine ⟨1263167202546518946736625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13473783493829535431857333 1263167202546518946736625)
                    ·
                      rfl

theorem cell23_7380028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_7380028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380028 prefixEnd_7380028 := by exact prefixLift 7380028
  have htrace : WordTrace (prefixWord ++ tailWord_7380028) baseStart_7380028 baseEnd_7380028 := by
    simpa [prefixWord, tailWord_7380028, baseEnd_7380028] using wordTrace_append hprefix tailTrace_7380028
  have hstable : (prefixWord ++ tailWord_7380028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380028).length < 2 ^ (prefixWord ++ tailWord_7380028).sum := by decide
  have hdescent : baseEnd_7380028 < baseStart_7380028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380041 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 7, 4]
def baseStart_7380041 : Nat := 118140960795 + 7380041 * 2 ^ 59
def prefixEnd_7380041 : Nat := 4983230072969 + 3 ^ 40 * 7380041 * 2
def baseEnd_7380041 : Nat := 1263169427629355096449105

theorem tailTrace_7380041 : CollatzResearch.WordTrace tailWord_7380041 prefixEnd_7380041 1263169427629355096449105 := by
  unfold tailWord_7380041
  simp only [CollatzResearch.WordTrace]
  refine ⟨269172208656379342501491977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179448139104252895000994651 269172208656379342501491977)
  ·
    refine ⟨201879156492284506876118983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269172208656379342501491977 201879156492284506876118983)
    ·
      refine ⟨302818734738426760314178475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201879156492284506876118983 302818734738426760314178475)
      ·
        refine ⟨454228102107640140471267713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302818734738426760314178475 454228102107640140471267713)
        ·
          refine ⟨340671076580730105353450785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454228102107640140471267713 340671076580730105353450785)
          ·
            refine ⟨255503307435547579015088089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340671076580730105353450785 255503307435547579015088089)
            ·
              refine ⟨191627480576660684261316067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255503307435547579015088089 191627480576660684261316067)
              ·
                refine ⟨287441220864991026391974101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191627480576660684261316067 287441220864991026391974101)
                ·
                  refine ⟨6736903614023227181061893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 287441220864991026391974101 6736903614023227181061893)
                  ·
                    refine ⟨1263169427629355096449105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736903614023227181061893 1263169427629355096449105)
                    ·
                      rfl

theorem cell23_7380041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_7380041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380041 prefixEnd_7380041 := by exact prefixLift 7380041
  have htrace : WordTrace (prefixWord ++ tailWord_7380041) baseStart_7380041 baseEnd_7380041 := by
    simpa [prefixWord, tailWord_7380041, baseEnd_7380041] using wordTrace_append hprefix tailTrace_7380041
  have hstable : (prefixWord ++ tailWord_7380041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380041).length < 2 ^ (prefixWord ++ tailWord_7380041).sum := by decide
  have hdescent : baseEnd_7380041 < baseStart_7380041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380081 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_7380081 : Nat := 118140960795 + 7380081 * 2 ^ 59
def prefixEnd_7380081 : Nat := 4983230072969 + 3 ^ 40 * 7380081 * 2
def baseEnd_7380081 : Nat := 3789528822114245132847131

theorem tailTrace_7380081 : CollatzResearch.WordTrace tailWord_7380081 prefixEnd_7380081 3789528822114245132847131 := by
  unfold tailWord_7380081
  simp only [CollatzResearch.WordTrace]
  refine ⟨269173667576234429332948097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179449111717489619555298731 269173667576234429332948097)
  ·
    refine ⟨201880250682175821999711073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269173667576234429332948097 201880250682175821999711073)
    ·
      refine ⟨151410188011631866499783305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201880250682175821999711073 151410188011631866499783305)
      ·
        refine ⟨113557641008723899874837479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151410188011631866499783305 113557641008723899874837479)
        ·
          refine ⟨170336461513085849812256219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113557641008723899874837479 170336461513085849812256219)
          ·
            refine ⟨255504692269628774718384329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170336461513085849812256219 255504692269628774718384329)
            ·
              refine ⟨191628519202221581038788247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255504692269628774718384329 191628519202221581038788247)
              ·
                refine ⟨287442778803332371558182371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191628519202221581038788247 287442778803332371558182371)
                ·
                  refine ⟨431164168204998557337273557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287442778803332371558182371 431164168204998557337273557)
                  ·
                    refine ⟨10105410192304653687592349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 431164168204998557337273557 10105410192304653687592349)
                    ·
                      refine ⟨3789528822114245132847131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105410192304653687592349 3789528822114245132847131)
                      ·
                        rfl

theorem cell23_7380081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_7380081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380081 prefixEnd_7380081 := by exact prefixLift 7380081
  have htrace : WordTrace (prefixWord ++ tailWord_7380081) baseStart_7380081 baseEnd_7380081 := by
    simpa [prefixWord, tailWord_7380081, baseEnd_7380081] using wordTrace_append hprefix tailTrace_7380081
  have hstable : (prefixWord ++ tailWord_7380081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380081).length < 2 ^ (prefixWord ++ tailWord_7380081).sum := by decide
  have hdescent : baseEnd_7380081 < baseStart_7380081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380135 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 1, 5]
def baseStart_7380135 : Nat := 118140960795 + 7380135 * 2 ^ 59
def prefixEnd_7380135 : Nat := 4983230072969 + 3 ^ 40 * 7380135 * 2
def baseEnd_7380135 : Nat := 1263185516689862640523961

theorem tailTrace_7380135 : CollatzResearch.WordTrace tailWord_7380135 prefixEnd_7380135 1263185516689862640523961 := by
  unfold tailWord_7380135
  simp only [CollatzResearch.WordTrace]
  refine ⟨269175637118038796555413859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179450424745359197703609239 269175637118038796555413859)
  ·
    refine ⟨403763455677058194833120789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269175637118038796555413859 403763455677058194833120789)
    ·
      refine ⟨18926411984862102882802537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 403763455677058194833120789 18926411984862102882802537)
      ·
        refine ⟨14194808988646577162101903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18926411984862102882802537 14194808988646577162101903)
        ·
          refine ⟨21292213482969865743152855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14194808988646577162101903 21292213482969865743152855)
          ·
            refine ⟨31938320224454798614729283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21292213482969865743152855 31938320224454798614729283)
            ·
              refine ⟨47907480336682197922093925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31938320224454798614729283 47907480336682197922093925)
              ·
                refine ⟨8982652563127912110392611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47907480336682197922093925 8982652563127912110392611)
                ·
                  refine ⟨13473978844691868165588917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982652563127912110392611 13473978844691868165588917)
                  ·
                    refine ⟨1263185516689862640523961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13473978844691868165588917 1263185516689862640523961)
                    ·
                      rfl

theorem cell23_7380135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_7380135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380135 prefixEnd_7380135 := by exact prefixLift 7380135
  have htrace : WordTrace (prefixWord ++ tailWord_7380135) baseStart_7380135 baseEnd_7380135 := by
    simpa [prefixWord, tailWord_7380135, baseEnd_7380135] using wordTrace_append hprefix tailTrace_7380135
  have hstable : (prefixWord ++ tailWord_7380135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380135).length < 2 ^ (prefixWord ++ tailWord_7380135).sum := by decide
  have hdescent : baseEnd_7380135 < baseStart_7380135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380178 : List Nat := [3, 2, 2, 2, 1, 1, 4, 8]
def baseStart_7380178 : Nat := 118140960795 + 7380178 * 2 ^ 59
def prefixEnd_7380178 : Nat := 4983230072969 + 3 ^ 40 * 7380178 * 2
def baseEnd_7380178 : Nat := 140354764064360416790155

theorem tailTrace_7380178 : CollatzResearch.WordTrace tailWord_7380178 prefixEnd_7380178 140354764064360416790155 := by
  unfold tailWord_7380178
  simp only [CollatzResearch.WordTrace]
  refine ⟨67294301364220753724807297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179451470304588676599486125 67294301364220753724807297)
  ·
    refine ⟨50470726023165565293605473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67294301364220753724807297 50470726023165565293605473)
    ·
      refine ⟨37853044517374173970204105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50470726023165565293605473 37853044517374173970204105)
      ·
        refine ⟨28389783388030630477653079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37853044517374173970204105 28389783388030630477653079)
        ·
          refine ⟨42584675082045945716479619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28389783388030630477653079 42584675082045945716479619)
          ·
            refine ⟨63877012623068918574719429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42584675082045945716479619 63877012623068918574719429)
            ·
              refine ⟨11976939866825422232759893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63877012623068918574719429 11976939866825422232759893)
              ·
                refine ⟨140354764064360416790155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11976939866825422232759893 140354764064360416790155)
                ·
                  rfl

theorem cell23_7380178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_7380178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380178 prefixEnd_7380178 := by exact prefixLift 7380178
  have htrace : WordTrace (prefixWord ++ tailWord_7380178) baseStart_7380178 baseEnd_7380178 := by
    simpa [prefixWord, tailWord_7380178, baseEnd_7380178] using wordTrace_append hprefix tailTrace_7380178
  have hstable : (prefixWord ++ tailWord_7380178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380178).length < 2 ^ (prefixWord ++ tailWord_7380178).sum := by decide
  have hdescent : baseEnd_7380178 < baseStart_7380178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380189 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7380189 : Nat := 118140960795 + 7380189 * 2 ^ 59
def prefixEnd_7380189 : Nat := 4983230072969 + 3 ^ 40 * 7380189 * 2
def baseEnd_7380189 : Nat := 3789584278024930710296635

theorem tailTrace_7380189 : CollatzResearch.WordTrace tailWord_7380189 prefixEnd_7380189 3789584278024930710296635 := by
  unfold tailWord_7380189
  simp only [CollatzResearch.WordTrace]
  refine ⟨269177606659843163777879621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179451737773228775851919747 269177606659843163777879621)
  ·
    refine ⟨50470801248720593208352429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269177606659843163777879621 50470801248720593208352429)
    ·
      refine ⟨18926550468270222453132161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50470801248720593208352429 18926550468270222453132161)
      ·
        refine ⟨14194912851202666839849121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18926550468270222453132161 14194912851202666839849121)
        ·
          refine ⟨10646184638402000129886841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14194912851202666839849121 10646184638402000129886841)
          ·
            refine ⟨7984638478801500097415131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10646184638402000129886841 7984638478801500097415131)
            ·
              refine ⟨11976957718202250146122697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984638478801500097415131 11976957718202250146122697)
              ·
                refine ⟨8982718288651687609592023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11976957718202250146122697 8982718288651687609592023)
                ·
                  refine ⟨13474077432977531414388035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982718288651687609592023 13474077432977531414388035)
                  ·
                    refine ⟨20211116149466297121582053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13474077432977531414388035 20211116149466297121582053)
                    ·
                      refine ⟨3789584278024930710296635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20211116149466297121582053 3789584278024930710296635)
                      ·
                        rfl

theorem cell23_7380189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7380189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380189 prefixEnd_7380189 := by exact prefixLift 7380189
  have htrace : WordTrace (prefixWord ++ tailWord_7380189) baseStart_7380189 baseEnd_7380189 := by
    simpa [prefixWord, tailWord_7380189, baseEnd_7380189] using wordTrace_append hprefix tailTrace_7380189
  have hstable : (prefixWord ++ tailWord_7380189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380189).length < 2 ^ (prefixWord ++ tailWord_7380189).sum := by decide
  have hdescent : baseEnd_7380189 < baseStart_7380189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380192 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3]
def baseStart_7380192 : Nat := 118140960795 + 7380192 * 2 ^ 59
def prefixEnd_7380192 : Nat := 4983230072969 + 3 ^ 40 * 7380192 * 2
def baseEnd_7380192 : Nat := 3789585818466894198559121

theorem tailTrace_7380192 : CollatzResearch.WordTrace tailWord_7380192 prefixEnd_7380192 3789585818466894198559121 := by
  unfold tailWord_7380192
  simp only [CollatzResearch.WordTrace]
  refine ⟨134588858039416147645119415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179451810719221530193492553 134588858039416147645119415)
  ·
    refine ⟨201883287059124221467679123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134588858039416147645119415 201883287059124221467679123)
    ·
      refine ⟨302824930588686332201518685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201883287059124221467679123 302824930588686332201518685)
      ·
        refine ⟨113559348970757374575569507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302824930588686332201518685 113559348970757374575569507)
        ·
          refine ⟨170339023456136061863354261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113559348970757374575569507 170339023456136061863354261)
          ·
            refine ⟨7984641724506377899844731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170339023456136061863354261 7984641724506377899844731)
            ·
              refine ⟨11976962586759566849767097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984641724506377899844731 11976962586759566849767097)
              ·
                refine ⟨8982721940069675137325323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11976962586759566849767097 8982721940069675137325323)
                ·
                  refine ⟨13474082910104512705987985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982721940069675137325323 13474082910104512705987985)
                  ·
                    refine ⟨10105562182578384529490989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13474082910104512705987985 10105562182578384529490989)
                    ·
                      refine ⟨3789585818466894198559121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105562182578384529490989 3789585818466894198559121)
                      ·
                        rfl

theorem cell23_7380192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_7380192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380192 prefixEnd_7380192 := by exact prefixLift 7380192
  have htrace : WordTrace (prefixWord ++ tailWord_7380192) baseStart_7380192 baseEnd_7380192 := by
    simpa [prefixWord, tailWord_7380192, baseEnd_7380192] using wordTrace_append hprefix tailTrace_7380192
  have hstable : (prefixWord ++ tailWord_7380192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380192).length < 2 ^ (prefixWord ++ tailWord_7380192).sum := by decide
  have hdescent : baseEnd_7380192 < baseStart_7380192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380205 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7380205 : Nat := 118140960795 + 7380205 * 2 ^ 59
def prefixEnd_7380205 : Nat := 4983230072969 + 3 ^ 40 * 7380205 * 2
def baseEnd_7380205 : Nat := 3789592493715402647696561

theorem tailTrace_7380205 : CollatzResearch.WordTrace tailWord_7380205 prefixEnd_7380205 3789592493715402647696561 := by
  unfold tailWord_7380205
  simp only [CollatzResearch.WordTrace]
  refine ⟨269178190227785198510462069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179452126818523465673641379 269178190227785198510462069)
  ·
    refine ⟨25235455333854862360355819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269178190227785198510462069 25235455333854862360355819)
    ·
      refine ⟨37853183000782293540533729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25235455333854862360355819 37853183000782293540533729)
      ·
        refine ⟨28389887250586720155400297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37853183000782293540533729 28389887250586720155400297)
        ·
          refine ⟨21292415437940040116550223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28389887250586720155400297 21292415437940040116550223)
          ·
            refine ⟨31938623156910060174825335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21292415437940040116550223 31938623156910060174825335)
            ·
              refine ⟨47907934735365090262238003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31938623156910060174825335 47907934735365090262238003)
              ·
                refine ⟨71861902103047635393357005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47907934735365090262238003 71861902103047635393357005)
                ·
                  refine ⟨26948213288642863272508877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71861902103047635393357005 26948213288642863272508877)
                  ·
                    refine ⟨10105579983241073727190829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26948213288642863272508877 10105579983241073727190829)
                    ·
                      refine ⟨3789592493715402647696561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105579983241073727190829 3789592493715402647696561)
                      ·
                        rfl

theorem cell23_7380205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7380205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380205 prefixEnd_7380205 := by exact prefixLift 7380205
  have htrace : WordTrace (prefixWord ++ tailWord_7380205) baseStart_7380205 baseEnd_7380205 := by
    simpa [prefixWord, tailWord_7380205, baseEnd_7380205] using wordTrace_append hprefix tailTrace_7380205
  have hstable : (prefixWord ++ tailWord_7380205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380205).length < 2 ^ (prefixWord ++ tailWord_7380205).sum := by decide
  have hdescent : baseEnd_7380205 < baseStart_7380205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380212 : List Nat := [2, 6, 1, 2, 1, 11]
def baseStart_7380212 : Nat := 118140960795 + 7380212 * 2 ^ 59
def prefixEnd_7380212 : Nat := 4983230072969 + 3 ^ 40 * 7380212 * 2
def baseEnd_7380212 : Nat := 15595045629958782388103

theorem tailTrace_7380212 : CollatzResearch.WordTrace tailWord_7380212 prefixEnd_7380212 15595045629958782388103 := by
  unfold tailWord_7380212
  simp only [CollatzResearch.WordTrace]
  refine ⟨134589222769379919352983445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179452297025839892470644593 134589222769379919352983445)
  ·
    refine ⟨6308869817314683719671099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134589222769379919352983445 6308869817314683719671099)
    ·
      refine ⟨9463304725972025579506649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308869817314683719671099 9463304725972025579506649)
      ·
        refine ⟨7097478544479019184629987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9463304725972025579506649 7097478544479019184629987)
        ·
          refine ⟨10646217816718528776944981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097478544479019184629987 10646217816718528776944981)
          ·
            refine ⟨15595045629958782388103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10646217816718528776944981 15595045629958782388103)
            ·
              rfl

theorem cell23_7380212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 11].length) (baseStart_7380212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380212 prefixEnd_7380212 := by exact prefixLift 7380212
  have htrace : WordTrace (prefixWord ++ tailWord_7380212) baseStart_7380212 baseEnd_7380212 := by
    simpa [prefixWord, tailWord_7380212, baseEnd_7380212] using wordTrace_append hprefix tailTrace_7380212
  have hstable : (prefixWord ++ tailWord_7380212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380212).length < 2 ^ (prefixWord ++ tailWord_7380212).sum := by decide
  have hdescent : baseEnd_7380212 < baseStart_7380212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380238 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7380238 : Nat := 118140960795 + 7380238 * 2 ^ 59
def prefixEnd_7380238 : Nat := 4983230072969 + 3 ^ 40 * 7380238 * 2
def baseEnd_7380238 : Nat := 1263203146192333672861303

theorem tailTrace_7380238 : CollatzResearch.WordTrace tailWord_7380238 prefixEnd_7380238 1263203146192333672861303 := by
  unfold tailWord_7380238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647424229583205643301671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179452929224443763430942245 33647424229583205643301671)
  ·
    refine ⟨50471136344374808464952507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33647424229583205643301671 50471136344374808464952507)
    ·
      refine ⟨75706704516562212697428761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50471136344374808464952507 75706704516562212697428761)
      ·
        refine ⟨56780028387421659523071571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75706704516562212697428761 56780028387421659523071571)
        ·
          refine ⟨85170042581132489284607357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56780028387421659523071571 85170042581132489284607357)
          ·
            refine ⟨31938765967924683481727759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85170042581132489284607357 31938765967924683481727759)
            ·
              refine ⟨47908148951887025222591639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31938765967924683481727759 47908148951887025222591639)
              ·
                refine ⟨71862223427830537833887459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47908148951887025222591639 71862223427830537833887459)
                ·
                  refine ⟨107793335141745806750831189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71862223427830537833887459 107793335141745806750831189)
                  ·
                    refine ⟨1263203146192333672861303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107793335141745806750831189 1263203146192333672861303)
                    ·
                      rfl

theorem cell23_7380238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7380238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380238 prefixEnd_7380238 := by exact prefixLift 7380238
  have htrace : WordTrace (prefixWord ++ tailWord_7380238) baseStart_7380238 baseEnd_7380238 := by
    simpa [prefixWord, tailWord_7380238, baseEnd_7380238] using wordTrace_append hprefix tailTrace_7380238
  have hstable : (prefixWord ++ tailWord_7380238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380238).length < 2 ^ (prefixWord ++ tailWord_7380238).sum := by decide
  have hdescent : baseEnd_7380238 < baseStart_7380238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380266 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7380266 : Nat := 118140960795 + 7380266 * 2 ^ 59
def prefixEnd_7380266 : Nat := 4983230072969 + 3 ^ 40 * 7380266 * 2
def baseEnd_7380266 : Nat := 3789623816035326909033781

theorem tailTrace_7380266 : CollatzResearch.WordTrace tailWord_7380266 prefixEnd_7380266 3789623816035326909033781 := by
  unfold tailWord_7380266
  simp only [CollatzResearch.WordTrace]
  refine ⟨67295103770141051482108163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179453610053709470618955101 67295103770141051482108163)
  ·
    refine ⟨100942655655211577223162245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67295103770141051482108163 100942655655211577223162245)
    ·
      refine ⟨18926747935352170729342921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100942655655211577223162245 18926747935352170729342921)
      ·
        refine ⟨14195060951514128047007191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18926747935352170729342921 14195060951514128047007191)
        ·
          refine ⟨21292591427271192070510787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195060951514128047007191 21292591427271192070510787)
          ·
            refine ⟨31938887140906788105766181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21292591427271192070510787 31938887140906788105766181)
            ·
              refine ⟨5988541338920022769831159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31938887140906788105766181 5988541338920022769831159)
              ·
                refine ⟨8982812008380034154746739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988541338920022769831159 8982812008380034154746739)
                ·
                  refine ⟨13474218012570051232120109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982812008380034154746739 13474218012570051232120109)
                  ·
                    refine ⟨5052831754713769212045041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13474218012570051232120109 5052831754713769212045041)
                    ·
                      refine ⟨3789623816035326909033781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5052831754713769212045041 3789623816035326909033781)
                      ·
                        rfl

theorem cell23_7380266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7380266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380266 prefixEnd_7380266 := by exact prefixLift 7380266
  have htrace : WordTrace (prefixWord ++ tailWord_7380266) baseStart_7380266 baseEnd_7380266 := by
    simpa [prefixWord, tailWord_7380266, baseEnd_7380266] using wordTrace_append hprefix tailTrace_7380266
  have hstable : (prefixWord ++ tailWord_7380266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380266).length < 2 ^ (prefixWord ++ tailWord_7380266).sum := by decide
  have hdescent : baseEnd_7380266 < baseStart_7380266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380292 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7380292 : Nat := 118140960795 + 7380292 * 2 ^ 59
def prefixEnd_7380292 : Nat := 4983230072969 + 3 ^ 40 * 7380292 * 2
def baseEnd_7380292 : Nat := 3789637166532343807308661

theorem tailTrace_7380292 : CollatzResearch.WordTrace tailWord_7380292 prefixEnd_7380292 3789637166532343807308661 := by
  unfold tailWord_7380292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134590681689235006184439565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179454242252313341579252753 134590681689235006184439565)
  ·
    refine ⟨50471505633463127319164837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134590681689235006184439565 50471505633463127319164837)
    ·
      refine ⟨9463407306274336372343407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50471505633463127319164837 9463407306274336372343407)
      ·
        refine ⟨14195110959411504558515111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463407306274336372343407 14195110959411504558515111)
        ·
          refine ⟨21292666439117256837772667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195110959411504558515111 21292666439117256837772667)
          ·
            refine ⟨31938999658675885256659001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21292666439117256837772667 31938999658675885256659001)
            ·
              refine ⟨23954249744006913942494251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31938999658675885256659001 23954249744006913942494251)
              ·
                refine ⟨35931374616010370913741377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23954249744006913942494251 35931374616010370913741377)
                ·
                  refine ⟨26948530962007778185306033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35931374616010370913741377 26948530962007778185306033)
                  ·
                    refine ⟨20211398221505833638979525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26948530962007778185306033 20211398221505833638979525)
                    ·
                      refine ⟨3789637166532343807308661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20211398221505833638979525 3789637166532343807308661)
                      ·
                        rfl

theorem cell23_7380292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7380292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380292 prefixEnd_7380292 := by exact prefixLift 7380292
  have htrace : WordTrace (prefixWord ++ tailWord_7380292) baseStart_7380292 baseEnd_7380292 := by
    simpa [prefixWord, tailWord_7380292, baseEnd_7380292] using wordTrace_append hprefix tailTrace_7380292
  have hstable : (prefixWord ++ tailWord_7380292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380292).length < 2 ^ (prefixWord ++ tailWord_7380292).sum := by decide
  have hdescent : baseEnd_7380292 < baseStart_7380292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380295 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_7380295 : Nat := 118140960795 + 7380295 * 2 ^ 59
def prefixEnd_7380295 : Nat := 4983230072969 + 3 ^ 40 * 7380295 * 2
def baseEnd_7380295 : Nat := 3789638706974307295571147

theorem tailTrace_7380295 : CollatzResearch.WordTrace tailWord_7380295 prefixEnd_7380295 3789638706974307295571147 := by
  unfold tailWord_7380295
  simp only [CollatzResearch.WordTrace]
  refine ⟨269181472797459143881238339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179454315198306095920825559 269181472797459143881238339)
  ·
    refine ⟨403772209196188715821857509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269181472797459143881238339 403772209196188715821857509)
    ·
      refine ⟨75707289224285384216598283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403772209196188715821857509 75707289224285384216598283)
      ·
        refine ⟨113560933836428076324897425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75707289224285384216598283 113560933836428076324897425)
        ·
          refine ⟨85170700377321057243673069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113560933836428076324897425 85170700377321057243673069)
          ·
            refine ⟨31939012641495396466377401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85170700377321057243673069 31939012641495396466377401)
            ·
              refine ⟨23954259481121547349783051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31939012641495396466377401 23954259481121547349783051)
              ·
                refine ⟨35931389221682321024674577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23954259481121547349783051 35931389221682321024674577)
                ·
                  refine ⟨26948541916261740768505933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35931389221682321024674577 26948541916261740768505933)
                  ·
                    refine ⟨10105703218598152788189725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26948541916261740768505933 10105703218598152788189725)
                    ·
                      refine ⟨3789638706974307295571147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105703218598152788189725 3789638706974307295571147)
                      ·
                        rfl

theorem cell23_7380295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_7380295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380295 prefixEnd_7380295 := by exact prefixLift 7380295
  have htrace : WordTrace (prefixWord ++ tailWord_7380295) baseStart_7380295 baseEnd_7380295 := by
    simpa [prefixWord, tailWord_7380295, baseEnd_7380295] using wordTrace_append hprefix tailTrace_7380295
  have hstable : (prefixWord ++ tailWord_7380295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380295).length < 2 ^ (prefixWord ++ tailWord_7380295).sum := by decide
  have hdescent : baseEnd_7380295 < baseStart_7380295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380335 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_7380335 : Nat := 118140960795 + 7380335 * 2 ^ 59
def prefixEnd_7380335 : Nat := 4983230072969 + 3 ^ 40 * 7380335 * 2
def baseEnd_7380335 : Nat := 3789659246200487139070963

theorem tailTrace_7380335 : CollatzResearch.WordTrace tailWord_7380335 prefixEnd_7380335 3789659246200487139070963 := by
  unfold tailWord_7380335
  simp only [CollatzResearch.WordTrace]
  refine ⟨269182931717314230712694459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179455287811542820475129639 269182931717314230712694459)
  ·
    refine ⟨403774397575971346069041689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269182931717314230712694459 403774397575971346069041689)
    ·
      refine ⟨302830798181978509551781267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403774397575971346069041689 302830798181978509551781267)
      ·
        refine ⟨454246197272967764327671901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302830798181978509551781267 454246197272967764327671901)
        ·
          refine ⟨170342323977362911622876963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454246197272967764327671901 170342323977362911622876963)
          ·
            refine ⟨255513485966044367434315445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170342323977362911622876963 255513485966044367434315445)
            ·
              refine ⟨23954389309316659446967073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255513485966044367434315445 23954389309316659446967073)
              ·
                refine ⟨17965791981987494585225305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23954389309316659446967073 17965791981987494585225305)
                ·
                  refine ⟨13474343986490620938918979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17965791981987494585225305 13474343986490620938918979)
                  ·
                    refine ⟨20211515979735931408378469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13474343986490620938918979 20211515979735931408378469)
                    ·
                      refine ⟨3789659246200487139070963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20211515979735931408378469 3789659246200487139070963)
                      ·
                        rfl

theorem cell23_7380335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_7380335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380335 prefixEnd_7380335 := by exact prefixLift 7380335
  have htrace : WordTrace (prefixWord ++ tailWord_7380335) baseStart_7380335 baseEnd_7380335 := by
    simpa [prefixWord, tailWord_7380335, baseEnd_7380335] using wordTrace_append hprefix tailTrace_7380335
  have hstable : (prefixWord ++ tailWord_7380335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380335).length < 2 ^ (prefixWord ++ tailWord_7380335).sum := by decide
  have hdescent : baseEnd_7380335 < baseStart_7380335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380462 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7380462 : Nat := 118140960795 + 7380462 * 2 ^ 59
def prefixEnd_7380462 : Nat := 4983230072969 + 3 ^ 40 * 7380462 * 2
def baseEnd_7380462 : Nat := 3789724458243608142182879

theorem tailTrace_7380462 : CollatzResearch.WordTrace tailWord_7380462 prefixEnd_7380462 3789724458243608142182879 := by
  unfold tailWord_7380462
  simp only [CollatzResearch.WordTrace]
  refine ⟨33648445473481766425320955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179458375858569420935045093 33648445473481766425320955)
  ·
    refine ⟨50472668210222649637981433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33648445473481766425320955 50472668210222649637981433)
    ·
      refine ⟨37854501157666987228486075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50472668210222649637981433 37854501157666987228486075)
      ·
        refine ⟨56781751736500480842729113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37854501157666987228486075 56781751736500480842729113)
        ·
          refine ⟨42586313802375360632046835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56781751736500480842729113 42586313802375360632046835)
          ·
            refine ⟨63879470703563040948070253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42586313802375360632046835 63879470703563040948070253)
            ·
              refine ⟨23954801513836140355526345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63879470703563040948070253 23954801513836140355526345)
              ·
                refine ⟨17966101135377105266644759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23954801513836140355526345 17966101135377105266644759)
                ·
                  refine ⟨26949151703065657899967139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966101135377105266644759 26949151703065657899967139)
                  ·
                    refine ⟨40423727554598486849950709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26949151703065657899967139 40423727554598486849950709)
                    ·
                      refine ⟨3789724458243608142182879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40423727554598486849950709 3789724458243608142182879)
                      ·
                        rfl

theorem cell23_7380462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7380462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380462 prefixEnd_7380462 := by exact prefixLift 7380462
  have htrace : WordTrace (prefixWord ++ tailWord_7380462) baseStart_7380462 baseEnd_7380462 := by
    simpa [prefixWord, tailWord_7380462, baseEnd_7380462] using wordTrace_append hprefix tailTrace_7380462
  have hstable : (prefixWord ++ tailWord_7380462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380462).length < 2 ^ (prefixWord ++ tailWord_7380462).sum := by decide
  have hdescent : baseEnd_7380462 < baseStart_7380462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380469 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7380469 : Nat := 118140960795 + 7380469 * 2 ^ 59
def prefixEnd_7380469 : Nat := 4983230072969 + 3 ^ 40 * 7380469 * 2
def baseEnd_7380469 : Nat := 1263242684202729871598449

theorem tailTrace_7380469 : CollatzResearch.WordTrace tailWord_7380469 prefixEnd_7380469 1263242684202729871598449 := by
  unfold tailWord_7380469
  simp only [CollatzResearch.WordTrace]
  refine ⟨269187819098828771598072461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179458546065885847732048307 269187819098828771598072461)
  ·
    refine ⟨100945432162060789349277173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269187819098828771598072461 100945432162060789349277173)
    ·
      refine ⟨9463634265193199001494735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100945432162060789349277173 9463634265193199001494735)
      ·
        refine ⟨14195451397789798502242103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463634265193199001494735 14195451397789798502242103)
        ·
          refine ⟨21293177096684697753363155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195451397789798502242103 21293177096684697753363155)
          ·
            refine ⟨31939765645027046630044733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21293177096684697753363155 31939765645027046630044733)
            ·
              refine ⟨11977412116885142486266775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31939765645027046630044733 11977412116885142486266775)
              ·
                refine ⟨17966118175327713729400163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977412116885142486266775 17966118175327713729400163)
                ·
                  refine ⟨26949177262991570594100245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966118175327713729400163 26949177262991570594100245)
                  ·
                    refine ⟨1263242684202729871598449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26949177262991570594100245 1263242684202729871598449)
                    ·
                      rfl

theorem cell23_7380469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7380469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380469 prefixEnd_7380469 := by exact prefixLift 7380469
  have htrace : WordTrace (prefixWord ++ tailWord_7380469) baseStart_7380469 baseEnd_7380469 := by
    simpa [prefixWord, tailWord_7380469, baseEnd_7380469] using wordTrace_append hprefix tailTrace_7380469
  have hstable : (prefixWord ++ tailWord_7380469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380469).length < 2 ^ (prefixWord ++ tailWord_7380469).sum := by decide
  have hdescent : baseEnd_7380469 < baseStart_7380469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380472 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_7380472 : Nat := 118140960795 + 7380472 * 2 ^ 59
def prefixEnd_7380472 : Nat := 4983230072969 + 3 ^ 40 * 7380472 * 2
def baseEnd_7380472 : Nat := 3789729593050153103057833

theorem tailTrace_7380472 : CollatzResearch.WordTrace tailWord_7380472 prefixEnd_7380472 3789729593050153103057833 := by
  unfold tailWord_7380472
  simp only [CollatzResearch.WordTrace]
  refine ⟨134593964258908951555215835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179458619011878602073621113 134593964258908951555215835)
  ·
    refine ⟨201890946388363427332823753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134593964258908951555215835 201890946388363427332823753)
    ·
      refine ⟨151418209791272570499617815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201890946388363427332823753 151418209791272570499617815)
      ·
        refine ⟨227127314686908855749426723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151418209791272570499617815 227127314686908855749426723)
        ·
          refine ⟨340690972030363283624140085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227127314686908855749426723 340690972030363283624140085)
          ·
            refine ⟨31939778627846557839763133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 340690972030363283624140085 31939778627846557839763133)
            ·
              refine ⟨11977416985442459189911175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31939778627846557839763133 11977416985442459189911175)
              ·
                refine ⟨17966125478163688784866763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977416985442459189911175 17966125478163688784866763)
                ·
                  refine ⟨26949188217245533177300145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966125478163688784866763 26949188217245533177300145)
                  ·
                    refine ⟨20211891162934149882975109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26949188217245533177300145 20211891162934149882975109)
                    ·
                      refine ⟨3789729593050153103057833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20211891162934149882975109 3789729593050153103057833)
                      ·
                        rfl

theorem cell23_7380472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_7380472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380472 prefixEnd_7380472 := by exact prefixLift 7380472
  have htrace : WordTrace (prefixWord ++ tailWord_7380472) baseStart_7380472 baseEnd_7380472 := by
    simpa [prefixWord, tailWord_7380472, baseEnd_7380472] using wordTrace_append hprefix tailTrace_7380472
  have hstable : (prefixWord ++ tailWord_7380472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380472).length < 2 ^ (prefixWord ++ tailWord_7380472).sum := by decide
  have hdescent : baseEnd_7380472 < baseStart_7380472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380509 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_7380509 : Nat := 118140960795 + 7380509 * 2 ^ 59
def prefixEnd_7380509 : Nat := 4983230072969 + 3 ^ 40 * 7380509 * 2
def baseEnd_7380509 : Nat := 3789748591834369458295163

theorem tailTrace_7380509 : CollatzResearch.WordTrace tailWord_7380509 prefixEnd_7380509 3789748591834369458295163 := by
  unfold tailWord_7380509
  simp only [CollatzResearch.WordTrace]
  refine ⟨269189278018683858429528581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179459518679122572286352387 269189278018683858429528581)
  ·
    refine ⟨50472989628503223455536609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269189278018683858429528581 50472989628503223455536609)
    ·
      refine ⟨37854742221377417591652457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50472989628503223455536609 37854742221377417591652457)
      ·
        refine ⟨28391056666033063193739343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37854742221377417591652457 28391056666033063193739343)
        ·
          refine ⟨42586584999049594790609015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28391056666033063193739343 42586584999049594790609015)
          ·
            refine ⟨63879877498574392185913523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42586584999049594790609015 63879877498574392185913523)
            ·
              refine ⟨95819816247861588278870285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63879877498574392185913523 95819816247861588278870285)
              ·
                refine ⟨35932431092948095604576357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95819816247861588278870285 35932431092948095604576357)
                ·
                  refine ⟨6737330829927767925858067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35932431092948095604576357 6737330829927767925858067)
                  ·
                    refine ⟨10105996244891651888787101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6737330829927767925858067 10105996244891651888787101)
                    ·
                      refine ⟨3789748591834369458295163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10105996244891651888787101 3789748591834369458295163)
                      ·
                        rfl

theorem cell23_7380509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_7380509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380509 prefixEnd_7380509 := by exact prefixLift 7380509
  have htrace : WordTrace (prefixWord ++ tailWord_7380509) baseStart_7380509 baseEnd_7380509 := by
    simpa [prefixWord, tailWord_7380509, baseEnd_7380509] using wordTrace_append hprefix tailTrace_7380509
  have hstable : (prefixWord ++ tailWord_7380509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380509).length < 2 ^ (prefixWord ++ tailWord_7380509).sum := by decide
  have hdescent : baseEnd_7380509 < baseStart_7380509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380520 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 2, 4]
def baseStart_7380520 : Nat := 118140960795 + 7380520 * 2 ^ 59
def prefixEnd_7380520 : Nat := 4983230072969 + 3 ^ 40 * 7380520 * 2
def baseEnd_7380520 : Nat := 1263251413373856305085871

theorem tailTrace_7380520 : CollatzResearch.WordTrace tailWord_7380520 prefixEnd_7380520 1263251413373856305085871 := by
  unfold tailWord_7380520
  simp only [CollatzResearch.WordTrace]
  refine ⟨134594839610822003654089507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179459786147762671538786009 134594839610822003654089507)
  ·
    refine ⟨201892259416233005481134261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134594839610822003654089507 201892259416233005481134261)
    ·
      refine ⟨18927399320271844263856337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201892259416233005481134261 18927399320271844263856337)
      ·
        refine ⟨14195549490203883197892253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18927399320271844263856337 14195549490203883197892253)
        ·
          refine ⟨5323331058826456199209595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14195549490203883197892253 5323331058826456199209595)
          ·
            refine ⟨7984996588239684298814393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323331058826456199209595 7984996588239684298814393)
            ·
              refine ⟨5988747441179763224110795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984996588239684298814393 5988747441179763224110795)
              ·
                refine ⟨8983121161769644836166193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988747441179763224110795 8983121161769644836166193)
                ·
                  refine ⟨6737340871327233627124645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8983121161769644836166193 6737340871327233627124645)
                  ·
                    refine ⟨1263251413373856305085871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737340871327233627124645 1263251413373856305085871)
                    ·
                      rfl

theorem cell23_7380520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_7380520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380520 prefixEnd_7380520 := by exact prefixLift 7380520
  have htrace : WordTrace (prefixWord ++ tailWord_7380520) baseStart_7380520 baseEnd_7380520 := by
    simpa [prefixWord, tailWord_7380520, baseEnd_7380520] using wordTrace_append hprefix tailTrace_7380520
  have hstable : (prefixWord ++ tailWord_7380520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380520).length < 2 ^ (prefixWord ++ tailWord_7380520).sum := by decide
  have hdescent : baseEnd_7380520 < baseStart_7380520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380536 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 1, 3, 2]
def baseStart_7380536 : Nat := 118140960795 + 7380536 * 2 ^ 59
def prefixEnd_7380536 : Nat := 4983230072969 + 3 ^ 40 * 7380536 * 2
def baseEnd_7380536 : Nat := 3789762455812040852657539

theorem tailTrace_7380536 : CollatzResearch.WordTrace tailWord_7380536 prefixEnd_7380536 3789762455812040852657539 := by
  unfold tailWord_7380536
  simp only [CollatzResearch.WordTrace]
  refine ⟨134595131394793021020380731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179460175193057361360507641 134595131394793021020380731)
  ·
    refine ⟨201892697092189531530571097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134595131394793021020380731 201892697092189531530571097)
    ·
      refine ⟨151419522819142148647928323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201892697092189531530571097 151419522819142148647928323)
      ·
        refine ⟨227129284228713222971892485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151419522819142148647928323 227129284228713222971892485)
        ·
          refine ⟨42586740792883729307229841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227129284228713222971892485 42586740792883729307229841)
          ·
            refine ⟨31940055594662796980422381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42586740792883729307229841 31940055594662796980422381)
            ·
              refine ⟨11977520847998548867658393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31940055594662796980422381 11977520847998548867658393)
              ·
                refine ⟨8983140635998911650743795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11977520847998548867658393 8983140635998911650743795)
                ·
                  refine ⟨13474710953998367476115693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8983140635998911650743795 13474710953998367476115693)
                  ·
                    refine ⟨5053016607749387803543385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13474710953998367476115693 5053016607749387803543385)
                    ·
                      refine ⟨3789762455812040852657539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053016607749387803543385 3789762455812040852657539)
                      ·
                        rfl

theorem cell23_7380536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_7380536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380536 prefixEnd_7380536 := by exact prefixLift 7380536
  have htrace : WordTrace (prefixWord ++ tailWord_7380536) baseStart_7380536 baseEnd_7380536 := by
    simpa [prefixWord, tailWord_7380536, baseEnd_7380536] using wordTrace_append hprefix tailTrace_7380536
  have hstable : (prefixWord ++ tailWord_7380536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380536).length < 2 ^ (prefixWord ++ tailWord_7380536).sum := by decide
  have hdescent : baseEnd_7380536 < baseStart_7380536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380549 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 1, 4, 2]
def baseStart_7380549 : Nat := 118140960795 + 7380549 * 2 ^ 59
def prefixEnd_7380549 : Nat := 4983230072969 + 3 ^ 40 * 7380549 * 2
def baseEnd_7380549 : Nat := 3789769131060549301794979

theorem tailTrace_7380549 : CollatzResearch.WordTrace tailWord_7380549 prefixEnd_7380549 3789769131060549301794979 := by
  unfold tailWord_7380549
  simp only [CollatzResearch.WordTrace]
  refine ⟨269190736938538945260984701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179460491292359296840656467 269190736938538945260984701)
  ·
    refine ⟨100946526351952104472869263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269190736938538945260984701 100946526351952104472869263)
    ·
      refine ⟨151419789527928156709303895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100946526351952104472869263 151419789527928156709303895)
      ·
        refine ⟨227129684291892235063955843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151419789527928156709303895 227129684291892235063955843)
        ·
          refine ⟨340694526437838352595933765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227129684291892235063955843 340694526437838352595933765)
          ·
            refine ⟨63880223707094691111737581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340694526437838352595933765 63880223707094691111737581)
            ·
              refine ⟨23955083890160509166901593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63880223707094691111737581 23955083890160509166901593)
              ·
                refine ⟨17966312917620381875176195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23955083890160509166901593 17966312917620381875176195)
                ·
                  refine ⟨26949469376430572812764293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966312917620381875176195 26949469376430572812764293)
                  ·
                    refine ⟨5053025508080732402393305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26949469376430572812764293 5053025508080732402393305)
                    ·
                      refine ⟨3789769131060549301794979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053025508080732402393305 3789769131060549301794979)
                      ·
                        rfl

theorem cell23_7380549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_7380549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380549 prefixEnd_7380549 := by exact prefixLift 7380549
  have htrace : WordTrace (prefixWord ++ tailWord_7380549) baseStart_7380549 baseEnd_7380549 := by
    simpa [prefixWord, tailWord_7380549, baseEnd_7380549] using wordTrace_append hprefix tailTrace_7380549
  have hstable : (prefixWord ++ tailWord_7380549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380549).length < 2 ^ (prefixWord ++ tailWord_7380549).sum := by decide
  have hdescent : baseEnd_7380549 < baseStart_7380549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
