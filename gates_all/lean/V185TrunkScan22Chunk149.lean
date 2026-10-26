import V185TrunkScan22Chunk148

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1331311 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 1, 3]
def baseStart_1331311 : Nat := 118140960795 + 1331311 * 2 ^ 59
def prefixEnd_1331311 : Nat := 4983230072969 + 3 ^ 40 * 1331311 * 2
def baseEnd_1331311 : Nat := 455734962411963982193279

theorem tailTrace_1331311 : CollatzResearch.WordTrace tailWord_1331311 prefixEnd_1331311 455734962411963982193279 := by
  unfold tailWord_1331311
  simp only [CollatzResearch.WordTrace]
  refine ⟨48556901279895091662073787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32371267519930061108049191 48556901279895091662073787)
  ·
    refine ⟨72835351919842637493110681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48556901279895091662073787 72835351919842637493110681)
    ·
      refine ⟨54626513939881978119833011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72835351919842637493110681 54626513939881978119833011)
      ·
        refine ⟨81939770909822967179749517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54626513939881978119833011 81939770909822967179749517)
        ·
          refine ⟨30727414091183612692406069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81939770909822967179749517 30727414091183612692406069)
          ·
            refine ⟨2880695071048463689913069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30727414091183612692406069 2880695071048463689913069)
            ·
              refine ⟨1080260651643173883717401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2880695071048463689913069 1080260651643173883717401)
              ·
                refine ⟨810195488732380412788051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080260651643173883717401 810195488732380412788051)
                ·
                  refine ⟨1215293233098570619182077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810195488732380412788051 1215293233098570619182077)
                  ·
                    refine ⟨455734962411963982193279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215293233098570619182077 455734962411963982193279)
                    ·
                      rfl

theorem cell22_1331311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_1331311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331311 prefixEnd_1331311 := by exact prefixLift 1331311
  have htrace : WordTrace (prefixWord ++ tailWord_1331311) baseStart_1331311 baseEnd_1331311 := by
    simpa [prefixWord, tailWord_1331311, baseEnd_1331311] using wordTrace_append hprefix tailTrace_1331311
  have hstable : (prefixWord ++ tailWord_1331311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331311).length < 2 ^ (prefixWord ++ tailWord_1331311).sum := by decide
  have hdescent : baseEnd_1331311 < baseStart_1331311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331320 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1331320 : Nat := 118140960795 + 1331320 * 2 ^ 59
def prefixEnd_1331320 : Nat := 4983230072969 + 3 ^ 40 * 1331320 * 2
def baseEnd_1331320 : Nat := 455738043295890958718251

theorem tailTrace_1331320 : CollatzResearch.WordTrace tailWord_1331320 prefixEnd_1331320 455738043295890958718251 := by
  unfold tailWord_1331320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24278614768431243099575707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32371486357908324132767609 24278614768431243099575707)
  ·
    refine ⟨36417922152646864649363561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24278614768431243099575707 36417922152646864649363561)
    ·
      refine ⟨27313441614485148487022671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36417922152646864649363561 27313441614485148487022671)
      ·
        refine ⟨40970162421727722730534007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27313441614485148487022671 40970162421727722730534007)
        ·
          refine ⟨61455243632591584095801011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40970162421727722730534007 61455243632591584095801011)
          ·
            refine ⟨92182865448887376143701517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61455243632591584095801011 92182865448887376143701517)
            ·
              refine ⟨34568574543332766053888069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92182865448887376143701517 34568574543332766053888069)
              ·
                refine ⟨6481607726874893635104013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34568574543332766053888069 6481607726874893635104013)
                ·
                  refine ⟨2430602897578085113164005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6481607726874893635104013 2430602897578085113164005)
                  ·
                    refine ⟨455738043295890958718251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2430602897578085113164005 455738043295890958718251)
                    ·
                      rfl

theorem cell22_1331320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1331320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331320 prefixEnd_1331320 := by exact prefixLift 1331320
  have htrace : WordTrace (prefixWord ++ tailWord_1331320) baseStart_1331320 baseEnd_1331320 := by
    simpa [prefixWord, tailWord_1331320, baseEnd_1331320] using wordTrace_append hprefix tailTrace_1331320
  have hstable : (prefixWord ++ tailWord_1331320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331320).length < 2 ^ (prefixWord ++ tailWord_1331320).sum := by decide
  have hdescent : baseEnd_1331320 < baseStart_1331320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331324 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 5]
def baseStart_1331324 : Nat := 118140960795 + 1331324 * 2 ^ 59
def prefixEnd_1331324 : Nat := 4983230072969 + 3 ^ 40 * 1331324 * 2
def baseEnd_1331324 : Nat := 151913137525878760539413

theorem tailTrace_1331324 : CollatzResearch.WordTrace tailWord_1331324 prefixEnd_1331324 151913137525878760539413 := by
  unfold tailWord_1331324
  simp only [CollatzResearch.WordTrace]
  refine ⟨24278687714423997441148513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32371583619231996588198017 24278687714423997441148513)
  ·
    refine ⟨18209015785817998080861385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24278687714423997441148513 18209015785817998080861385)
    ·
      refine ⟨13656761839363498560646039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18209015785817998080861385 13656761839363498560646039)
      ·
        refine ⟨20485142759045247840969059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13656761839363498560646039 20485142759045247840969059)
        ·
          refine ⟨30727714138567871761453589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20485142759045247840969059 30727714138567871761453589)
          ·
            refine ⟨1440361600245368988818137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30727714138567871761453589 1440361600245368988818137)
            ·
              refine ⟨1080271200184026741613603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440361600245368988818137 1080271200184026741613603)
              ·
                refine ⟨1620406800276040112420405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080271200184026741613603 1620406800276040112420405)
                ·
                  refine ⟨151913137525878760539413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1620406800276040112420405 151913137525878760539413)
                  ·
                    rfl

theorem cell22_1331324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_1331324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331324 prefixEnd_1331324 := by exact prefixLift 1331324
  have htrace : WordTrace (prefixWord ++ tailWord_1331324) baseStart_1331324 baseEnd_1331324 := by
    simpa [prefixWord, tailWord_1331324, baseEnd_1331324] using wordTrace_append hprefix tailTrace_1331324
  have hstable : (prefixWord ++ tailWord_1331324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331324).length < 2 ^ (prefixWord ++ tailWord_1331324).sum := by decide
  have hdescent : baseEnd_1331324 < baseStart_1331324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331335 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 6]
def baseStart_1331335 : Nat := 118140960795 + 1331335 * 2 ^ 59
def prefixEnd_1331335 : Nat := 4983230072969 + 3 ^ 40 * 1331335 * 2
def baseEnd_1331335 : Nat := 151914392700811973197735

theorem tailTrace_1331335 : CollatzResearch.WordTrace tailWord_1331335 prefixEnd_1331335 151914392700811973197735 := by
  unfold tailWord_1331335
  simp only [CollatzResearch.WordTrace]
  refine ⟨48557776631808143760947459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32371851087872095840631639 48557776631808143760947459)
  ·
    refine ⟨72836664947712215641421189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48557776631808143760947459 72836664947712215641421189)
    ·
      refine ⟨13656874677696040432766473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72836664947712215641421189 13656874677696040432766473)
      ·
        refine ⟨10242656008272030324574855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13656874677696040432766473 10242656008272030324574855)
        ·
          refine ⟨15363984012408045486862283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10242656008272030324574855 15363984012408045486862283)
          ·
            refine ⟨23045976018612068230293425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15363984012408045486862283 23045976018612068230293425)
            ·
              refine ⟨17284482013959051172720069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23045976018612068230293425 17284482013959051172720069)
              ·
                refine ⟨3240840377617322094885013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17284482013959051172720069 3240840377617322094885013)
                ·
                  refine ⟨151914392700811973197735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3240840377617322094885013 151914392700811973197735)
                  ·
                    rfl

theorem cell22_1331335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 6].length) (baseStart_1331335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331335 prefixEnd_1331335 := by exact prefixLift 1331335
  have htrace : WordTrace (prefixWord ++ tailWord_1331335) baseStart_1331335 baseEnd_1331335 := by
    simpa [prefixWord, tailWord_1331335, baseEnd_1331335] using wordTrace_append hprefix tailTrace_1331335
  have hstable : (prefixWord ++ tailWord_1331335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331335).length < 2 ^ (prefixWord ++ tailWord_1331335).sum := by decide
  have hdescent : baseEnd_1331335 < baseStart_1331335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331414 : List Nat := [5, 2, 1, 2, 1, 2, 9]
def baseStart_1331414 : Nat := 118140960795 + 1331414 * 2 ^ 59
def prefixEnd_1331414 : Nat := 4983230072969 + 3 ^ 40 * 1331414 * 2
def baseEnd_1331414 : Nat := 16880378570996520254369

theorem tailTrace_1331414 : CollatzResearch.WordTrace tailWord_1331414 prefixEnd_1331414 16880378570996520254369 := by
  unfold tailWord_1331414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035041124907621265817081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32373771999014626835382197 3035041124907621265817081)
  ·
    refine ⟨2276280843680715949362811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3035041124907621265817081 2276280843680715949362811)
    ·
      refine ⟨3414421265521073924044217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2276280843680715949362811 3414421265521073924044217)
      ·
        refine ⟨2560815949140805443033163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3414421265521073924044217 2560815949140805443033163)
        ·
          refine ⟨3841223923711208164549745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560815949140805443033163 3841223923711208164549745)
          ·
            refine ⟨2880917942783406123412309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3841223923711208164549745 2880917942783406123412309)
            ·
              refine ⟨16880378570996520254369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2880917942783406123412309 16880378570996520254369)
              ·
                rfl

theorem cell22_1331414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 9].length) (baseStart_1331414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331414 prefixEnd_1331414 := by exact prefixLift 1331414
  have htrace : WordTrace (prefixWord ++ tailWord_1331414) baseStart_1331414 baseEnd_1331414 := by
    simpa [prefixWord, tailWord_1331414, baseEnd_1331414] using wordTrace_append hprefix tailTrace_1331414
  have hstable : (prefixWord ++ tailWord_1331414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331414).length < 2 ^ (prefixWord ++ tailWord_1331414).sum := by decide
  have hdescent : baseEnd_1331414 < baseStart_1331414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331429 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_1331429 : Nat := 118140960795 + 1331429 * 2 ^ 59
def prefixEnd_1331429 : Nat := 4983230072969 + 3 ^ 40 * 1331429 * 2
def baseEnd_1331429 : Nat := 455775356223451007742917

theorem tailTrace_1331429 : CollatzResearch.WordTrace tailWord_1331429 prefixEnd_1331429 455775356223451007742917 := by
  unfold tailWord_1331429
  simp only [CollatzResearch.WordTrace]
  refine ⟨48561205093467597814869341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32374136728978398543246227 48561205093467597814869341)
  ·
    refine ⟨18210451910050349180576003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48561205093467597814869341 18210451910050349180576003)
    ·
      refine ⟨27315677865075523770864005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18210451910050349180576003 27315677865075523770864005)
      ·
        refine ⟨5121689599701660707037001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27315677865075523770864005 5121689599701660707037001)
        ·
          refine ⟨3841267199776245530277751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5121689599701660707037001 3841267199776245530277751)
          ·
            refine ⟨5761900799664368295416627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841267199776245530277751 5761900799664368295416627)
            ·
              refine ⟨8642851199496552443124941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5761900799664368295416627 8642851199496552443124941)
              ·
                refine ⟨3241069199811207166171853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8642851199496552443124941 3241069199811207166171853)
                ·
                  refine ⟨1215400949929202687314445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3241069199811207166171853 1215400949929202687314445)
                  ·
                    refine ⟨455775356223451007742917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215400949929202687314445 455775356223451007742917)
                    ·
                      rfl

theorem cell22_1331429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_1331429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331429 prefixEnd_1331429 := by exact prefixLift 1331429
  have htrace : WordTrace (prefixWord ++ tailWord_1331429) baseStart_1331429 baseEnd_1331429 := by
    simpa [prefixWord, tailWord_1331429, baseEnd_1331429] using wordTrace_append hprefix tailTrace_1331429
  have hstable : (prefixWord ++ tailWord_1331429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331429).length < 2 ^ (prefixWord ++ tailWord_1331429).sum := by decide
  have hdescent : baseEnd_1331429 < baseStart_1331429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331493 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 5]
def baseStart_1331493 : Nat := 118140960795 + 1331493 * 2 ^ 59
def prefixEnd_1331493 : Nat := 4983230072969 + 3 ^ 40 * 1331493 * 2
def baseEnd_1331493 : Nat := 151932421577125391380907

theorem tailTrace_1331493 : CollatzResearch.WordTrace tailWord_1331493 prefixEnd_1331493 151932421577125391380907 := by
  unfold tailWord_1331493
  simp only [CollatzResearch.WordTrace]
  refine ⟨48563539365235736745199133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32375692910157157830132755 48563539365235736745199133)
  ·
    refine ⟨18211327261963401279449675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48563539365235736745199133 18211327261963401279449675)
    ·
      refine ⟨27316990892945101919174513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18211327261963401279449675 27316990892945101919174513)
      ·
        refine ⟨20487743169708826439380885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27316990892945101919174513 20487743169708826439380885)
        ·
          refine ⟨960362961080101239345979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20487743169708826439380885 960362961080101239345979)
          ·
            refine ⟨1440544441620151859018969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960362961080101239345979 1440544441620151859018969)
            ·
              refine ⟨1080408331215113894264227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440544441620151859018969 1080408331215113894264227)
              ·
                refine ⟨1620612496822670841396341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080408331215113894264227 1620612496822670841396341)
                ·
                  refine ⟨151932421577125391380907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1620612496822670841396341 151932421577125391380907)
                  ·
                    rfl

theorem cell22_1331493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_1331493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331493 prefixEnd_1331493 := by exact prefixLift 1331493
  have htrace : WordTrace (prefixWord ++ tailWord_1331493) baseStart_1331493 baseEnd_1331493 := by
    simpa [prefixWord, tailWord_1331493, baseEnd_1331493] using wordTrace_append hprefix tailTrace_1331493
  have hstable : (prefixWord ++ tailWord_1331493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331493).length < 2 ^ (prefixWord ++ tailWord_1331493).sum := by decide
  have hdescent : baseEnd_1331493 < baseStart_1331493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331536 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_1331536 : Nat := 118140960795 + 1331536 * 2 ^ 59
def prefixEnd_1331536 : Nat := 4983230072969 + 3 ^ 40 * 1331536 * 2
def baseEnd_1331536 : Nat := 455811984510138395317589

theorem tailTrace_1331536 : CollatzResearch.WordTrace tailWord_1331536 prefixEnd_1331536 455811984510138395317589 := by
  unfold tailWord_1331536
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282553852039977544507231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32376738469386636726009641 24282553852039977544507231)
  ·
    refine ⟨36423830778059966316760847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24282553852039977544507231 36423830778059966316760847)
    ·
      refine ⟨54635746167089949475141271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36423830778059966316760847 54635746167089949475141271)
      ·
        refine ⟨81953619250634924212711907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54635746167089949475141271 81953619250634924212711907)
        ·
          refine ⟨122930428875952386319067861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81953619250634924212711907 122930428875952386319067861)
          ·
            refine ⟨2881181926780134054353153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 122930428875952386319067861 2881181926780134054353153)
            ·
              refine ⟨2160886445085100540764865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881181926780134054353153 2160886445085100540764865)
              ·
                refine ⟨1620664833813825405573649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160886445085100540764865 1620664833813825405573649)
                ·
                  refine ⟨1215498625360369054180237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1620664833813825405573649 1215498625360369054180237)
                  ·
                    refine ⟨455811984510138395317589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215498625360369054180237 455811984510138395317589)
                    ·
                      rfl

theorem cell22_1331536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_1331536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331536 prefixEnd_1331536 := by exact prefixLift 1331536
  have htrace : WordTrace (prefixWord ++ tailWord_1331536) baseStart_1331536 baseEnd_1331536 := by
    simpa [prefixWord, tailWord_1331536, baseEnd_1331536] using wordTrace_append hprefix tailTrace_1331536
  have hstable : (prefixWord ++ tailWord_1331536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331536).length < 2 ^ (prefixWord ++ tailWord_1331536).sum := by decide
  have hdescent : baseEnd_1331536 < baseStart_1331536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331577 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 7]
def baseStart_1331577 : Nat := 118140960795 + 1331577 * 2 ^ 59
def prefixEnd_1331577 : Nat := 4983230072969 + 3 ^ 40 * 1331577 * 2
def baseEnd_1331577 : Nat := 151942006549342651680821

theorem tailTrace_1331577 : CollatzResearch.WordTrace tailWord_1331577 prefixEnd_1331577 151942006549342651680821 := by
  unfold tailWord_1331577
  simp only [CollatzResearch.WordTrace]
  refine ⟨48566603096931419091256985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32377735397954279394171323 48566603096931419091256985)
  ·
    refine ⟨36424952322698564318442739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48566603096931419091256985 36424952322698564318442739)
    ·
      refine ⟨54637428484047846477664109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36424952322698564318442739 54637428484047846477664109)
      ·
        refine ⟨20489035681517942429124041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54637428484047846477664109 20489035681517942429124041)
        ·
          refine ⟨15366776761138456821843031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20489035681517942429124041 15366776761138456821843031)
          ·
            refine ⟨23050165141707685232764547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15366776761138456821843031 23050165141707685232764547)
            ·
              refine ⟨34575247712561527849146821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23050165141707685232764547 34575247712561527849146821)
              ·
                refine ⟨6482858946105286471715029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34575247712561527849146821 6482858946105286471715029)
                ·
                  refine ⟨151942006549342651680821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6482858946105286471715029 151942006549342651680821)
                  ·
                    rfl

theorem cell22_1331577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_1331577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331577 prefixEnd_1331577 := by exact prefixLift 1331577
  have htrace : WordTrace (prefixWord ++ tailWord_1331577) baseStart_1331577 baseEnd_1331577 := by
    simpa [prefixWord, tailWord_1331577, baseEnd_1331577] using wordTrace_append hprefix tailTrace_1331577
  have hstable : (prefixWord ++ tailWord_1331577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331577).length < 2 ^ (prefixWord ++ tailWord_1331577).sum := by decide
  have hdescent : baseEnd_1331577 < baseStart_1331577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331598 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_1331598 : Nat := 118140960795 + 1331598 * 2 ^ 59
def prefixEnd_1331598 : Nat := 4983230072969 + 3 ^ 40 * 1331598 * 2
def baseEnd_1331598 : Nat := 455833208377190900267399

theorem tailTrace_1331598 : CollatzResearch.WordTrace tailWord_1331598 prefixEnd_1331598 455833208377190900267399 := by
  unfold tailWord_1331598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070921128731917459721431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32378246019903559785180965 6070921128731917459721431)
  ·
    refine ⟨9106381693097876189582147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6070921128731917459721431 9106381693097876189582147)
    ·
      refine ⟨13659572539646814284373221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9106381693097876189582147 13659572539646814284373221)
      ·
        refine ⟨2561169851183777678319979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13659572539646814284373221 2561169851183777678319979)
        ·
          refine ⟨3841754776775666517479969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561169851183777678319979 3841754776775666517479969)
          ·
            refine ⟨2881316082581749888109977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3841754776775666517479969 2881316082581749888109977)
            ·
              refine ⟨2160987061936312416082483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881316082581749888109977 2160987061936312416082483)
              ·
                refine ⟨3241480592904468624123725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160987061936312416082483 3241480592904468624123725)
                ·
                  refine ⟨1215555222339175734046397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3241480592904468624123725 1215555222339175734046397)
                  ·
                    refine ⟨455833208377190900267399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215555222339175734046397 455833208377190900267399)
                    ·
                      rfl

theorem cell22_1331598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_1331598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331598 prefixEnd_1331598 := by exact prefixLift 1331598
  have htrace : WordTrace (prefixWord ++ tailWord_1331598) baseStart_1331598 baseEnd_1331598 := by
    simpa [prefixWord, tailWord_1331598, baseEnd_1331598] using wordTrace_append hprefix tailTrace_1331598
  have hstable : (prefixWord ++ tailWord_1331598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331598).length < 2 ^ (prefixWord ++ tailWord_1331598).sum := by decide
  have hdescent : baseEnd_1331598 < baseStart_1331598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331641 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_1331641 : Nat := 118140960795 + 1331641 * 2 ^ 59
def prefixEnd_1331641 : Nat := 4983230072969 + 3 ^ 40 * 1331641 * 2
def baseEnd_1331641 : Nat := 455847928155953121442267

theorem tailTrace_1331641 : CollatzResearch.WordTrace tailWord_1331641 prefixEnd_1331641 455847928155953121442267 := by
  unfold tailWord_1331641
  simp only [CollatzResearch.WordTrace]
  refine ⟨48568937368699558021586777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32379291579133038681057851 48568937368699558021586777)
  ·
    refine ⟨36426703026524668516190083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48568937368699558021586777 36426703026524668516190083)
    ·
      refine ⟨54640054539787002774285125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36426703026524668516190083 54640054539787002774285125)
      ·
        refine ⟨10245010226210063020178461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54640054539787002774285125 10245010226210063020178461)
        ·
          refine ⟨3841878834828773632566923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10245010226210063020178461 3841878834828773632566923)
          ·
            refine ⟨5762818252243160448850385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841878834828773632566923 5762818252243160448850385)
            ·
              refine ⟨4322113689182370336637789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5762818252243160448850385 4322113689182370336637789)
              ·
                refine ⟨1620792633443388876239171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4322113689182370336637789 1620792633443388876239171)
                ·
                  refine ⟨2431188950165083314358757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620792633443388876239171 2431188950165083314358757)
                  ·
                    refine ⟨455847928155953121442267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2431188950165083314358757 455847928155953121442267)
                    ·
                      rfl

theorem cell22_1331641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_1331641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331641 prefixEnd_1331641 := by exact prefixLift 1331641
  have htrace : WordTrace (prefixWord ++ tailWord_1331641) baseStart_1331641 baseEnd_1331641 := by
    simpa [prefixWord, tailWord_1331641, baseEnd_1331641] using wordTrace_append hprefix tailTrace_1331641
  have hstable : (prefixWord ++ tailWord_1331641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331641).length < 2 ^ (prefixWord ++ tailWord_1331641).sum := by decide
  have hdescent : baseEnd_1331641 < baseStart_1331641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331649 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1331649 : Nat := 118140960795 + 1331649 * 2 ^ 59
def prefixEnd_1331649 : Nat := 4983230072969 + 3 ^ 40 * 1331649 * 2
def baseEnd_1331649 : Nat := 455850666719443767242243

theorem tailTrace_1331649 : CollatzResearch.WordTrace tailWord_1331649 prefixEnd_1331649 455850666719443767242243 := by
  unfold tailWord_1331649
  simp only [CollatzResearch.WordTrace]
  refine ⟨48569229152670575387878001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32379486101780383591918667 48569229152670575387878001)
  ·
    refine ⟨36426921864502931540908501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48569229152670575387878001 36426921864502931540908501)
    ·
      refine ⟨853755981199287457990043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 36426921864502931540908501 853755981199287457990043)
      ·
        refine ⟨1280633971798931186985065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853755981199287457990043 1280633971798931186985065)
        ·
          refine ⟨960475478849198390238799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1280633971798931186985065 960475478849198390238799)
          ·
            refine ⟨1440713218273797585358199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960475478849198390238799 1440713218273797585358199)
            ·
              refine ⟨2161069827410696378037299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440713218273797585358199 2161069827410696378037299)
              ·
                refine ⟨3241604741116044567055949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161069827410696378037299 3241604741116044567055949)
                ·
                  refine ⟨1215601777918516712645981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3241604741116044567055949 1215601777918516712645981)
                  ·
                    refine ⟨455850666719443767242243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215601777918516712645981 455850666719443767242243)
                    ·
                      rfl

theorem cell22_1331649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1331649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331649 prefixEnd_1331649 := by exact prefixLift 1331649
  have htrace : WordTrace (prefixWord ++ tailWord_1331649) baseStart_1331649 baseEnd_1331649 := by
    simpa [prefixWord, tailWord_1331649, baseEnd_1331649] using wordTrace_append hprefix tailTrace_1331649
  have hstable : (prefixWord ++ tailWord_1331649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331649).length < 2 ^ (prefixWord ++ tailWord_1331649).sum := by decide
  have hdescent : baseEnd_1331649 < baseStart_1331649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331656 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 6]
def baseStart_1331656 : Nat := 118140960795 + 1331656 * 2 ^ 59
def prefixEnd_1331656 : Nat := 4983230072969 + 3 ^ 40 * 1331656 * 2
def baseEnd_1331656 : Nat := 151951020987499360772407

theorem tailTrace_1331656 : CollatzResearch.WordTrace tailWord_1331656 prefixEnd_1331656 151951020987499360772407 := by
  unfold tailWord_1331656
  simp only [CollatzResearch.WordTrace]
  refine ⟨24284742231822607791691411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32379656309096810388921881 24284742231822607791691411)
  ·
    refine ⟨36427113347733911687537117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24284742231822607791691411 36427113347733911687537117)
    ·
      refine ⟨13660167505400216882826419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36427113347733911687537117 13660167505400216882826419)
      ·
        refine ⟨20490251258100325324239629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13660167505400216882826419 20490251258100325324239629)
        ·
          refine ⟨7683844221787621996589861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20490251258100325324239629 7683844221787621996589861)
          ·
            refine ⟨1440720791585179124360599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7683844221787621996589861 1440720791585179124360599)
            ·
              refine ⟨2161081187377768686540899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440720791585179124360599 2161081187377768686540899)
              ·
                refine ⟨3241621781066653029811349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161081187377768686540899 3241621781066653029811349)
                ·
                  refine ⟨151951020987499360772407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3241621781066653029811349 151951020987499360772407)
                  ·
                    rfl

theorem cell22_1331656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_1331656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331656 prefixEnd_1331656 := by exact prefixLift 1331656
  have htrace : WordTrace (prefixWord ++ tailWord_1331656) baseStart_1331656 baseEnd_1331656 := by
    simpa [prefixWord, tailWord_1331656, baseEnd_1331656] using wordTrace_append hprefix tailTrace_1331656
  have hstable : (prefixWord ++ tailWord_1331656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331656).length < 2 ^ (prefixWord ++ tailWord_1331656).sum := by decide
  have hdescent : baseEnd_1331656 < baseStart_1331656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331701 : List Nat := [1, 3, 5, 1, 2, 10]
def baseStart_1331701 : Nat := 118140960795 + 1331701 * 2 ^ 59
def prefixEnd_1331701 : Nat := 4983230072969 + 3 ^ 40 * 1331701 * 2
def baseEnd_1331701 : Nat := 5628005770149789690643

theorem tailTrace_1331701 : CollatzResearch.WordTrace tailWord_1331701 prefixEnd_1331701 5628005770149789690643 := by
  unfold tailWord_1331701
  simp only [CollatzResearch.WordTrace]
  refine ⟨48571125748482188268770957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32380750498988125512513971 48571125748482188268770957)
  ·
    refine ⟨18214172155680820600789109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48571125748482188268770957 18214172155680820600789109)
    ·
      refine ⟨1707578639595076931323979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18214172155680820600789109 1707578639595076931323979)
      ·
        refine ⟨2561367959392615396985969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707578639595076931323979 2561367959392615396985969)
        ·
          refine ⟨1921025969544461547739477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2561367959392615396985969 1921025969544461547739477)
          ·
            refine ⟨5628005770149789690643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1921025969544461547739477 5628005770149789690643)
            ·
              rfl

theorem cell22_1331701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 10].length) (baseStart_1331701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331701 prefixEnd_1331701 := by exact prefixLift 1331701
  have htrace : WordTrace (prefixWord ++ tailWord_1331701) baseStart_1331701 baseEnd_1331701 := by
    simpa [prefixWord, tailWord_1331701, baseEnd_1331701] using wordTrace_append hprefix tailTrace_1331701
  have hstable : (prefixWord ++ tailWord_1331701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331701).length < 2 ^ (prefixWord ++ tailWord_1331701).sum := by decide
  have hdescent : baseEnd_1331701 < baseStart_1331701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331793 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_1331793 : Nat := 118140960795 + 1331793 * 2 ^ 59
def prefixEnd_1331793 : Nat := 4983230072969 + 3 ^ 40 * 1331793 * 2
def baseEnd_1331793 : Nat := 455899960862275391641801

theorem tailTrace_1331793 : CollatzResearch.WordTrace tailWord_1331793 prefixEnd_1331793 455899960862275391641801 := by
  unfold tailWord_1331793
  simp only [CollatzResearch.WordTrace]
  refine ⟨48574481264148887981120033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32382987509432591987413355 48574481264148887981120033)
  ·
    refine ⟨36430860948111665985840025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48574481264148887981120033 36430860948111665985840025)
    ·
      refine ⟨27323145711083749489380019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36430860948111665985840025 27323145711083749489380019)
      ·
        refine ⟨40984718566625624234070029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27323145711083749489380019 40984718566625624234070029)
        ·
          refine ⟨15369269462484609087776261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40984718566625624234070029 15369269462484609087776261)
          ·
            refine ⟨2881738024215864203958049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15369269462484609087776261 2881738024215864203958049)
            ·
              refine ⟨2161303518161898152968537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881738024215864203958049 2161303518161898152968537)
              ·
                refine ⟨1620977638621423614726403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161303518161898152968537 1620977638621423614726403)
                ·
                  refine ⟨2431466457932135422089605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620977638621423614726403 2431466457932135422089605)
                  ·
                    refine ⟨455899960862275391641801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2431466457932135422089605 455899960862275391641801)
                    ·
                      rfl

theorem cell22_1331793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_1331793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331793 prefixEnd_1331793 := by exact prefixLift 1331793
  have htrace : WordTrace (prefixWord ++ tailWord_1331793) baseStart_1331793 baseEnd_1331793 := by
    simpa [prefixWord, tailWord_1331793, baseEnd_1331793] using wordTrace_append hprefix tailTrace_1331793
  have hstable : (prefixWord ++ tailWord_1331793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331793).length < 2 ^ (prefixWord ++ tailWord_1331793).sum := by decide
  have hdescent : baseEnd_1331793 < baseStart_1331793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331808 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 4]
def baseStart_1331808 : Nat := 118140960795 + 1331808 * 2 ^ 59
def prefixEnd_1331808 : Nat := 4983230072969 + 3 ^ 40 * 1331808 * 2
def baseEnd_1331808 : Nat := 151968365222940117505585

theorem tailTrace_1331808 : CollatzResearch.WordTrace tailWord_1331808 prefixEnd_1331808 151968365222940117505585 := by
  unfold tailWord_1331808
  simp only [CollatzResearch.WordTrace]
  refine ⟨24287514179547272771458039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32383352239396363695277385 24287514179547272771458039)
  ·
    refine ⟨36431271269320909157187059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24287514179547272771458039 36431271269320909157187059)
    ·
      refine ⟨54646906903981363735780589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36431271269320909157187059 54646906903981363735780589)
      ·
        refine ⟨20492590088993011400917721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54646906903981363735780589 20492590088993011400917721)
        ·
          refine ⟨15369442566744758550688291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20492590088993011400917721 15369442566744758550688291)
          ·
            refine ⟨23054163850117137826032437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15369442566744758550688291 23054163850117137826032437)
            ·
              refine ⟨2161327860948481671190541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23054163850117137826032437 2161327860948481671190541)
              ·
                refine ⟨810497947855680626696453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2161327860948481671190541 810497947855680626696453)
                ·
                  refine ⟨151968365222940117505585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 810497947855680626696453 151968365222940117505585)
                  ·
                    rfl

theorem cell22_1331808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_1331808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331808 prefixEnd_1331808 := by exact prefixLift 1331808
  have htrace : WordTrace (prefixWord ++ tailWord_1331808) baseStart_1331808 baseEnd_1331808 := by
    simpa [prefixWord, tailWord_1331808, baseEnd_1331808] using wordTrace_append hprefix tailTrace_1331808
  have hstable : (prefixWord ++ tailWord_1331808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331808).length < 2 ^ (prefixWord ++ tailWord_1331808).sum := by decide
  have hdescent : baseEnd_1331808 < baseStart_1331808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331840 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 2, 3]
def baseStart_1331840 : Nat := 118140960795 + 1331840 * 2 ^ 59
def prefixEnd_1331840 : Nat := 4983230072969 + 3 ^ 40 * 1331840 * 2
def baseEnd_1331840 : Nat := 455916049922782935716657

theorem tailTrace_1331840 : CollatzResearch.WordTrace tailWord_1331840 prefixEnd_1331840 455916049922782935716657 := by
  unfold tailWord_1331840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24288097747489307504040487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32384130329985743338720649 24288097747489307504040487)
  ·
    refine ⟨36432146621233961256060731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24288097747489307504040487 36432146621233961256060731)
    ·
      refine ⟨54648219931850941884091097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36432146621233961256060731 54648219931850941884091097)
      ·
        refine ⟨40986164948888206413068323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54648219931850941884091097 40986164948888206413068323)
        ·
          refine ⟨61479247423332309619602485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40986164948888206413068323 61479247423332309619602485)
          ·
            refine ⟨5763679445937404026837733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61479247423332309619602485 5763679445937404026837733)
            ·
              refine ⟨1080689896113263255032075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5763679445937404026837733 1080689896113263255032075)
              ·
                refine ⟨1621034844169894882548113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080689896113263255032075 1621034844169894882548113)
                ·
                  refine ⟨1215776133127421161911085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621034844169894882548113 1215776133127421161911085)
                  ·
                    refine ⟨455916049922782935716657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215776133127421161911085 455916049922782935716657)
                    ·
                      rfl

theorem cell22_1331840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_1331840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331840 prefixEnd_1331840 := by exact prefixLift 1331840
  have htrace : WordTrace (prefixWord ++ tailWord_1331840) baseStart_1331840 baseEnd_1331840 := by
    simpa [prefixWord, tailWord_1331840, baseEnd_1331840] using wordTrace_append hprefix tailTrace_1331840
  have hstable : (prefixWord ++ tailWord_1331840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331840).length < 2 ^ (prefixWord ++ tailWord_1331840).sum := by decide
  have hdescent : baseEnd_1331840 < baseStart_1331840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331881 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 5]
def baseStart_1331881 : Nat := 118140960795 + 1331881 * 2 ^ 59
def prefixEnd_1331881 : Nat := 4983230072969 + 3 ^ 40 * 1331881 * 2
def baseEnd_1331881 : Nat := 151976695020224165147177

theorem tailTrace_1331881 : CollatzResearch.WordTrace tailWord_1331881 prefixEnd_1331881 151976695020224165147177 := by
  unfold tailWord_1331881
  simp only [CollatzResearch.WordTrace]
  refine ⟨48577690887830079010323497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32385127258553386006882331 48577690887830079010323497)
  ·
    refine ⟨36433268165872559257742623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48577690887830079010323497 36433268165872559257742623)
    ·
      refine ⟨54649902248808838886613935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36433268165872559257742623 54649902248808838886613935)
      ·
        refine ⟨81974853373213258329920903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54649902248808838886613935 81974853373213258329920903)
        ·
          refine ⟨122962280059819887494881355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81974853373213258329920903 122962280059819887494881355)
          ·
            refine ⟨184443420089729831242322033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122962280059819887494881355 184443420089729831242322033)
            ·
              refine ⟨138332565067297373431741525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184443420089729831242322033 138332565067297373431741525)
              ·
                refine ⟨1621084746882391094903221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 138332565067297373431741525 1621084746882391094903221)
                ·
                  refine ⟨151976695020224165147177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621084746882391094903221 151976695020224165147177)
                  ·
                    rfl

theorem cell22_1331881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_1331881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331881 prefixEnd_1331881 := by exact prefixLift 1331881
  have htrace : WordTrace (prefixWord ++ tailWord_1331881) baseStart_1331881 baseEnd_1331881 := by
    simpa [prefixWord, tailWord_1331881, baseEnd_1331881] using wordTrace_append hprefix tailTrace_1331881
  have hstable : (prefixWord ++ tailWord_1331881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331881).length < 2 ^ (prefixWord ++ tailWord_1331881).sum := by decide
  have hdescent : baseEnd_1331881 < baseStart_1331881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331932 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 5]
def baseStart_1331932 : Nat := 118140960795 + 1331932 * 2 ^ 59
def prefixEnd_1331932 : Nat := 4983230072969 + 3 ^ 40 * 1331932 * 2
def baseEnd_1331932 : Nat := 151982514467641787472125

theorem tailTrace_1331932 : CollatzResearch.WordTrace tailWord_1331932 prefixEnd_1331932 151982514467641787472125 := by
  unfold tailWord_1331932
  simp only [CollatzResearch.WordTrace]
  refine ⟨24289775505322657360215025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32386367340430209813620033 24289775505322657360215025)
  ·
    refine ⟨18217331628991993020161269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24289775505322657360215025 18217331628991993020161269)
    ·
      refine ⟨1707874840217999345640119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18217331628991993020161269 1707874840217999345640119)
      ·
        refine ⟨2561812260326999018460179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707874840217999345640119 2561812260326999018460179)
        ·
          refine ⟨3842718390490498527690269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561812260326999018460179 3842718390490498527690269)
          ·
            refine ⟨1441019396433936947883851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3842718390490498527690269 1441019396433936947883851)
            ·
              refine ⟨2161529094650905421825777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441019396433936947883851 2161529094650905421825777)
              ·
                refine ⟨1621146820988179066369333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161529094650905421825777 1621146820988179066369333)
                ·
                  refine ⟨151982514467641787472125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621146820988179066369333 151982514467641787472125)
                  ·
                    rfl

theorem cell22_1331932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_1331932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331932 prefixEnd_1331932 := by exact prefixLift 1331932
  have htrace : WordTrace (prefixWord ++ tailWord_1331932) baseStart_1331932 baseEnd_1331932 := by
    simpa [prefixWord, tailWord_1331932, baseEnd_1331932] using wordTrace_append hprefix tailTrace_1331932
  have hstable : (prefixWord ++ tailWord_1331932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331932).length < 2 ^ (prefixWord ++ tailWord_1331932).sum := by decide
  have hdescent : baseEnd_1331932 < baseStart_1331932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331975 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1331975 : Nat := 118140960795 + 1331975 * 2 ^ 59
def prefixEnd_1331975 : Nat := 4983230072969 + 3 ^ 40 * 1331975 * 2
def baseEnd_1331975 : Nat := 455962263181687583591243

theorem tailTrace_1331975 : CollatzResearch.WordTrace tailWord_1331975 prefixEnd_1331975 455962263181687583591243 := by
  unfold tailWord_1331975
  simp only [CollatzResearch.WordTrace]
  refine ⟨48581119349489533064245379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32387412899659688709496919 48581119349489533064245379)
  ·
    refine ⟨72871679024234299596368069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48581119349489533064245379 72871679024234299596368069)
    ·
      refine ⟨13663439817043931174319013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72871679024234299596368069 13663439817043931174319013)
      ·
        refine ⟨2561894965695737095184815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13663439817043931174319013 2561894965695737095184815)
        ·
          refine ⟨3842842448543605642777223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561894965695737095184815 3842842448543605642777223)
          ·
            refine ⟨5764263672815408464165835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842842448543605642777223 5764263672815408464165835)
            ·
              refine ⟨8646395509223112696248753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5764263672815408464165835 8646395509223112696248753)
              ·
                refine ⟨6484796631917334522186565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8646395509223112696248753 6484796631917334522186565)
                ·
                  refine ⟨1215899368484500222909981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6484796631917334522186565 1215899368484500222909981)
                  ·
                    refine ⟨455962263181687583591243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215899368484500222909981 455962263181687583591243)
                    ·
                      rfl

theorem cell22_1331975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1331975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331975 prefixEnd_1331975 := by exact prefixLift 1331975
  have htrace : WordTrace (prefixWord ++ tailWord_1331975) baseStart_1331975 baseEnd_1331975 := by
    simpa [prefixWord, tailWord_1331975, baseEnd_1331975] using wordTrace_append hprefix tailTrace_1331975
  have hstable : (prefixWord ++ tailWord_1331975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331975).length < 2 ^ (prefixWord ++ tailWord_1331975).sum := by decide
  have hdescent : baseEnd_1331975 < baseStart_1331975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332050 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1332050 : Nat := 118140960795 + 1332050 * 2 ^ 59
def prefixEnd_1332050 : Nat := 4983230072969 + 3 ^ 40 * 1332050 * 2
def baseEnd_1332050 : Nat := 151995979071470795988671

theorem tailTrace_1332050 : CollatzResearch.WordTrace tailWord_1332050 prefixEnd_1332050 151995979071470795988671 := by
  unfold tailWord_1332050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12145963706054455218306401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32389236549478547248817069 12145963706054455218306401)
  ·
    refine ⟨9109472779540841413729801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12145963706054455218306401 9109472779540841413729801)
    ·
      refine ⟨6832104584655631060297351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9109472779540841413729801 6832104584655631060297351)
      ·
        refine ⟨10248156876983446590446027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832104584655631060297351 10248156876983446590446027)
        ·
          refine ⟨15372235315475169885669041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248156876983446590446027 15372235315475169885669041)
          ·
            refine ⟨11529176486606377414251781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15372235315475169885669041 11529176486606377414251781)
            ·
              refine ⟨2161720591238695765172209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11529176486606377414251781 2161720591238695765172209)
              ·
                refine ⟨1621290443429021823879157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161720591238695765172209 1621290443429021823879157)
                ·
                  refine ⟨151995979071470795988671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621290443429021823879157 151995979071470795988671)
                  ·
                    rfl

theorem cell22_1332050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1332050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332050 prefixEnd_1332050 := by exact prefixLift 1332050
  have htrace : WordTrace (prefixWord ++ tailWord_1332050) baseStart_1332050 baseEnd_1332050 := by
    simpa [prefixWord, tailWord_1332050, baseEnd_1332050] using wordTrace_append hprefix tailTrace_1332050
  have hstable : (prefixWord ++ tailWord_1332050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332050).length < 2 ^ (prefixWord ++ tailWord_1332050).sum := by decide
  have hdescent : baseEnd_1332050 < baseStart_1332050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332063 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 5, 4]
def baseStart_1332063 : Nat := 118140960795 + 1332063 * 2 ^ 59
def prefixEnd_1332063 : Nat := 4983230072969 + 3 ^ 40 * 1332063 * 2
def baseEnd_1332063 : Nat := 455992387380084687390973

theorem tailTrace_1332063 : CollatzResearch.WordTrace tailWord_1332063 prefixEnd_1332063 455992387380084687390973 := by
  unfold tailWord_1332063
  simp only [CollatzResearch.WordTrace]
  refine ⟨48584328973170724093448843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32389552648780482728965895 48584328973170724093448843)
  ·
    refine ⟨72876493459756086140173265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48584328973170724093448843 72876493459756086140173265)
    ·
      refine ⟨54657370094817064605129949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72876493459756086140173265 54657370094817064605129949)
      ·
        refine ⟨20496513785556399226923731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54657370094817064605129949 20496513785556399226923731)
        ·
          refine ⟨30744770678334598840385597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20496513785556399226923731 30744770678334598840385597)
          ·
            refine ⟨11529289004375474565144599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30744770678334598840385597 11529289004375474565144599)
            ·
              refine ⟨17293933506563211847716899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11529289004375474565144599 17293933506563211847716899)
              ·
                refine ⟨25940900259844817771575349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17293933506563211847716899 25940900259844817771575349)
                ·
                  refine ⟨2431959399360451666085189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25940900259844817771575349 2431959399360451666085189)
                  ·
                    refine ⟨455992387380084687390973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2431959399360451666085189 455992387380084687390973)
                    ·
                      rfl

theorem cell22_1332063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_1332063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332063 prefixEnd_1332063 := by exact prefixLift 1332063
  have htrace : WordTrace (prefixWord ++ tailWord_1332063) baseStart_1332063 baseEnd_1332063 := by
    simpa [prefixWord, tailWord_1332063, baseEnd_1332063] using wordTrace_append hprefix tailTrace_1332063
  have hstable : (prefixWord ++ tailWord_1332063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332063).length < 2 ^ (prefixWord ++ tailWord_1332063).sum := by decide
  have hdescent : baseEnd_1332063 < baseStart_1332063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332095 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 4]
def baseStart_1332095 : Nat := 118140960795 + 1332095 * 2 ^ 59
def prefixEnd_1332095 : Nat := 4983230072969 + 3 ^ 40 * 1332095 * 2
def baseEnd_1332095 : Nat := 152001113878015756863625

theorem tailTrace_1332095 : CollatzResearch.WordTrace tailWord_1332095 prefixEnd_1332095 152001113878015756863625 := by
  unfold tailWord_1332095
  simp only [CollatzResearch.WordTrace]
  refine ⟨48585496109054793558613739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32390330739369862372409159 48585496109054793558613739)
  ·
    refine ⟨72878244163582190337920609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48585496109054793558613739 72878244163582190337920609)
    ·
      refine ⟨54658683122686642753440457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72878244163582190337920609 54658683122686642753440457)
      ·
        refine ⟨40994012342014982065080343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54658683122686642753440457 40994012342014982065080343)
        ·
          refine ⟨61491018513022473097620515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40994012342014982065080343 61491018513022473097620515)
          ·
            refine ⟨92236527769533709646430773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61491018513022473097620515 92236527769533709646430773)
            ·
              refine ⟨8647174478393785279352885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92236527769533709646430773 8647174478393785279352885)
              ·
                refine ⟨810672607349417369939333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8647174478393785279352885 810672607349417369939333)
                ·
                  refine ⟨152001113878015756863625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 810672607349417369939333 152001113878015756863625)
                  ·
                    rfl

theorem cell22_1332095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 4].length) (baseStart_1332095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332095 prefixEnd_1332095 := by exact prefixLift 1332095
  have htrace : WordTrace (prefixWord ++ tailWord_1332095) baseStart_1332095 baseEnd_1332095 := by
    simpa [prefixWord, tailWord_1332095, baseEnd_1332095] using wordTrace_append hprefix tailTrace_1332095
  have hstable : (prefixWord ++ tailWord_1332095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332095).length < 2 ^ (prefixWord ++ tailWord_1332095).sum := by decide
  have hdescent : baseEnd_1332095 < baseStart_1332095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332127 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 1, 5]
def baseStart_1332127 : Nat := 118140960795 + 1332127 * 2 ^ 59
def prefixEnd_1332127 : Nat := 4983230072969 + 3 ^ 40 * 1332127 * 2
def baseEnd_1332127 : Nat := 456014295888009853790777

theorem tailTrace_1332127 : CollatzResearch.WordTrace tailWord_1332127 prefixEnd_1332127 456014295888009853790777 := by
  unfold tailWord_1332127
  simp only [CollatzResearch.WordTrace]
  refine ⟨48586663244938863023778635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32391108829959242015852423 48586663244938863023778635)
  ·
    refine ⟨72879994867408294535667953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48586663244938863023778635 72879994867408294535667953)
    ·
      refine ⟨54659996150556220901750965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72879994867408294535667953 54659996150556220901750965)
      ·
        refine ⟨5124374639114645709539153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54659996150556220901750965 5124374639114645709539153)
        ·
          refine ⟨3843280979335984282154365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5124374639114645709539153 3843280979335984282154365)
          ·
            refine ⟨1441230367250994105807887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3843280979335984282154365 1441230367250994105807887)
            ·
              refine ⟨2161845550876491158711831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441230367250994105807887 2161845550876491158711831)
              ·
                refine ⟨3242768326314736738067747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161845550876491158711831 3242768326314736738067747)
                ·
                  refine ⟨4864152489472105107101621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242768326314736738067747 4864152489472105107101621)
                  ·
                    refine ⟨456014295888009853790777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4864152489472105107101621 456014295888009853790777)
                    ·
                      rfl

theorem cell22_1332127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_1332127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332127 prefixEnd_1332127 := by exact prefixLift 1332127
  have htrace : WordTrace (prefixWord ++ tailWord_1332127) baseStart_1332127 baseEnd_1332127 := by
    simpa [prefixWord, tailWord_1332127, baseEnd_1332127] using wordTrace_append hprefix tailTrace_1332127
  have hstable : (prefixWord ++ tailWord_1332127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332127).length < 2 ^ (prefixWord ++ tailWord_1332127).sum := by decide
  have hdescent : baseEnd_1332127 < baseStart_1332127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332157 : List Nat := [1, 4, 1, 2, 5, 1, 8]
def baseStart_1332157 : Nat := 118140960795 + 1332157 * 2 ^ 59
def prefixEnd_1332157 : Nat := 4983230072969 + 3 ^ 40 * 1332157 * 2
def baseEnd_1332157 : Nat := 16889798722262954649655

theorem tailTrace_1332157 : CollatzResearch.WordTrace tailWord_1332157 prefixEnd_1332157 16889798722262954649655 := by
  unfold tailWord_1332157
  simp only [CollatzResearch.WordTrace]
  refine ⟨48587757434830178147370725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32391838289886785431580483 48587757434830178147370725)
  ·
    refine ⟨9110204519030658402632011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48587757434830178147370725 9110204519030658402632011)
    ·
      refine ⟨13665306778545987603948017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110204519030658402632011 13665306778545987603948017)
      ·
        refine ⟨10248980083909490702961013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13665306778545987603948017 10248980083909490702961013)
        ·
          refine ⟨960841882866514753402595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10248980083909490702961013 960841882866514753402595)
          ·
            refine ⟨1441262824299772130103893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960841882866514753402595 1441262824299772130103893)
            ·
              refine ⟨16889798722262954649655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1441262824299772130103893 16889798722262954649655)
              ·
                rfl

theorem cell22_1332157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 8].length) (baseStart_1332157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332157 prefixEnd_1332157 := by exact prefixLift 1332157
  have htrace : WordTrace (prefixWord ++ tailWord_1332157) baseStart_1332157 baseEnd_1332157 := by
    simpa [prefixWord, tailWord_1332157, baseEnd_1332157] using wordTrace_append hprefix tailTrace_1332157
  have hstable : (prefixWord ++ tailWord_1332157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332157).length < 2 ^ (prefixWord ++ tailWord_1332157).sum := by decide
  have hdescent : baseEnd_1332157 < baseStart_1332157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332247 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 6]
def baseStart_1332247 : Nat := 118140960795 + 1332247 * 2 ^ 59
def prefixEnd_1332247 : Nat := 4983230072969 + 3 ^ 40 * 1332247 * 2
def baseEnd_1332247 : Nat := 152018458113456513596803

theorem tailTrace_1332247 : CollatzResearch.WordTrace tailWord_1332247 prefixEnd_1332247 152018458113456513596803 := by
  unfold tailWord_1332247
  simp only [CollatzResearch.WordTrace]
  refine ⟨48591040004504123518146995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32394026669669415678764663 48591040004504123518146995)
  ·
    refine ⟨72886560006756185277220493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48591040004504123518146995 72886560006756185277220493)
    ·
      refine ⟨27332460002533569478957685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72886560006756185277220493 27332460002533569478957685)
      ·
        refine ⟨2562418125237522138652283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27332460002533569478957685 2562418125237522138652283)
        ·
          refine ⟨3843627187856283207978425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562418125237522138652283 3843627187856283207978425)
          ·
            refine ⟨2882720390892212405983819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3843627187856283207978425 2882720390892212405983819)
            ·
              refine ⟨4324080586338318608975729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882720390892212405983819 4324080586338318608975729)
              ·
                refine ⟨3243060439753738956731797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4324080586338318608975729 3243060439753738956731797)
                ·
                  refine ⟨152018458113456513596803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3243060439753738956731797 152018458113456513596803)
                  ·
                    rfl

theorem cell22_1332247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 6].length) (baseStart_1332247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332247 prefixEnd_1332247 := by exact prefixLift 1332247
  have htrace : WordTrace (prefixWord ++ tailWord_1332247) baseStart_1332247 baseEnd_1332247 := by
    simpa [prefixWord, tailWord_1332247, baseEnd_1332247] using wordTrace_append hprefix tailTrace_1332247
  have hstable : (prefixWord ++ tailWord_1332247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332247).length < 2 ^ (prefixWord ++ tailWord_1332247).sum := by decide
  have hdescent : baseEnd_1332247 < baseStart_1332247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332294 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1332294 : Nat := 118140960795 + 1332294 * 2 ^ 59
def prefixEnd_1332294 : Nat := 4983230072969 + 3 ^ 40 * 1332294 * 2
def baseEnd_1332294 : Nat := 456071463400877084865265

theorem tailTrace_1332294 : CollatzResearch.WordTrace tailWord_1332294 prefixEnd_1332294 456071463400877084865265 := by
  unfold tailWord_1332294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518523569854182829534623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32395169490222567030071957 1518523569854182829534623)
  ·
    refine ⟨2277785354781274244301935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1518523569854182829534623 2277785354781274244301935)
    ·
      refine ⟨3416678032171911366452903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277785354781274244301935 3416678032171911366452903)
      ·
        refine ⟨5125017048257867049679355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416678032171911366452903 5125017048257867049679355)
        ·
          refine ⟨7687525572386800574519033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125017048257867049679355 7687525572386800574519033)
          ·
            refine ⟨5765644179290100430889275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687525572386800574519033 5765644179290100430889275)
            ·
              refine ⟨8648466268935150646333913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765644179290100430889275 8648466268935150646333913)
              ·
                refine ⟨6486349701701362984750435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8648466268935150646333913 6486349701701362984750435)
                ·
                  refine ⟨9729524552552044477125653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6486349701701362984750435 9729524552552044477125653)
                  ·
                    refine ⟨456071463400877084865265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9729524552552044477125653 456071463400877084865265)
                    ·
                      rfl

theorem cell22_1332294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1332294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332294 prefixEnd_1332294 := by exact prefixLift 1332294
  have htrace : WordTrace (prefixWord ++ tailWord_1332294) baseStart_1332294 baseEnd_1332294 := by
    simpa [prefixWord, tailWord_1332294, baseEnd_1332294] using wordTrace_append hprefix tailTrace_1332294
  have hstable : (prefixWord ++ tailWord_1332294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332294).length < 2 ^ (prefixWord ++ tailWord_1332294).sum := by decide
  have hdescent : baseEnd_1332294 < baseStart_1332294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332305 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_1332305 : Nat := 118140960795 + 1332305 * 2 ^ 59
def prefixEnd_1332305 : Nat := 4983230072969 + 3 ^ 40 * 1332305 * 2
def baseEnd_1332305 : Nat := 456075228925676722840231

theorem tailTrace_1332305 : CollatzResearch.WordTrace tailWord_1332305 prefixEnd_1332305 456075228925676722840231 := by
  unfold tailWord_1332305
  simp only [CollatzResearch.WordTrace]
  refine ⟨48593155438293999423758369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32395436958862666282505579 48593155438293999423758369)
  ·
    refine ⟨36444866578720499567818777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48593155438293999423758369 36444866578720499567818777)
    ·
      refine ⟨27333649934040374675864083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36444866578720499567818777 27333649934040374675864083)
      ·
        refine ⟨41000474901060562013796125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27333649934040374675864083 41000474901060562013796125)
        ·
          refine ⟨15375178087897710755173547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41000474901060562013796125 15375178087897710755173547)
          ·
            refine ⟨23062767131846566132760321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15375178087897710755173547 23062767131846566132760321)
            ·
              refine ⟨17297075348884924599570241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23062767131846566132760321 17297075348884924599570241)
              ·
                refine ⟨12972806511663693449677681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17297075348884924599570241 12972806511663693449677681)
                ·
                  refine ⟨9729604883747770087258261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12972806511663693449677681 9729604883747770087258261)
                  ·
                    refine ⟨456075228925676722840231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9729604883747770087258261 456075228925676722840231)
                    ·
                      rfl

theorem cell22_1332305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_1332305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332305 prefixEnd_1332305 := by exact prefixLift 1332305
  have htrace : WordTrace (prefixWord ++ tailWord_1332305) baseStart_1332305 baseEnd_1332305 := by
    simpa [prefixWord, tailWord_1332305, baseEnd_1332305] using wordTrace_append hprefix tailTrace_1332305
  have hstable : (prefixWord ++ tailWord_1332305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332305).length < 2 ^ (prefixWord ++ tailWord_1332305).sum := by decide
  have hdescent : baseEnd_1332305 < baseStart_1332305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332320 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_1332320 : Nat := 118140960795 + 1332320 * 2 ^ 59
def prefixEnd_1332320 : Nat := 4983230072969 + 3 ^ 40 * 1332320 * 2
def baseEnd_1332320 : Nat := 152026787910740561238395

theorem tailTrace_1332320 : CollatzResearch.WordTrace tailWord_1332320 prefixEnd_1332320 152026787910740561238395 := by
  unfold tailWord_1332320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24296851266619828492777207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32395801688826437990369609 24296851266619828492777207)
  ·
    refine ⟨36445276899929742739165811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24296851266619828492777207 36445276899929742739165811)
    ·
      refine ⟨54667915349894614108748717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36445276899929742739165811 54667915349894614108748717)
      ·
        refine ⟨20500468256210480290780769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54667915349894614108748717 20500468256210480290780769)
        ·
          refine ⟨15375351192157860218085577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20500468256210480290780769 15375351192157860218085577)
          ·
            refine ⟨11531513394118395163564183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15375351192157860218085577 11531513394118395163564183)
            ·
              refine ⟨17297270091177592745346275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11531513394118395163564183 17297270091177592745346275)
              ·
                refine ⟨25945905136766389118019413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17297270091177592745346275 25945905136766389118019413)
                ·
                  refine ⟨152026787910740561238395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25945905136766389118019413 152026787910740561238395)
                  ·
                    rfl

theorem cell22_1332320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_1332320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332320 prefixEnd_1332320 := by exact prefixLift 1332320
  have htrace : WordTrace (prefixWord ++ tailWord_1332320) baseStart_1332320 baseEnd_1332320 := by
    simpa [prefixWord, tailWord_1332320, baseEnd_1332320] using wordTrace_append hprefix tailTrace_1332320
  have hstable : (prefixWord ++ tailWord_1332320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332320).length < 2 ^ (prefixWord ++ tailWord_1332320).sum := by decide
  have hdescent : baseEnd_1332320 < baseStart_1332320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332414 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1332414 : Nat := 118140960795 + 1332414 * 2 ^ 59
def prefixEnd_1332414 : Nat := 4983230072969 + 3 ^ 40 * 1332414 * 2
def baseEnd_1332414 : Nat := 456112541853236771864897

theorem tailTrace_1332414 : CollatzResearch.WordTrace tailWord_1332414 prefixEnd_1332414 456112541853236771864897 := by
  unfold tailWord_1332414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6074641374362388879934537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32398087329932740692984197 6074641374362388879934537)
  ·
    refine ⟨4555981030771791659950903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6074641374362388879934537 4555981030771791659950903)
    ·
      refine ⟨6833971546157687489926355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555981030771791659950903 6833971546157687489926355)
      ·
        refine ⟨10250957319236531234889533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6833971546157687489926355 10250957319236531234889533)
        ·
          refine ⟨3844108994713699213083575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10250957319236531234889533 3844108994713699213083575)
          ·
            refine ⟨5766163492070548819625363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844108994713699213083575 5766163492070548819625363)
            ·
              refine ⟨8649245238105823229438045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766163492070548819625363 8649245238105823229438045)
              ·
                refine ⟨3243466964289683711039267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8649245238105823229438045 3243466964289683711039267)
                ·
                  refine ⟨4865200446434525566558901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243466964289683711039267 4865200446434525566558901)
                  ·
                    refine ⟨456112541853236771864897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4865200446434525566558901 456112541853236771864897)
                    ·
                      rfl

theorem cell22_1332414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1332414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332414 prefixEnd_1332414 := by exact prefixLift 1332414
  have htrace : WordTrace (prefixWord ++ tailWord_1332414) baseStart_1332414 baseEnd_1332414 := by
    simpa [prefixWord, tailWord_1332414, baseEnd_1332414] using wordTrace_append hprefix tailTrace_1332414
  have hstable : (prefixWord ++ tailWord_1332414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332414).length < 2 ^ (prefixWord ++ tailWord_1332414).sum := by decide
  have hdescent : baseEnd_1332414 < baseStart_1332414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332459 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 3, 3]
def baseStart_1332459 : Nat := 118140960795 + 1332459 * 2 ^ 59
def prefixEnd_1332459 : Nat := 4983230072969 + 3 ^ 40 * 1332459 * 2
def baseEnd_1332459 : Nat := 456127946272871654489759

theorem tailTrace_1332459 : CollatzResearch.WordTrace tailWord_1332459 prefixEnd_1332459 456127946272871654489759 := by
  unfold tailWord_1332459
  simp only [CollatzResearch.WordTrace]
  refine ⟨48598772279736083724864431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32399181519824055816576287 48598772279736083724864431)
  ·
    refine ⟨72898158419604125587296647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48598772279736083724864431 72898158419604125587296647)
    ·
      refine ⟨109347237629406188380944971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72898158419604125587296647 109347237629406188380944971)
      ·
        refine ⟨164020856444109282571417457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109347237629406188380944971 164020856444109282571417457)
        ·
          refine ⟨123015642333081961928563093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164020856444109282571417457 123015642333081961928563093)
          ·
            refine ⟨5766358234363216965401395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123015642333081961928563093 5766358234363216965401395)
            ·
              refine ⟨8649537351544825448102093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766358234363216965401395 8649537351544825448102093)
              ·
                refine ⟨3243576506829309543038285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8649537351544825448102093 3243576506829309543038285)
                ·
                  refine ⟨1216341190060991078639357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3243576506829309543038285 1216341190060991078639357)
                  ·
                    refine ⟨456127946272871654489759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216341190060991078639357 456127946272871654489759)
                    ·
                      rfl

theorem cell22_1332459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 3].length) (baseStart_1332459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332459 prefixEnd_1332459 := by exact prefixLift 1332459
  have htrace : WordTrace (prefixWord ++ tailWord_1332459) baseStart_1332459 baseEnd_1332459 := by
    simpa [prefixWord, tailWord_1332459, baseEnd_1332459] using wordTrace_append hprefix tailTrace_1332459
  have hstable : (prefixWord ++ tailWord_1332459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332459).length < 2 ^ (prefixWord ++ tailWord_1332459).sum := by decide
  have hdescent : baseEnd_1332459 < baseStart_1332459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332549 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_1332549 : Nat := 118140960795 + 1332549 * 2 ^ 59
def prefixEnd_1332549 : Nat := 4983230072969 + 3 ^ 40 * 1332549 * 2
def baseEnd_1332549 : Nat := 456158755112141419739483

theorem tailTrace_1332549 : CollatzResearch.WordTrace tailWord_1332549 prefixEnd_1332549 456158755112141419739483 := by
  unfold tailWord_1332549
  simp only [CollatzResearch.WordTrace]
  refine ⟨48602054849410029095640701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32401369899606686063760467 48602054849410029095640701)
  ·
    refine ⟨18225770568528760910865263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48602054849410029095640701 18225770568528760910865263)
    ·
      refine ⟨27338655852793141366297895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18225770568528760910865263 27338655852793141366297895)
      ·
        refine ⟨41007983779189712049446843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27338655852793141366297895 41007983779189712049446843)
        ·
          refine ⟨61511975668784568074170265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41007983779189712049446843 61511975668784568074170265)
          ·
            refine ⟨46133981751588426055627699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61511975668784568074170265 46133981751588426055627699)
            ·
              refine ⟨69200972627382639083441549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46133981751588426055627699 69200972627382639083441549)
              ·
                refine ⟨25950364735268489656290581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69200972627382639083441549 25950364735268489656290581)
                ·
                  refine ⟨1216423346965710452638621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25950364735268489656290581 1216423346965710452638621)
                  ·
                    refine ⟨456158755112141419739483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216423346965710452638621 456158755112141419739483)
                    ·
                      rfl

theorem cell22_1332549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_1332549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332549 prefixEnd_1332549 := by exact prefixLift 1332549
  have htrace : WordTrace (prefixWord ++ tailWord_1332549) baseStart_1332549 baseEnd_1332549 := by
    simpa [prefixWord, tailWord_1332549, baseEnd_1332549] using wordTrace_append hprefix tailTrace_1332549
  have hstable : (prefixWord ++ tailWord_1332549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332549).length < 2 ^ (prefixWord ++ tailWord_1332549).sum := by decide
  have hdescent : baseEnd_1332549 < baseStart_1332549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332579 : List Nat := [1, 1, 1, 5, 2, 2, 3, 7]
def baseStart_1332579 : Nat := 118140960795 + 1332579 * 2 ^ 59
def prefixEnd_1332579 : Nat := 4983230072969 + 3 ^ 40 * 1332579 * 2
def baseEnd_1332579 : Nat := 50685447191692371276599

theorem tailTrace_1332579 : CollatzResearch.WordTrace tailWord_1332579 prefixEnd_1332579 50685447191692371276599 := by
  unfold tailWord_1332579
  simp only [CollatzResearch.WordTrace]
  refine ⟨48603149039301344219232791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32402099359534229479488527 48603149039301344219232791)
  ·
    refine ⟨72904723558952016328849187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48603149039301344219232791 72904723558952016328849187)
    ·
      refine ⟨109357085338428024493273781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72904723558952016328849187 109357085338428024493273781)
      ·
        refine ⟨10252226750477627296244417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109357085338428024493273781 10252226750477627296244417)
        ·
          refine ⟨7689170062858220472183313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10252226750477627296244417 7689170062858220472183313)
          ·
            refine ⟨5766877547143665354137485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7689170062858220472183313 5766877547143665354137485)
            ·
              refine ⟨2162579080178874507801557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5766877547143665354137485 2162579080178874507801557)
              ·
                refine ⟨50685447191692371276599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2162579080178874507801557 50685447191692371276599)
                ·
                  rfl

theorem cell22_1332579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 7].length) (baseStart_1332579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332579 prefixEnd_1332579 := by exact prefixLift 1332579
  have htrace : WordTrace (prefixWord ++ tailWord_1332579) baseStart_1332579 baseEnd_1332579 := by
    simpa [prefixWord, tailWord_1332579, baseEnd_1332579] using wordTrace_append hprefix tailTrace_1332579
  have hstable : (prefixWord ++ tailWord_1332579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332579).length < 2 ^ (prefixWord ++ tailWord_1332579).sum := by decide
  have hdescent : baseEnd_1332579 < baseStart_1332579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332628 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1332628 : Nat := 118140960795 + 1332628 * 2 ^ 59
def prefixEnd_1332628 : Nat := 4983230072969 + 3 ^ 40 * 1332628 * 2
def baseEnd_1332628 : Nat := 456185798426611547014241

theorem tailTrace_1332628 : CollatzResearch.WordTrace tailWord_1332628 prefixEnd_1332628 456185798426611547014241 := by
  unfold tailWord_1332628
  simp only [CollatzResearch.WordTrace]
  refine ⟨24302468108061912793883269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32403290810749217058511025 24302468108061912793883269)
  ·
    refine ⟨4556712770261608648853113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24302468108061912793883269 4556712770261608648853113)
    ·
      refine ⟨3417534577696206486639835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4556712770261608648853113 3417534577696206486639835)
      ·
        refine ⟨5126301866544309729959753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417534577696206486639835 5126301866544309729959753)
        ·
          refine ⟨3844726399908232297469815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5126301866544309729959753 3844726399908232297469815)
          ·
            refine ⟨5767089599862348446204723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844726399908232297469815 5767089599862348446204723)
            ·
              refine ⟨8650634399793522669307085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767089599862348446204723 8650634399793522669307085)
              ·
                refine ⟨3243987899922571000990157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8650634399793522669307085 3243987899922571000990157)
                ·
                  refine ⟨1216495462470964125371309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3243987899922571000990157 1216495462470964125371309)
                  ·
                    refine ⟨456185798426611547014241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216495462470964125371309 456185798426611547014241)
                    ·
                      rfl

theorem cell22_1332628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1332628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332628 prefixEnd_1332628 := by exact prefixLift 1332628
  have htrace : WordTrace (prefixWord ++ tailWord_1332628) baseStart_1332628 baseEnd_1332628 := by
    simpa [prefixWord, tailWord_1332628, baseEnd_1332628] using wordTrace_append hprefix tailTrace_1332628
  have hstable : (prefixWord ++ tailWord_1332628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332628).length < 2 ^ (prefixWord ++ tailWord_1332628).sum := by decide
  have hdescent : baseEnd_1332628 < baseStart_1332628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332686 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1332686 : Nat := 118140960795 + 1332686 * 2 ^ 59
def prefixEnd_1332686 : Nat := 4983230072969 + 3 ^ 40 * 1332686 * 2
def baseEnd_1332686 : Nat := 152068551003972909688021

theorem tailTrace_1332686 : CollatzResearch.WordTrace tailWord_1332686 prefixEnd_1332686 152068551003972909688021 := by
  unfold tailWord_1332686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075881456239212686672239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32404701099942467662251941 6075881456239212686672239)
  ·
    refine ⟨9113822184358819030008359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6075881456239212686672239 9113822184358819030008359)
    ·
      refine ⟨13670733276538228545012539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9113822184358819030008359 13670733276538228545012539)
      ·
        refine ⟨20506099914807342817518809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13670733276538228545012539 20506099914807342817518809)
        ·
          refine ⟨15379574936105507113139107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20506099914807342817518809 15379574936105507113139107)
          ·
            refine ⟨23069362404158260669708661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15379574936105507113139107 23069362404158260669708661)
            ·
              refine ⟨2162752725389836937785187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23069362404158260669708661 2162752725389836937785187)
              ·
                refine ⟨3244129088084755406677781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162752725389836937785187 3244129088084755406677781)
                ·
                  refine ⟨152068551003972909688021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3244129088084755406677781 152068551003972909688021)
                  ·
                    rfl

theorem cell22_1332686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1332686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332686 prefixEnd_1332686 := by exact prefixLift 1332686
  have htrace : WordTrace (prefixWord ++ tailWord_1332686) baseStart_1332686 baseEnd_1332686 := by
    simpa [prefixWord, tailWord_1332686, baseEnd_1332686] using wordTrace_append hprefix tailTrace_1332686
  have hstable : (prefixWord ++ tailWord_1332686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332686).length < 2 ^ (prefixWord ++ tailWord_1332686).sum := by decide
  have hdescent : baseEnd_1332686 < baseStart_1332686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332692 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1332692 : Nat := 118140960795 + 1332692 * 2 ^ 59
def prefixEnd_1332692 : Nat := 4983230072969 + 3 ^ 40 * 1332692 * 2
def baseEnd_1332692 : Nat := 152069235644845571138015

theorem tailTrace_1332692 : CollatzResearch.WordTrace tailWord_1332692 prefixEnd_1332692 152069235644845571138015 := by
  unfold tailWord_1332692
  simp only [CollatzResearch.WordTrace]
  refine ⟨24303635243945982259048165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32404846991927976345397553 24303635243945982259048165)
  ·
    refine ⟨4556931608239871673571531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24303635243945982259048165 4556931608239871673571531)
    ·
      refine ⟨6835397412359807510357297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556931608239871673571531 6835397412359807510357297)
      ·
        refine ⟨5126548059269855632767973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6835397412359807510357297 5126548059269855632767973)
        ·
          refine ⟨961227761113097931143995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5126548059269855632767973 961227761113097931143995)
          ·
            refine ⟨1441841641669646896715993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961227761113097931143995 1441841641669646896715993)
            ·
              refine ⟨1081381231252235172536995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441841641669646896715993 1081381231252235172536995)
              ·
                refine ⟨1622071846878352758805493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081381231252235172536995 1622071846878352758805493)
                ·
                  refine ⟨152069235644845571138015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1622071846878352758805493 152069235644845571138015)
                  ·
                    rfl

theorem cell22_1332692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1332692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332692 prefixEnd_1332692 := by exact prefixLift 1332692
  have htrace : WordTrace (prefixWord ++ tailWord_1332692) baseStart_1332692 baseEnd_1332692 := by
    simpa [prefixWord, tailWord_1332692, baseEnd_1332692] using wordTrace_append hprefix tailTrace_1332692
  have hstable : (prefixWord ++ tailWord_1332692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332692).length < 2 ^ (prefixWord ++ tailWord_1332692).sum := by decide
  have hdescent : baseEnd_1332692 < baseStart_1332692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332737 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 4]
def baseStart_1332737 : Nat := 118140960795 + 1332737 * 2 ^ 59
def prefixEnd_1332737 : Nat := 4983230072969 + 3 ^ 40 * 1332737 * 2
def baseEnd_1332737 : Nat := 152074370451390532012969

theorem tailTrace_1332737 : CollatzResearch.WordTrace tailWord_1332737 prefixEnd_1332737 152074370451390532012969 := by
  unfold tailWord_1332737
  simp only [CollatzResearch.WordTrace]
  refine ⟨48608911772728937203484465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32405941181819291468989643 48608911772728937203484465)
  ·
    refine ⟨36456683829546702902613349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48608911772728937203484465 36456683829546702902613349)
    ·
      refine ⟨6835628218040006794240003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36456683829546702902613349 6835628218040006794240003)
      ·
        refine ⟨10253442327060010191360005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835628218040006794240003 10253442327060010191360005)
        ·
          refine ⟨1922520436323751910880001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10253442327060010191360005 1922520436323751910880001)
          ·
            refine ⟨1441890327242813933160001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922520436323751910880001 1441890327242813933160001)
            ·
              refine ⟨1081417745432110449870001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441890327242813933160001 1081417745432110449870001)
              ·
                refine ⟨811063309074082837402501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081417745432110449870001 811063309074082837402501)
                ·
                  refine ⟨152074370451390532012969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811063309074082837402501 152074370451390532012969)
                  ·
                    rfl

theorem cell22_1332737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_1332737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332737 prefixEnd_1332737 := by exact prefixLift 1332737
  have htrace : WordTrace (prefixWord ++ tailWord_1332737) baseStart_1332737 baseEnd_1332737 := by
    simpa [prefixWord, tailWord_1332737, baseEnd_1332737] using wordTrace_append hprefix tailTrace_1332737
  have hstable : (prefixWord ++ tailWord_1332737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332737).length < 2 ^ (prefixWord ++ tailWord_1332737).sum := by decide
  have hdescent : baseEnd_1332737 < baseStart_1332737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332748 : List Nat := [2, 2, 1, 2, 5, 2, 1, 7]
def baseStart_1332748 : Nat := 118140960795 + 1332748 * 2 ^ 59
def prefixEnd_1332748 : Nat := 4983230072969 + 3 ^ 40 * 1332748 * 2
def baseEnd_1332748 : Nat := 50691875208774581557097

theorem tailTrace_1332748 : CollatzResearch.WordTrace tailWord_1332748 prefixEnd_1332748 50691875208774581557097 := by
  unfold tailWord_1332748
  simp only [CollatzResearch.WordTrace]
  refine ⟨24304656487844543041067449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32406208650459390721423265 24304656487844543041067449)
  ·
    refine ⟨18228492365883407280800587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24304656487844543041067449 18228492365883407280800587)
    ·
      refine ⟨27342738548825110921200881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18228492365883407280800587 27342738548825110921200881)
      ·
        refine ⟨20507053911618833190900661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27342738548825110921200881 20507053911618833190900661)
        ·
          refine ⟨1922536304214265611646937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20507053911618833190900661 1922536304214265611646937)
          ·
            refine ⟨1441902228160699208735203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922536304214265611646937 1441902228160699208735203)
            ·
              refine ⟨2162853342241048813102805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441902228160699208735203 2162853342241048813102805)
              ·
                refine ⟨50691875208774581557097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2162853342241048813102805 50691875208774581557097)
                ·
                  rfl

theorem cell22_1332748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 7].length) (baseStart_1332748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332748 prefixEnd_1332748 := by exact prefixLift 1332748
  have htrace : WordTrace (prefixWord ++ tailWord_1332748) baseStart_1332748 baseEnd_1332748 := by
    simpa [prefixWord, tailWord_1332748, baseEnd_1332748] using wordTrace_append hprefix tailTrace_1332748
  have hstable : (prefixWord ++ tailWord_1332748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332748).length < 2 ^ (prefixWord ++ tailWord_1332748).sum := by decide
  have hdescent : baseEnd_1332748 < baseStart_1332748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332791 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_1332791 : Nat := 118140960795 + 1332791 * 2 ^ 59
def prefixEnd_1332791 : Nat := 4983230072969 + 3 ^ 40 * 1332791 * 2
def baseEnd_1332791 : Nat := 456241596657733455188741

theorem tailTrace_1332791 : CollatzResearch.WordTrace tailWord_1332791 prefixEnd_1332791 456241596657733455188741 := by
  unfold tailWord_1332791
  simp only [CollatzResearch.WordTrace]
  refine ⟨48610881314533304425950227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32407254209688869617300151 48610881314533304425950227)
  ·
    refine ⟨72916321971799956638925341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48610881314533304425950227 72916321971799956638925341)
    ·
      refine ⟨27343620739424983739597003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72916321971799956638925341 27343620739424983739597003)
      ·
        refine ⟨41015431109137475609395505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27343620739424983739597003 41015431109137475609395505)
        ·
          refine ⟨30761573331853106707046629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41015431109137475609395505 30761573331853106707046629)
          ·
            refine ⟨5767794999722457507571243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30761573331853106707046629 5767794999722457507571243)
            ·
              refine ⟨8651692499583686261356865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767794999722457507571243 8651692499583686261356865)
              ·
                refine ⟨6488769374687764696017649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8651692499583686261356865 6488769374687764696017649)
                ·
                  refine ⟨4866577031015823522013237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6488769374687764696017649 4866577031015823522013237)
                  ·
                    refine ⟨456241596657733455188741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4866577031015823522013237 456241596657733455188741)
                    ·
                      rfl

theorem cell22_1332791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_1332791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332791 prefixEnd_1332791 := by exact prefixLift 1332791
  have htrace : WordTrace (prefixWord ++ tailWord_1332791) baseStart_1332791 baseEnd_1332791 := by
    simpa [prefixWord, tailWord_1332791, baseEnd_1332791] using wordTrace_append hprefix tailTrace_1332791
  have hstable : (prefixWord ++ tailWord_1332791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332791).length < 2 ^ (prefixWord ++ tailWord_1332791).sum := by decide
  have hdescent : baseEnd_1332791 < baseStart_1332791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332793 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 5]
def baseStart_1332793 : Nat := 118140960795 + 1332793 * 2 ^ 59
def prefixEnd_1332793 : Nat := 4983230072969 + 3 ^ 40 * 1332793 * 2
def baseEnd_1332793 : Nat := 152080760432868705546245

theorem tailTrace_1332793 : CollatzResearch.WordTrace tailWord_1332793 prefixEnd_1332793 152080760432868705546245 := by
  unfold tailWord_1332793
  simp only [CollatzResearch.WordTrace]
  refine ⟨48610954260526058767523033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32407302840350705845015355 48610954260526058767523033)
  ·
    refine ⟨36458215695394544075642275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48610954260526058767523033 36458215695394544075642275)
    ·
      refine ⟨54687323543091816113463413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36458215695394544075642275 54687323543091816113463413)
      ·
        refine ⟨5126936582164857760637195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54687323543091816113463413 5126936582164857760637195)
        ·
          refine ⟨7690404873247286640955793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5126936582164857760637195 7690404873247286640955793)
          ·
            refine ⟨5767803654935464980716845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7690404873247286640955793 5767803654935464980716845)
            ·
              refine ⟨2162926370600799367768817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5767803654935464980716845 2162926370600799367768817)
              ·
                refine ⟨1622194777950599525826613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2162926370600799367768817 1622194777950599525826613)
                ·
                  refine ⟨152080760432868705546245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1622194777950599525826613 152080760432868705546245)
                  ·
                    rfl

theorem cell22_1332793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_1332793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332793 prefixEnd_1332793 := by exact prefixLift 1332793
  have htrace : WordTrace (prefixWord ++ tailWord_1332793) baseStart_1332793 baseEnd_1332793 := by
    simpa [prefixWord, tailWord_1332793, baseEnd_1332793] using wordTrace_append hprefix tailTrace_1332793
  have hstable : (prefixWord ++ tailWord_1332793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332793).length < 2 ^ (prefixWord ++ tailWord_1332793).sum := by decide
  have hdescent : baseEnd_1332793 < baseStart_1332793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332823 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 1, 4]
def baseStart_1332823 : Nat := 118140960795 + 1332823 * 2 ^ 59
def prefixEnd_1332823 : Nat := 4983230072969 + 3 ^ 40 * 1332823 * 2
def baseEnd_1332823 : Nat := 456252550911696038388643

theorem tailTrace_1332823 : CollatzResearch.WordTrace tailWord_1332823 prefixEnd_1332823 456252550911696038388643 := by
  unfold tailWord_1332823
  simp only [CollatzResearch.WordTrace]
  refine ⟨48612048450417373891115123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32408032300278249260743415 48612048450417373891115123)
  ·
    refine ⟨72918072675626060836672685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48612048450417373891115123 72918072675626060836672685)
    ·
      refine ⟨27344277253359772813752257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72918072675626060836672685 27344277253359772813752257)
      ·
        refine ⟨20508207940019829610314193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27344277253359772813752257 20508207940019829610314193)
        ·
          refine ⟨15381155955014872207735645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20508207940019829610314193 15381155955014872207735645)
          ·
            refine ⟨5767933483130577077900867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15381155955014872207735645 5767933483130577077900867)
            ·
              refine ⟨8651900224695865616851301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767933483130577077900867 8651900224695865616851301)
              ·
                refine ⟨1622231292130474803159619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8651900224695865616851301 1622231292130474803159619)
                ·
                  refine ⟨2433346938195712204739429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622231292130474803159619 2433346938195712204739429)
                  ·
                    refine ⟨456252550911696038388643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433346938195712204739429 456252550911696038388643)
                    ·
                      rfl

theorem cell22_1332823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_1332823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332823 prefixEnd_1332823 := by exact prefixLift 1332823
  have htrace : WordTrace (prefixWord ++ tailWord_1332823) baseStart_1332823 baseEnd_1332823 := by
    simpa [prefixWord, tailWord_1332823, baseEnd_1332823] using wordTrace_append hprefix tailTrace_1332823
  have hstable : (prefixWord ++ tailWord_1332823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332823).length < 2 ^ (prefixWord ++ tailWord_1332823).sum := by decide
  have hdescent : baseEnd_1332823 < baseStart_1332823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332840 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1332840 : Nat := 118140960795 + 1332840 * 2 ^ 59
def prefixEnd_1332840 : Nat := 4983230072969 + 3 ^ 40 * 1332840 * 2
def baseEnd_1332840 : Nat := 456258370359113660713591

theorem tailTrace_1332840 : CollatzResearch.WordTrace tailWord_1332840 prefixEnd_1332840 456258370359113660713591 := by
  unfold tailWord_1332840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24306334245677892897241987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32408445660903857196322649 24306334245677892897241987)
  ·
    refine ⟨36459501368516839345862981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24306334245677892897241987 36459501368516839345862981)
    ·
      refine ⟨6836156506596907377349309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36459501368516839345862981 6836156506596907377349309)
      ·
        refine ⟨2563558689973840266505991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6836156506596907377349309 2563558689973840266505991)
        ·
          refine ⟨3845338034960760399758987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563558689973840266505991 3845338034960760399758987)
          ·
            refine ⟨5768007052441140599638481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845338034960760399758987 5768007052441140599638481)
            ·
              refine ⟨4326005289330855449728861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5768007052441140599638481 4326005289330855449728861)
              ·
                refine ⟨1622251983499070793648323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4326005289330855449728861 1622251983499070793648323)
                ·
                  refine ⟨2433377975248606190472485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622251983499070793648323 2433377975248606190472485)
                  ·
                    refine ⟨456258370359113660713591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433377975248606190472485 456258370359113660713591)
                    ·
                      rfl

theorem cell22_1332840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1332840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332840 prefixEnd_1332840 := by exact prefixLift 1332840
  have htrace : WordTrace (prefixWord ++ tailWord_1332840) baseStart_1332840 baseEnd_1332840 := by
    simpa [prefixWord, tailWord_1332840, baseEnd_1332840] using wordTrace_append hprefix tailTrace_1332840
  have hstable : (prefixWord ++ tailWord_1332840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332840).length < 2 ^ (prefixWord ++ tailWord_1332840).sum := by decide
  have hdescent : baseEnd_1332840 < baseStart_1332840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332917 : List Nat := [1, 3, 3, 3, 3, 1, 1, 7]
def baseStart_1332917 : Nat := 118140960795 + 1332917 * 2 ^ 59
def prefixEnd_1332917 : Nat := 4983230072969 + 3 ^ 40 * 1332917 * 2
def baseEnd_1332917 : Nat := 50698303225856791837595

theorem tailTrace_1332917 : CollatzResearch.WordTrace tailWord_1332917 prefixEnd_1332917 50698303225856791837595 := by
  unfold tailWord_1332917
  simp only [CollatzResearch.WordTrace]
  refine ⟨48615476912076827945037005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32410317941384551963358003 48615476912076827945037005)
  ·
    refine ⟨18230803842028810479388877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48615476912076827945037005 18230803842028810479388877)
    ·
      refine ⟨6836551440760803929770829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18230803842028810479388877 6836551440760803929770829)
      ·
        refine ⟨2563706790285301473664061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6836551440760803929770829 2563706790285301473664061)
        ·
          refine ⟨961390046356988052624023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2563706790285301473664061 961390046356988052624023)
          ·
            refine ⟨1442085069535482078936035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961390046356988052624023 1442085069535482078936035)
            ·
              refine ⟨2163127604303223118404053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442085069535482078936035 2163127604303223118404053)
              ·
                refine ⟨50698303225856791837595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2163127604303223118404053 50698303225856791837595)
                ·
                  rfl

theorem cell22_1332917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 7].length) (baseStart_1332917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332917 prefixEnd_1332917 := by exact prefixLift 1332917
  have htrace : WordTrace (prefixWord ++ tailWord_1332917) baseStart_1332917 baseEnd_1332917 := by
    simpa [prefixWord, tailWord_1332917, baseEnd_1332917] using wordTrace_append hprefix tailTrace_1332917
  have hstable : (prefixWord ++ tailWord_1332917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332917).length < 2 ^ (prefixWord ++ tailWord_1332917).sum := by decide
  have hdescent : baseEnd_1332917 < baseStart_1332917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332928 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_1332928 : Nat := 118140960795 + 1332928 * 2 ^ 59
def prefixEnd_1332928 : Nat := 4983230072969 + 3 ^ 40 * 1332928 * 2
def baseEnd_1332928 : Nat := 152096164852503588171107

theorem tailTrace_1332928 : CollatzResearch.WordTrace tailWord_1332928 prefixEnd_1332928 152096164852503588171107 := by
  unfold tailWord_1332928
  simp only [CollatzResearch.WordTrace]
  refine ⟨24307939057518488411843719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32410585410024651215791625 24307939057518488411843719)
  ·
    refine ⟨36461908586277732617765579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24307939057518488411843719 36461908586277732617765579)
    ·
      refine ⟨54692862879416598926648369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36461908586277732617765579 54692862879416598926648369)
      ·
        refine ⟨41019647159562449194986277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54692862879416598926648369 41019647159562449194986277)
        ·
          refine ⟨7691183842417959224059927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41019647159562449194986277 7691183842417959224059927)
          ·
            refine ⟨11536775763626938836089891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7691183842417959224059927 11536775763626938836089891)
            ·
              refine ⟨17305163645440408254134837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11536775763626938836089891 17305163645440408254134837)
              ·
                refine ⟨1622359091760038273825141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17305163645440408254134837 1622359091760038273825141)
                ·
                  refine ⟨152096164852503588171107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1622359091760038273825141 152096164852503588171107)
                  ·
                    rfl

theorem cell22_1332928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_1332928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332928 prefixEnd_1332928 := by exact prefixLift 1332928
  have htrace : WordTrace (prefixWord ++ tailWord_1332928) baseStart_1332928 baseEnd_1332928 := by
    simpa [prefixWord, tailWord_1332928, baseEnd_1332928] using wordTrace_append hprefix tailTrace_1332928
  have hstable : (prefixWord ++ tailWord_1332928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332928).length < 2 ^ (prefixWord ++ tailWord_1332928).sum := by decide
  have hdescent : baseEnd_1332928 < baseStart_1332928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332934 : List Nat := [6, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1332934 : Nat := 118140960795 + 1332934 * 2 ^ 59
def prefixEnd_1332934 : Nat := 4983230072969 + 3 ^ 40 * 1332934 * 2
def baseEnd_1332934 : Nat := 50698949831125416540367

theorem tailTrace_1332934 : CollatzResearch.WordTrace tailWord_1332934 prefixEnd_1332934 50698949831125416540367 := by
  unfold tailWord_1332934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519253029781726245262683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32410731302010159898937237 1519253029781726245262683)
  ·
    refine ⟨2278879544672589367894025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519253029781726245262683 2278879544672589367894025)
    ·
      refine ⟨1709159658504442025920519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2278879544672589367894025 1709159658504442025920519)
      ·
        refine ⟨2563739487756663038880779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709159658504442025920519 2563739487756663038880779)
        ·
          refine ⟨3845609231634994558321169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563739487756663038880779 3845609231634994558321169)
          ·
            refine ⟨2884206923726245918740877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3845609231634994558321169 2884206923726245918740877)
            ·
              refine ⟨1081577596397342219527829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2884206923726245918740877 1081577596397342219527829)
              ·
                refine ⟨50698949831125416540367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1081577596397342219527829 50698949831125416540367)
                ·
                  rfl

theorem cell22_1332934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1332934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1332934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1332934 prefixEnd_1332934 := by exact prefixLift 1332934
  have htrace : WordTrace (prefixWord ++ tailWord_1332934) baseStart_1332934 baseEnd_1332934 := by
    simpa [prefixWord, tailWord_1332934, baseEnd_1332934] using wordTrace_append hprefix tailTrace_1332934
  have hstable : (prefixWord ++ tailWord_1332934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332934).length < 2 ^ (prefixWord ++ tailWord_1332934).sum := by decide
  have hdescent : baseEnd_1332934 < baseStart_1332934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333003 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 1, 6]
def baseStart_1333003 : Nat := 118140960795 + 1333003 * 2 ^ 59
def prefixEnd_1333003 : Nat := 4983230072969 + 3 ^ 40 * 1333003 * 2
def baseEnd_1333003 : Nat := 456314168590235568888091

theorem tailTrace_1333003 : CollatzResearch.WordTrace tailWord_1333003 prefixEnd_1333003 456314168590235568888091 := by
  unfold tailWord_1333003
  simp only [CollatzResearch.WordTrace]
  refine ⟨48618613589765264632667663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32412409059843509755111775 48618613589765264632667663)
  ·
    refine ⟨72927920384647896949001495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48618613589765264632667663 72927920384647896949001495)
    ·
      refine ⟨109391880576971845423502243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72927920384647896949001495 109391880576971845423502243)
      ·
        refine ⟨164087820865457768135253365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109391880576971845423502243 164087820865457768135253365)
        ·
          refine ⟨15383233206136665762680003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164087820865457768135253365 15383233206136665762680003)
          ·
            refine ⟨23074849809204998644020005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15383233206136665762680003 23074849809204998644020005)
            ·
              refine ⟨4326534339225937245753751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23074849809204998644020005 4326534339225937245753751)
              ·
                refine ⟨6489801508838905868630627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4326534339225937245753751 6489801508838905868630627)
                ·
                  refine ⟨9734702263258358802945941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6489801508838905868630627 9734702263258358802945941)
                  ·
                    refine ⟨456314168590235568888091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9734702263258358802945941 456314168590235568888091)
                    ·
                      rfl

theorem cell22_1333003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_1333003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333003 prefixEnd_1333003 := by exact prefixLift 1333003
  have htrace : WordTrace (prefixWord ++ tailWord_1333003) baseStart_1333003 baseEnd_1333003 := by
    simpa [prefixWord, tailWord_1333003, baseEnd_1333003] using wordTrace_append hprefix tailTrace_1333003
  have hstable : (prefixWord ++ tailWord_1333003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333003).length < 2 ^ (prefixWord ++ tailWord_1333003).sum := by decide
  have hdescent : baseEnd_1333003 < baseStart_1333003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333018 : List Nat := [3, 1, 1, 3, 2, 2, 10]
def baseStart_1333018 : Nat := 118140960795 + 1333018 * 2 ^ 59
def prefixEnd_1333018 : Nat := 4983230072969 + 3 ^ 40 * 1333018 * 2
def baseEnd_1333018 : Nat := 16900714940621501102335

theorem tailTrace_1333018 : CollatzResearch.WordTrace tailWord_1333018 prefixEnd_1333018 16900714940621501102335 := by
  unfold tailWord_1333018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154790171177730548615927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32412773789807281462975805 12154790171177730548615927)
  ·
    refine ⟨18232185256766595822923891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12154790171177730548615927 18232185256766595822923891)
    ·
      refine ⟨27348277885149893734385837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18232185256766595822923891 27348277885149893734385837)
      ·
        refine ⟨10255604206931210150394689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27348277885149893734385837 10255604206931210150394689)
        ·
          refine ⟨7691703155198407612796017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10255604206931210150394689 7691703155198407612796017)
          ·
            refine ⟨5768777366398805709597013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7691703155198407612796017 5768777366398805709597013)
            ·
              refine ⟨16900714940621501102335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5768777366398805709597013 16900714940621501102335)
              ·
                rfl

theorem cell22_1333018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 10].length) (baseStart_1333018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333018 prefixEnd_1333018 := by exact prefixLift 1333018
  have htrace : WordTrace (prefixWord ++ tailWord_1333018) baseStart_1333018 baseEnd_1333018 := by
    simpa [prefixWord, tailWord_1333018, baseEnd_1333018] using wordTrace_append hprefix tailTrace_1333018
  have hstable : (prefixWord ++ tailWord_1333018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333018).length < 2 ^ (prefixWord ++ tailWord_1333018).sum := by decide
  have hdescent : baseEnd_1333018 < baseStart_1333018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333020 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1333020 : Nat := 118140960795 + 1333020 * 2 ^ 59
def prefixEnd_1333020 : Nat := 4983230072969 + 3 ^ 40 * 1333020 * 2
def baseEnd_1333020 : Nat := 456319988037653191213039

theorem tailTrace_1333020 : CollatzResearch.WordTrace tailWord_1333020 prefixEnd_1333020 456319988037653191213039 := by
  unfold tailWord_1333020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24309616815351838268018257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32412822420469117690691009 24309616815351838268018257)
  ·
    refine ⟨18232212611513878701013693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24309616815351838268018257 18232212611513878701013693)
    ·
      refine ⟨6837079729317704512880135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18232212611513878701013693 6837079729317704512880135)
      ·
        refine ⟨10255619593976556769320203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6837079729317704512880135 10255619593976556769320203)
        ·
          refine ⟨15383429390964835153980305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10255619593976556769320203 15383429390964835153980305)
          ·
            refine ⟨11537572043223626365485229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15383429390964835153980305 11537572043223626365485229)
            ·
              refine ⟨4326589516208859887056961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11537572043223626365485229 4326589516208859887056961)
              ·
                refine ⟨3244942137156644915292721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326589516208859887056961 3244942137156644915292721)
                ·
                  refine ⟨2433706602867483686469541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3244942137156644915292721 2433706602867483686469541)
                  ·
                    refine ⟨456319988037653191213039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433706602867483686469541 456319988037653191213039)
                    ·
                      rfl

theorem cell22_1333020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1333020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333020 prefixEnd_1333020 := by exact prefixLift 1333020
  have htrace : WordTrace (prefixWord ++ tailWord_1333020) baseStart_1333020 baseEnd_1333020 := by
    simpa [prefixWord, tailWord_1333020, baseEnd_1333020] using wordTrace_append hprefix tailTrace_1333020
  have hstable : (prefixWord ++ tailWord_1333020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333020).length < 2 ^ (prefixWord ++ tailWord_1333020).sum := by decide
  have hdescent : baseEnd_1333020 < baseStart_1333020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333063 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 9]
def baseStart_1333063 : Nat := 118140960795 + 1333063 * 2 ^ 59
def prefixEnd_1333063 : Nat := 4983230072969 + 3 ^ 40 * 1333063 * 2
def baseEnd_1333063 : Nat := 152111569272138470795969

theorem tailTrace_1333063 : CollatzResearch.WordTrace tailWord_1333063 prefixEnd_1333063 152111569272138470795969 := by
  unfold tailWord_1333063
  simp only [CollatzResearch.WordTrace]
  refine ⟨48620801969547894879851843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32413867979698596586567895 48620801969547894879851843)
  ·
    refine ⟨72931202954321842319777765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48620801969547894879851843 72931202954321842319777765)
    ·
      refine ⟨13674600553935345434958331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72931202954321842319777765 13674600553935345434958331)
      ·
        refine ⟨20511900830903018152437497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13674600553935345434958331 20511900830903018152437497)
        ·
          refine ⟨15383925623177263614328123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20511900830903018152437497 15383925623177263614328123)
          ·
            refine ⟨23075888434765895421492185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15383925623177263614328123 23075888434765895421492185)
            ·
              refine ⟨17306916326074421566119139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23075888434765895421492185 17306916326074421566119139)
              ·
                refine ⟨25960374489111632349178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17306916326074421566119139 25960374489111632349178709)
                ·
                  refine ⟨152111569272138470795969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25960374489111632349178709 152111569272138470795969)
                  ·
                    rfl

theorem cell22_1333063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_1333063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333063 prefixEnd_1333063 := by exact prefixLift 1333063
  have htrace : WordTrace (prefixWord ++ tailWord_1333063) baseStart_1333063 baseEnd_1333063 := by
    simpa [prefixWord, tailWord_1333063, baseEnd_1333063] using wordTrace_append hprefix tailTrace_1333063
  have hstable : (prefixWord ++ tailWord_1333063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333063).length < 2 ^ (prefixWord ++ tailWord_1333063).sum := by decide
  have hdescent : baseEnd_1333063 < baseStart_1333063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333095 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1333095 : Nat := 118140960795 + 1333095 * 2 ^ 59
def prefixEnd_1333095 : Nat := 4983230072969 + 3 ^ 40 * 1333095 * 2
def baseEnd_1333095 : Nat := 456345662070377995587809

theorem tailTrace_1333095 : CollatzResearch.WordTrace tailWord_1333095 prefixEnd_1333095 456345662070377995587809 := by
  unfold tailWord_1333095
  simp only [CollatzResearch.WordTrace]
  refine ⟨48621969105431964345016739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32414646070287976230011159 48621969105431964345016739)
  ·
    refine ⟨72932953658147946517525109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48621969105431964345016739 72932953658147946517525109)
    ·
      refine ⟨6837464405451369986017979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72932953658147946517525109 6837464405451369986017979)
      ·
        refine ⟨10256196608177054979026969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6837464405451369986017979 10256196608177054979026969)
        ·
          refine ⟨7692147456132791234270227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10256196608177054979026969 7692147456132791234270227)
          ·
            refine ⟨11538221184199186851405341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692147456132791234270227 11538221184199186851405341)
            ·
              refine ⟨4326832944074695069277003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11538221184199186851405341 4326832944074695069277003)
              ·
                refine ⟨6490249416112042603915505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4326832944074695069277003 6490249416112042603915505)
                ·
                  refine ⟨4867687062084031952936629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6490249416112042603915505 4867687062084031952936629)
                  ·
                    refine ⟨456345662070377995587809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4867687062084031952936629 456345662070377995587809)
                    ·
                      rfl

theorem cell22_1333095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1333095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333095 prefixEnd_1333095 := by exact prefixLift 1333095
  have htrace : WordTrace (prefixWord ++ tailWord_1333095) baseStart_1333095 baseEnd_1333095 := by
    simpa [prefixWord, tailWord_1333095, baseEnd_1333095] using wordTrace_append hprefix tailTrace_1333095
  have hstable : (prefixWord ++ tailWord_1333095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333095).length < 2 ^ (prefixWord ++ tailWord_1333095).sum := by decide
  have hdescent : baseEnd_1333095 < baseStart_1333095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333118 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1333118 : Nat := 118140960795 + 1333118 * 2 ^ 59
def prefixEnd_1333118 : Nat := 4983230072969 + 3 ^ 40 * 1333118 * 2
def baseEnd_1333118 : Nat := 456353535440413602262739

theorem tailTrace_1333118 : CollatzResearch.WordTrace tailWord_1333118 prefixEnd_1333118 456353535440413602262739 := by
  unfold tailWord_1333118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077850998043579909138001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32415205322899092848736005 6077850998043579909138001)
  ·
    refine ⟨4558388248532684931853501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6077850998043579909138001 4558388248532684931853501)
    ·
      refine ⟨1709395593199756849445063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4558388248532684931853501 1709395593199756849445063)
      ·
        refine ⟨2564093389799635274167595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709395593199756849445063 2564093389799635274167595)
        ·
          refine ⟨3846140084699452911251393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564093389799635274167595 3846140084699452911251393)
          ·
            refine ⟨2884605063524589683438545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3846140084699452911251393 2884605063524589683438545)
            ·
              refine ⟨2163453797643442262578909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884605063524589683438545 2163453797643442262578909)
              ·
                refine ⟨811295174116290848467091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2163453797643442262578909 811295174116290848467091)
                ·
                  refine ⟨1216942761174436272700637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811295174116290848467091 1216942761174436272700637)
                  ·
                    refine ⟨456353535440413602262739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216942761174436272700637 456353535440413602262739)
                    ·
                      rfl

theorem cell22_1333118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1333118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333118 prefixEnd_1333118 := by exact prefixLift 1333118
  have htrace : WordTrace (prefixWord ++ tailWord_1333118) baseStart_1333118 baseEnd_1333118 := by
    simpa [prefixWord, tailWord_1333118, baseEnd_1333118] using wordTrace_append hprefix tailTrace_1333118
  have hstable : (prefixWord ++ tailWord_1333118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333118).length < 2 ^ (prefixWord ++ tailWord_1333118).sum := by decide
  have hdescent : baseEnd_1333118 < baseStart_1333118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333157 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_1333157 : Nat := 118140960795 + 1333157 * 2 ^ 59
def prefixEnd_1333157 : Nat := 4983230072969 + 3 ^ 40 * 1333157 * 2
def baseEnd_1333157 : Nat := 456366885937430500537619

theorem tailTrace_1333157 : CollatzResearch.WordTrace tailWord_1333157 prefixEnd_1333157 456366885937430500537619 := by
  unfold tailWord_1333157
  simp only [CollatzResearch.WordTrace]
  refine ⟨48624230431207348933773725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32416153620804899289182483 48624230431207348933773725)
  ·
    refine ⟨18234086411702755850165147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48624230431207348933773725 18234086411702755850165147)
    ·
      refine ⟨27351129617554133775247721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18234086411702755850165147 27351129617554133775247721)
      ·
        refine ⟨20513347213165600331435791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27351129617554133775247721 20513347213165600331435791)
        ·
          refine ⟨30770020819748400497153687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20513347213165600331435791 30770020819748400497153687)
          ·
            refine ⟨46155031229622600745730531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30770020819748400497153687 46155031229622600745730531)
            ·
              refine ⟨69232546844433901118595797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46155031229622600745730531 69232546844433901118595797)
              ·
                refine ⟨1622637816666419557467089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69232546844433901118595797 1622637816666419557467089)
                ·
                  refine ⟨1216978362499814668100317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1622637816666419557467089 1216978362499814668100317)
                  ·
                    refine ⟨456366885937430500537619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216978362499814668100317 456366885937430500537619)
                    ·
                      rfl

theorem cell22_1333157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_1333157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333157 prefixEnd_1333157 := by exact prefixLift 1333157
  have htrace : WordTrace (prefixWord ++ tailWord_1333157) baseStart_1333157 baseEnd_1333157 := by
    simpa [prefixWord, tailWord_1333157, baseEnd_1333157] using wordTrace_append hprefix tailTrace_1333157
  have hstable : (prefixWord ++ tailWord_1333157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333157).length < 2 ^ (prefixWord ++ tailWord_1333157).sum := by decide
  have hdescent : baseEnd_1333157 < baseStart_1333157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333253 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_1333253 : Nat := 118140960795 + 1333253 * 2 ^ 59
def prefixEnd_1333253 : Nat := 4983230072969 + 3 ^ 40 * 1333253 * 2
def baseEnd_1333253 : Nat := 456399748699318250137325

theorem tailTrace_1333253 : CollatzResearch.WordTrace tailWord_1333253 prefixEnd_1333253 456399748699318250137325 := by
  unfold tailWord_1333253
  simp only [CollatzResearch.WordTrace]
  refine ⟨48627731838859557329268413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32418487892573038219512275 48627731838859557329268413)
  ·
    refine ⟨18235399439572333998475655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48627731838859557329268413 18235399439572333998475655)
    ·
      refine ⟨27353099159358500997713483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18235399439572333998475655 27353099159358500997713483)
      ·
        refine ⟨41029648739037751496570225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27353099159358500997713483 41029648739037751496570225)
        ·
          refine ⟨30772236554278313622427669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41029648739037751496570225 30772236554278313622427669)
          ·
            refine ⟨1442448588481795951051297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30772236554278313622427669 1442448588481795951051297)
            ·
              refine ⟨1081836441361346963288473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442448588481795951051297 1081836441361346963288473)
              ·
                refine ⟨811377331021010222466355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081836441361346963288473 811377331021010222466355)
                ·
                  refine ⟨1217065996531515333699533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811377331021010222466355 1217065996531515333699533)
                  ·
                    refine ⟨456399748699318250137325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217065996531515333699533 456399748699318250137325)
                    ·
                      rfl

theorem cell22_1333253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_1333253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333253 prefixEnd_1333253 := by exact prefixLift 1333253
  have htrace : WordTrace (prefixWord ++ tailWord_1333253) baseStart_1333253 baseEnd_1333253 := by
    simpa [prefixWord, tailWord_1333253, baseEnd_1333253] using wordTrace_append hprefix tailTrace_1333253
  have hstable : (prefixWord ++ tailWord_1333253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333253).length < 2 ^ (prefixWord ++ tailWord_1333253).sum := by decide
  have hdescent : baseEnd_1333253 < baseStart_1333253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333262 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1333262 : Nat := 118140960795 + 1333262 * 2 ^ 59
def prefixEnd_1333262 : Nat := 4983230072969 + 3 ^ 40 * 1333262 * 2
def baseEnd_1333262 : Nat := 456402829583245226662297

theorem tailTrace_1333262 : CollatzResearch.WordTrace tailWord_1333262 prefixEnd_1333262 456402829583245226662297 := by
  unfold tailWord_1333262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078507511978368983293255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32418706730551301244230693 6078507511978368983293255)
  ·
    refine ⟨9117761267967553474939883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6078507511978368983293255 9117761267967553474939883)
    ·
      refine ⟨13676641901951330212409825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9117761267967553474939883 13676641901951330212409825)
      ·
        refine ⟨10257481426463497659307369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13676641901951330212409825 10257481426463497659307369)
        ·
          refine ⟨7693111069847623244480527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10257481426463497659307369 7693111069847623244480527)
          ·
            refine ⟨11539666604771434866720791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693111069847623244480527 11539666604771434866720791)
            ·
              refine ⟨17309499907157152300081187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11539666604771434866720791 17309499907157152300081187)
              ·
                refine ⟨25964249860735728450121781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17309499907157152300081187 25964249860735728450121781)
                ·
                  refine ⟨2434148424443974542198917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25964249860735728450121781 2434148424443974542198917)
                  ·
                    refine ⟨456402829583245226662297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2434148424443974542198917 456402829583245226662297)
                    ·
                      rfl

theorem cell22_1333262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1333262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333262 prefixEnd_1333262 := by exact prefixLift 1333262
  have htrace : WordTrace (prefixWord ++ tailWord_1333262) baseStart_1333262 baseEnd_1333262 := by
    simpa [prefixWord, tailWord_1333262, baseEnd_1333262] using wordTrace_append hprefix tailTrace_1333262
  have hstable : (prefixWord ++ tailWord_1333262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333262).length < 2 ^ (prefixWord ++ tailWord_1333262).sum := by decide
  have hdescent : baseEnd_1333262 < baseStart_1333262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333277 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 8]
def baseStart_1333277 : Nat := 118140960795 + 1333277 * 2 ^ 59
def prefixEnd_1333277 : Nat := 4983230072969 + 3 ^ 40 * 1333277 * 2
def baseEnd_1333277 : Nat := 152135988129930062512417

theorem tailTrace_1333277 : CollatzResearch.WordTrace tailWord_1333277 prefixEnd_1333277 152135988129930062512417 := by
  unfold tailWord_1333277
  simp only [CollatzResearch.WordTrace]
  refine ⟨48628607190772609428142085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32419071460515072952094723 48628607190772609428142085)
  ·
    refine ⟨9117863848269864267776641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48628607190772609428142085 9117863848269864267776641)
    ·
      refine ⟨6838397886202398200832481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9117863848269864267776641 6838397886202398200832481)
      ·
        refine ⟨5128798414651798650624361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6838397886202398200832481 5128798414651798650624361)
        ·
          refine ⟨3846598810988848987968271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5128798414651798650624361 3846598810988848987968271)
          ·
            refine ⟨5769898216483273481952407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846598810988848987968271 5769898216483273481952407)
            ·
              refine ⟨8654847324724910222928611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5769898216483273481952407 8654847324724910222928611)
              ·
                refine ⟨12982270987087365334392917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8654847324724910222928611 12982270987087365334392917)
                ·
                  refine ⟨152135988129930062512417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12982270987087365334392917 152135988129930062512417)
                  ·
                    rfl

theorem cell22_1333277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_1333277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333277 prefixEnd_1333277 := by exact prefixLift 1333277
  have htrace : WordTrace (prefixWord ++ tailWord_1333277) baseStart_1333277 baseEnd_1333277 := by
    simpa [prefixWord, tailWord_1333277, baseEnd_1333277] using wordTrace_append hprefix tailTrace_1333277
  have hstable : (prefixWord ++ tailWord_1333277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333277).length < 2 ^ (prefixWord ++ tailWord_1333277).sum := by decide
  have hdescent : baseEnd_1333277 < baseStart_1333277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333296 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 1, 4]
def baseStart_1333296 : Nat := 118140960795 + 1333296 * 2 ^ 59
def prefixEnd_1333296 : Nat := 4983230072969 + 3 ^ 40 * 1333296 * 2
def baseEnd_1333296 : Nat := 456414468478080471312193

theorem tailTrace_1333296 : CollatzResearch.WordTrace tailWord_1333296 prefixEnd_1333296 456414468478080471312193 := by
  unfold tailWord_1333296
  simp only [CollatzResearch.WordTrace]
  refine ⟨24314650088851887836541871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32419533451802517115389161 24314650088851887836541871)
  ·
    refine ⟨36471975133277831754812807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24314650088851887836541871 36471975133277831754812807)
    ·
      refine ⟨54707962699916747632219211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36471975133277831754812807 54707962699916747632219211)
      ·
        refine ⟨82061944049875121448328817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54707962699916747632219211 82061944049875121448328817)
        ·
          refine ⟨61546458037406341086246613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82061944049875121448328817 61546458037406341086246613)
          ·
            refine ⟨1442495110251711119208905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61546458037406341086246613 1442495110251711119208905)
            ·
              refine ⟨1081871332688783339406679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442495110251711119208905 1081871332688783339406679)
              ·
                refine ⟨1622806999033175009110019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081871332688783339406679 1622806999033175009110019)
                ·
                  refine ⟨2434210498549762513665029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622806999033175009110019 2434210498549762513665029)
                  ·
                    refine ⟨456414468478080471312193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2434210498549762513665029 456414468478080471312193)
                    ·
                      rfl

theorem cell22_1333296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_1333296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333296 prefixEnd_1333296 := by exact prefixLift 1333296
  have htrace : WordTrace (prefixWord ++ tailWord_1333296) baseStart_1333296 baseEnd_1333296 := by
    simpa [prefixWord, tailWord_1333296, baseEnd_1333296] using wordTrace_append hprefix tailTrace_1333296
  have hstable : (prefixWord ++ tailWord_1333296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333296).length < 2 ^ (prefixWord ++ tailWord_1333296).sum := by decide
  have hdescent : baseEnd_1333296 < baseStart_1333296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333309 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1333309 : Nat := 118140960795 + 1333309 * 2 ^ 59
def prefixEnd_1333309 : Nat := 4983230072969 + 3 ^ 40 * 1333309 * 2
def baseEnd_1333309 : Nat := 456418918643752770737153

theorem tailTrace_1333309 : CollatzResearch.WordTrace tailWord_1333309 prefixEnd_1333309 456418918643752770737153 := by
  unfold tailWord_1333309
  simp only [CollatzResearch.WordTrace]
  refine ⟨48629774326656678893306981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32419849551104452595537987 48629774326656678893306981)
  ·
    refine ⟨9118082686248127292495059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48629774326656678893306981 9118082686248127292495059)
    ·
      refine ⟨13677124029372190938742589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9118082686248127292495059 13677124029372190938742589)
      ·
        refine ⟨5128921511014571602028471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13677124029372190938742589 5128921511014571602028471)
        ·
          refine ⟨7693382266521857403042707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128921511014571602028471 7693382266521857403042707)
          ·
            refine ⟨11540073399782786104564061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693382266521857403042707 11540073399782786104564061)
            ·
              refine ⟨4327527524918544789211523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11540073399782786104564061 4327527524918544789211523)
              ·
                refine ⟨6491291287377817183817285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327527524918544789211523 6491291287377817183817285)
                ·
                  refine ⟨1217117116383340721965741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6491291287377817183817285 1217117116383340721965741)
                  ·
                    refine ⟨456418918643752770737153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217117116383340721965741 456418918643752770737153)
                    ·
                      rfl

theorem cell22_1333309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1333309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333309 prefixEnd_1333309 := by exact prefixLift 1333309
  have htrace : WordTrace (prefixWord ++ tailWord_1333309) baseStart_1333309 baseEnd_1333309 := by
    simpa [prefixWord, tailWord_1333309, baseEnd_1333309] using wordTrace_append hprefix tailTrace_1333309
  have hstable : (prefixWord ++ tailWord_1333309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333309).length < 2 ^ (prefixWord ++ tailWord_1333309).sum := by decide
  have hdescent : baseEnd_1333309 < baseStart_1333309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333367 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 7]
def baseStart_1333367 : Nat := 118140960795 + 1333367 * 2 ^ 59
def prefixEnd_1333367 : Nat := 4983230072969 + 3 ^ 40 * 1333367 * 2
def baseEnd_1333367 : Nat := 152146257743019984262325

theorem tailTrace_1333367 : CollatzResearch.WordTrace tailWord_1333367 prefixEnd_1333367 152146257743019984262325 := by
  unfold tailWord_1333367
  simp only [CollatzResearch.WordTrace]
  refine ⟨48631889760446554798918355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32421259840297703199278903 48631889760446554798918355)
  ·
    refine ⟨72947834640669832198377533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48631889760446554798918355 72947834640669832198377533)
    ·
      refine ⟨27355437990251187074391575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72947834640669832198377533 27355437990251187074391575)
      ·
        refine ⟨41033156985376780611587363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27355437990251187074391575 41033156985376780611587363)
        ·
          refine ⟨61549735478065170917381045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41033156985376780611587363 61549735478065170917381045)
          ·
            refine ⟨5770287701068609773504473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61549735478065170917381045 5770287701068609773504473)
            ·
              refine ⟨4327715775801457330128355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5770287701068609773504473 4327715775801457330128355)
              ·
                refine ⟨6491573663702185995192533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327715775801457330128355 6491573663702185995192533)
                ·
                  refine ⟨152146257743019984262325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6491573663702185995192533 152146257743019984262325)
                  ·
                    rfl

theorem cell22_1333367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 7].length) (baseStart_1333367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333367 prefixEnd_1333367 := by exact prefixLift 1333367
  have htrace : WordTrace (prefixWord ++ tailWord_1333367) baseStart_1333367 baseEnd_1333367 := by
    simpa [prefixWord, tailWord_1333367, baseEnd_1333367] using wordTrace_append hprefix tailTrace_1333367
  have hstable : (prefixWord ++ tailWord_1333367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333367).length < 2 ^ (prefixWord ++ tailWord_1333367).sum := by decide
  have hdescent : baseEnd_1333367 < baseStart_1333367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333418 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_1333418 : Nat := 118140960795 + 1333418 * 2 ^ 59
def prefixEnd_1333418 : Nat := 4983230072969 + 3 ^ 40 * 1333418 * 2
def baseEnd_1333418 : Nat := 152152077190437606587273

theorem tailTrace_1333418 : CollatzResearch.WordTrace tailWord_1333418 prefixEnd_1333418 152152077190437606587273 := by
  unfold tailWord_1333418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158437470815447627256227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32422499922174527006016605 12158437470815447627256227)
  ·
    refine ⟨18237656206223171440884341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12158437470815447627256227 18237656206223171440884341)
    ·
      refine ⟨1709780269333422322582907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18237656206223171440884341 1709780269333422322582907)
      ·
        refine ⟨2564670404000133483874361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709780269333422322582907 2564670404000133483874361)
        ·
          refine ⟨1923502803000100112905771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564670404000133483874361 1923502803000100112905771)
          ·
            refine ⟨2885254204500150169358657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923502803000100112905771 2885254204500150169358657)
            ·
              refine ⟨2163940653375112627018993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885254204500150169358657 2163940653375112627018993)
              ·
                refine ⟨1622955490031334470264245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163940653375112627018993 1622955490031334470264245)
                ·
                  refine ⟨152152077190437606587273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1622955490031334470264245 152152077190437606587273)
                  ·
                    rfl

theorem cell22_1333418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_1333418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333418 prefixEnd_1333418 := by exact prefixLift 1333418
  have htrace : WordTrace (prefixWord ++ tailWord_1333418) baseStart_1333418 baseEnd_1333418 := by
    simpa [prefixWord, tailWord_1333418, baseEnd_1333418] using wordTrace_append hprefix tailTrace_1333418
  have hstable : (prefixWord ++ tailWord_1333418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333418).length < 2 ^ (prefixWord ++ tailWord_1333418).sum := by decide
  have hdescent : baseEnd_1333418 < baseStart_1333418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333422 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1333422 : Nat := 118140960795 + 1333422 * 2 ^ 59
def prefixEnd_1333422 : Nat := 4983230072969 + 3 ^ 40 * 1333422 * 2
def baseEnd_1333422 : Nat := 456457600853058142661807

theorem tailTrace_1333422 : CollatzResearch.WordTrace tailWord_1333422 prefixEnd_1333422 456457600853058142661807 := by
  unfold tailWord_1333422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6079236971905912399021315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32422597183498199461447013 6079236971905912399021315)
  ·
    refine ⟨9118855457858868598531973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6079236971905912399021315 9118855457858868598531973)
    ·
      refine ⟨1709785398348537862224745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9118855457858868598531973 1709785398348537862224745)
      ·
        refine ⟨1282339048761403396668559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1709785398348537862224745 1282339048761403396668559)
        ·
          refine ⟨1923508573142105095002839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282339048761403396668559 1923508573142105095002839)
          ·
            refine ⟨2885262859713157642504259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923508573142105095002839 2885262859713157642504259)
            ·
              refine ⟨4327894289569736463756389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885262859713157642504259 4327894289569736463756389)
              ·
                refine ⟨811480179294325586954323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4327894289569736463756389 811480179294325586954323)
                ·
                  refine ⟨1217220268941488380431485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811480179294325586954323 1217220268941488380431485)
                  ·
                    refine ⟨456457600853058142661807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217220268941488380431485 456457600853058142661807)
                    ·
                      rfl

theorem cell22_1333422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1333422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333422 prefixEnd_1333422 := by exact prefixLift 1333422
  have htrace : WordTrace (prefixWord ++ tailWord_1333422) baseStart_1333422 baseEnd_1333422 := by
    simpa [prefixWord, tailWord_1333422, baseEnd_1333422] using wordTrace_append hprefix tailTrace_1333422
  have hstable : (prefixWord ++ tailWord_1333422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333422).length < 2 ^ (prefixWord ++ tailWord_1333422).sum := by decide
  have hdescent : baseEnd_1333422 < baseStart_1333422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333427 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_1333427 : Nat := 118140960795 + 1333427 * 2 ^ 59
def prefixEnd_1333427 : Nat := 4983230072969 + 3 ^ 40 * 1333427 * 2
def baseEnd_1333427 : Nat := 456459312455239796286791

theorem tailTrace_1333427 : CollatzResearch.WordTrace tailWord_1333427 prefixEnd_1333427 456459312455239796286791 := by
  unfold tailWord_1333427
  simp only [CollatzResearch.WordTrace]
  refine ⟨48634078140229185046102535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32422718760152790030735023 48634078140229185046102535)
  ·
    refine ⟨72951117210343777569153803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48634078140229185046102535 72951117210343777569153803)
    ·
      refine ⟨109426675815515666353730705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72951117210343777569153803 109426675815515666353730705)
      ·
        refine ⟨82070006861636749765298029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109426675815515666353730705 82070006861636749765298029)
        ·
          refine ⟨30776252573113781161986761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82070006861636749765298029 30776252573113781161986761)
          ·
            refine ⟨23082189429835335871490071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30776252573113781161986761 23082189429835335871490071)
            ·
              refine ⟨34623284144753003807235107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23082189429835335871490071 34623284144753003807235107)
              ·
                refine ⟨51934926217129505710852661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34623284144753003807235107 51934926217129505710852661)
                ·
                  refine ⟨4868899332855891160392437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51934926217129505710852661 4868899332855891160392437)
                  ·
                    refine ⟨456459312455239796286791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4868899332855891160392437 456459312455239796286791)
                    ·
                      rfl

theorem cell22_1333427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_1333427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333427 prefixEnd_1333427 := by exact prefixLift 1333427
  have htrace : WordTrace (prefixWord ++ tailWord_1333427) baseStart_1333427 baseEnd_1333427 := by
    simpa [prefixWord, tailWord_1333427, baseEnd_1333427] using wordTrace_append hprefix tailTrace_1333427
  have hstable : (prefixWord ++ tailWord_1333427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333427).length < 2 ^ (prefixWord ++ tailWord_1333427).sum := by decide
  have hdescent : baseEnd_1333427 < baseStart_1333427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333457 : List Nat := [1, 2, 2, 1, 2, 2, 2, 10]
def baseStart_1333457 : Nat := 118140960795 + 1333457 * 2 ^ 59
def prefixEnd_1333457 : Nat := 4983230072969 + 3 ^ 40 * 1333457 * 2
def baseEnd_1333457 : Nat := 50718842452036635337411

theorem tailTrace_1333457 : CollatzResearch.WordTrace tailWord_1333457 prefixEnd_1333457 50718842452036635337411 := by
  unfold tailWord_1333457
  simp only [CollatzResearch.WordTrace]
  refine ⟨48635172330120500169694625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32423448220080333446463083 48635172330120500169694625)
  ·
    refine ⟨36476379247590375127270969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48635172330120500169694625 36476379247590375127270969)
    ·
      refine ⟨27357284435692781345453227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36476379247590375127270969 27357284435692781345453227)
      ·
        refine ⟨41035926653539172018179841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27357284435692781345453227 41035926653539172018179841)
        ·
          refine ⟨30776944990154379013634881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41035926653539172018179841 30776944990154379013634881)
          ·
            refine ⟨23082708742615784260226161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30776944990154379013634881 23082708742615784260226161)
            ·
              refine ⟨17312031556961838195169621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23082708742615784260226161 17312031556961838195169621)
              ·
                refine ⟨50718842452036635337411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17312031556961838195169621 50718842452036635337411)
                ·
                  rfl

theorem cell22_1333457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 10].length) (baseStart_1333457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333457 prefixEnd_1333457 := by exact prefixLift 1333457
  have htrace : WordTrace (prefixWord ++ tailWord_1333457) baseStart_1333457 baseEnd_1333457 := by
    simpa [prefixWord, tailWord_1333457, baseEnd_1333457] using wordTrace_append hprefix tailTrace_1333457
  have hstable : (prefixWord ++ tailWord_1333457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333457).length < 2 ^ (prefixWord ++ tailWord_1333457).sum := by decide
  have hdescent : baseEnd_1333457 < baseStart_1333457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333508 : List Nat := [2, 3, 2, 2, 3, 2, 2, 6]
def baseStart_1333508 : Nat := 118140960795 + 1333508 * 2 ^ 59
def prefixEnd_1333508 : Nat := 4983230072969 + 3 ^ 40 * 1333508 * 2
def baseEnd_1333508 : Nat := 50720782267842509445727

theorem tailTrace_1333508 : CollatzResearch.WordTrace tailWord_1333508 prefixEnd_1333508 50720782267842509445727 := by
  unfold tailWord_1333508
  simp only [CollatzResearch.WordTrace]
  refine ⟨24318516226467867939900589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32424688301957157253200785 24318516226467867939900589)
  ·
    refine ⟨9119443584925450477462721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24318516226467867939900589 9119443584925450477462721)
    ·
      refine ⟨6839582688694087858097041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9119443584925450477462721 6839582688694087858097041)
      ·
        refine ⟨5129687016520565893572781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6839582688694087858097041 5129687016520565893572781)
        ·
          refine ⟨1923632631195212210089793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5129687016520565893572781 1923632631195212210089793)
          ·
            refine ⟨1442724473396409157567345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1923632631195212210089793 1442724473396409157567345)
            ·
              refine ⟨1082043355047306868175509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442724473396409157567345 1082043355047306868175509)
              ·
                refine ⟨50720782267842509445727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1082043355047306868175509 50720782267842509445727)
                ·
                  rfl

theorem cell22_1333508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 6].length) (baseStart_1333508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333508 prefixEnd_1333508 := by exact prefixLift 1333508
  have htrace : WordTrace (prefixWord ++ tailWord_1333508) baseStart_1333508 baseEnd_1333508 := by
    simpa [prefixWord, tailWord_1333508, baseEnd_1333508] using wordTrace_append hprefix tailTrace_1333508
  have hstable : (prefixWord ++ tailWord_1333508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333508).length < 2 ^ (prefixWord ++ tailWord_1333508).sum := by decide
  have hdescent : baseEnd_1333508 < baseStart_1333508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333564 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_1333564 : Nat := 118140960795 + 1333564 * 2 ^ 59
def prefixEnd_1333564 : Nat := 4983230072969 + 3 ^ 40 * 1333564 * 2
def baseEnd_1333564 : Nat := 152168736785005701870457

theorem tailTrace_1333564 : CollatzResearch.WordTrace tailWord_1333564 prefixEnd_1333564 152168736785005701870457 := by
  unfold tailWord_1333564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24319537470366428721919873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32426049960488571629226497 24319537470366428721919873)
  ·
    refine ⟨18239653102774821541439905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24319537470366428721919873 18239653102774821541439905)
    ·
      refine ⟨13679739827081116156079929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18239653102774821541439905 13679739827081116156079929)
      ·
        refine ⟨10259804870310837117059947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13679739827081116156079929 10259804870310837117059947)
        ·
          refine ⟨15389707305466255675589921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10259804870310837117059947 15389707305466255675589921)
          ·
            refine ⟨11542280479099691756692441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15389707305466255675589921 11542280479099691756692441)
            ·
              refine ⟨8656710359324768817519331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11542280479099691756692441 8656710359324768817519331)
              ·
                refine ⟨12985065538987153226278997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8656710359324768817519331 12985065538987153226278997)
                ·
                  refine ⟨152168736785005701870457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12985065538987153226278997 152168736785005701870457)
                  ·
                    rfl

theorem cell22_1333564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_1333564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333564 prefixEnd_1333564 := by exact prefixLift 1333564
  have htrace : WordTrace (prefixWord ++ tailWord_1333564) baseStart_1333564 baseEnd_1333564 := by
    simpa [prefixWord, tailWord_1333564, baseEnd_1333564] using wordTrace_append hprefix tailTrace_1333564
  have hstable : (prefixWord ++ tailWord_1333564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333564).length < 2 ^ (prefixWord ++ tailWord_1333564).sum := by decide
  have hdescent : baseEnd_1333564 < baseStart_1333564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333594 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1333594 : Nat := 118140960795 + 1333594 * 2 ^ 59
def prefixEnd_1333594 : Nat := 4983230072969 + 3 ^ 40 * 1333594 * 2
def baseEnd_1333594 : Nat := 456516479968107027361279

theorem tailTrace_1333594 : CollatzResearch.WordTrace tailWord_1333594 prefixEnd_1333594 456516479968107027361279 := by
  unfold tailWord_1333594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160042282656043141857959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32426779420416115044954557 12160042282656043141857959)
  ·
    refine ⟨18240063423984064712786939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12160042282656043141857959 18240063423984064712786939)
    ·
      refine ⟨27360095135976097069180409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18240063423984064712786939 27360095135976097069180409)
      ·
        refine ⟨20520071351982072801885307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27360095135976097069180409 20520071351982072801885307)
        ·
          refine ⟨30780107027973109202827961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20520071351982072801885307 30780107027973109202827961)
          ·
            refine ⟨23085080270979831902120971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30780107027973109202827961 23085080270979831902120971)
            ·
              refine ⟨34627620406469747853181457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23085080270979831902120971 34627620406469747853181457)
              ·
                refine ⟨25970715304852310889886093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34627620406469747853181457 25970715304852310889886093)
                ·
                  refine ⟨9739018239319616583707285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25970715304852310889886093 9739018239319616583707285)
                  ·
                    refine ⟨456516479968107027361279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9739018239319616583707285 456516479968107027361279)
                    ·
                      rfl

theorem cell22_1333594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1333594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333594 prefixEnd_1333594 := by exact prefixLift 1333594
  have htrace : WordTrace (prefixWord ++ tailWord_1333594) baseStart_1333594 baseEnd_1333594 := by
    simpa [prefixWord, tailWord_1333594, baseEnd_1333594] using wordTrace_append hprefix tailTrace_1333594
  have hstable : (prefixWord ++ tailWord_1333594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333594).length < 2 ^ (prefixWord ++ tailWord_1333594).sum := by decide
  have hdescent : baseEnd_1333594 < baseStart_1333594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333613 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_1333613 : Nat := 118140960795 + 1333613 * 2 ^ 59
def prefixEnd_1333613 : Nat := 4983230072969 + 3 ^ 40 * 1333613 * 2
def baseEnd_1333613 : Nat := 456522984056397311136221

theorem tailTrace_1333613 : CollatzResearch.WordTrace tailWord_1333613 prefixEnd_1333613 456522984056397311136221 := by
  unfold tailWord_1333613
  simp only [CollatzResearch.WordTrace]
  refine ⟨48640862117555338812373493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32427241411703559208248995 48640862117555338812373493)
  ·
    refine ⟨4560080823520813013660015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48640862117555338812373493 4560080823520813013660015)
    ·
      refine ⟨6840121235281219520490023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560080823520813013660015 6840121235281219520490023)
      ·
        refine ⟨10260181852921829280735035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840121235281219520490023 10260181852921829280735035)
        ·
          refine ⟨15390272779382743921102553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10260181852921829280735035 15390272779382743921102553)
          ·
            refine ⟨11542704584537057940826915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15390272779382743921102553 11542704584537057940826915)
            ·
              refine ⟨17314056876805586911240373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542704584537057940826915 17314056876805586911240373)
              ·
                refine ⟨1623192832200523772928785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17314056876805586911240373 1623192832200523772928785)
                ·
                  refine ⟨1217394624150392829696589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623192832200523772928785 1217394624150392829696589)
                  ·
                    refine ⟨456522984056397311136221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217394624150392829696589 456522984056397311136221)
                    ·
                      rfl

theorem cell22_1333613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_1333613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333613 prefixEnd_1333613 := by exact prefixLift 1333613
  have htrace : WordTrace (prefixWord ++ tailWord_1333613) baseStart_1333613 baseEnd_1333613 := by
    simpa [prefixWord, tailWord_1333613, baseEnd_1333613] using wordTrace_append hprefix tailTrace_1333613
  have hstable : (prefixWord ++ tailWord_1333613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333613).length < 2 ^ (prefixWord ++ tailWord_1333613).sum := by decide
  have hdescent : baseEnd_1333613 < baseStart_1333613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333634 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1333634 : Nat := 118140960795 + 1333634 * 2 ^ 59
def prefixEnd_1333634 : Nat := 4983230072969 + 3 ^ 40 * 1333634 * 2
def baseEnd_1333634 : Nat := 456530172785560256361157

theorem tailTrace_1333634 : CollatzResearch.WordTrace tailWord_1333634 prefixEnd_1333634 456530172785560256361157 := by
  unfold tailWord_1333634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160407012619814849721989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32427752033652839599258637 12160407012619814849721989)
  ·
    refine ⟨2280076314866215284322873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12160407012619814849721989 2280076314866215284322873)
    ·
      refine ⟨1710057236149661463242155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2280076314866215284322873 1710057236149661463242155)
      ·
        refine ⟨2565085854224492194863233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710057236149661463242155 2565085854224492194863233)
        ·
          refine ⟨1923814390668369146147425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2565085854224492194863233 1923814390668369146147425)
          ·
            refine ⟨1442860793001276859610569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1923814390668369146147425 1442860793001276859610569)
            ·
              refine ⟨1082145594750957644707927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442860793001276859610569 1082145594750957644707927)
              ·
                refine ⟨1623218392126436467061891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082145594750957644707927 1623218392126436467061891)
                ·
                  refine ⟨2434827588189654700592837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623218392126436467061891 2434827588189654700592837)
                  ·
                    refine ⟨456530172785560256361157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2434827588189654700592837 456530172785560256361157)
                    ·
                      rfl

theorem cell22_1333634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1333634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333634 prefixEnd_1333634 := by exact prefixLift 1333634
  have htrace : WordTrace (prefixWord ++ tailWord_1333634) baseStart_1333634 baseEnd_1333634 := by
    simpa [prefixWord, tailWord_1333634, baseEnd_1333634] using wordTrace_append hprefix tailTrace_1333634
  have hstable : (prefixWord ++ tailWord_1333634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333634).length < 2 ^ (prefixWord ++ tailWord_1333634).sum := by decide
  have hdescent : baseEnd_1333634 < baseStart_1333634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333658 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_1333658 : Nat := 118140960795 + 1333658 * 2 ^ 59
def prefixEnd_1333658 : Nat := 4983230072969 + 3 ^ 40 * 1333658 * 2
def baseEnd_1333658 : Nat := 456538388476032193761083

theorem tailTrace_1333658 : CollatzResearch.WordTrace tailWord_1333658 prefixEnd_1333658 456538388476032193761083 := by
  unfold tailWord_1333658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160625850598077874440407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32428335601594874331841085 12160625850598077874440407)
  ·
    refine ⟨18240938775897116811660611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12160625850598077874440407 18240938775897116811660611)
    ·
      refine ⟨27361408163845675217490917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18240938775897116811660611 27361408163845675217490917)
      ·
        refine ⟨5130264030721064103279547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27361408163845675217490917 5130264030721064103279547)
        ·
          refine ⟨7695396046081596154919321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130264030721064103279547 7695396046081596154919321)
          ·
            refine ⟨5771547034561197116189491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7695396046081596154919321 5771547034561197116189491)
            ·
              refine ⟨8657320551841795674284237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771547034561197116189491 8657320551841795674284237)
              ·
                refine ⟨3246495206940673377856589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8657320551841795674284237 3246495206940673377856589)
                ·
                  refine ⟨1217435702602752516696221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3246495206940673377856589 1217435702602752516696221)
                  ·
                    refine ⟨456538388476032193761083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217435702602752516696221 456538388476032193761083)
                    ·
                      rfl

theorem cell22_1333658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_1333658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333658 prefixEnd_1333658 := by exact prefixLift 1333658
  have htrace : WordTrace (prefixWord ++ tailWord_1333658) baseStart_1333658 baseEnd_1333658 := by
    simpa [prefixWord, tailWord_1333658, baseEnd_1333658] using wordTrace_append hprefix tailTrace_1333658
  have hstable : (prefixWord ++ tailWord_1333658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333658).length < 2 ^ (prefixWord ++ tailWord_1333658).sum := by decide
  have hdescent : baseEnd_1333658 < baseStart_1333658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333677 : List Nat := [1, 5, 2, 2, 3, 1, 2, 6]
def baseStart_1333677 : Nat := 118140960795 + 1333677 * 2 ^ 59
def prefixEnd_1333677 : Nat := 4983230072969 + 3 ^ 40 * 1333677 * 2
def baseEnd_1333677 : Nat := 50727210284924719726225

theorem tailTrace_1333677 : CollatzResearch.WordTrace tailWord_1333677 prefixEnd_1333677 50727210284924719726225 := by
  unfold tailWord_1333677
  simp only [CollatzResearch.WordTrace]
  refine ⟨48643196389323477742703285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32428797592882318495135523 48643196389323477742703285)
  ·
    refine ⟨4560299661499076038378433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48643196389323477742703285 4560299661499076038378433)
    ·
      refine ⟨3420224746124307028783825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4560299661499076038378433 3420224746124307028783825)
      ·
        refine ⟨2565168559593230271587869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3420224746124307028783825 2565168559593230271587869)
        ·
          refine ⟨961938209847461351845451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2565168559593230271587869 961938209847461351845451)
          ·
            refine ⟨1442907314771192027768177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961938209847461351845451 1442907314771192027768177)
            ·
              refine ⟨1082180486078394020826133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442907314771192027768177 1082180486078394020826133)
              ·
                refine ⟨50727210284924719726225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1082180486078394020826133 50727210284924719726225)
                ·
                  rfl

theorem cell22_1333677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 6].length) (baseStart_1333677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333677 prefixEnd_1333677 := by exact prefixLift 1333677
  have htrace : WordTrace (prefixWord ++ tailWord_1333677) baseStart_1333677 baseEnd_1333677 := by
    simpa [prefixWord, tailWord_1333677, baseEnd_1333677] using wordTrace_append hprefix tailTrace_1333677
  have hstable : (prefixWord ++ tailWord_1333677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333677).length < 2 ^ (prefixWord ++ tailWord_1333677).sum := by decide
  have hdescent : baseEnd_1333677 < baseStart_1333677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333692 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_1333692 : Nat := 118140960795 + 1333692 * 2 ^ 59
def prefixEnd_1333692 : Nat := 4983230072969 + 3 ^ 40 * 1333692 * 2
def baseEnd_1333692 : Nat := 456550027370867438410979

theorem tailTrace_1333692 : CollatzResearch.WordTrace tailWord_1333692 prefixEnd_1333692 456550027370867438410979 := by
  unfold tailWord_1333692
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321871742134567652249665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32429162322846090202999553 24321871742134567652249665)
  ·
    refine ⟨18241403806600925739187249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24321871742134567652249665 18241403806600925739187249)
    ·
      refine ⟨13681052854950694304390437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18241403806600925739187249 13681052854950694304390437)
      ·
        refine ⟨2565197410303255182073207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13681052854950694304390437 2565197410303255182073207)
        ·
          refine ⟨3847796115454882773109811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565197410303255182073207 3847796115454882773109811)
          ·
            refine ⟨5771694173182324159664717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847796115454882773109811 5771694173182324159664717)
            ·
              refine ⟨2164385314943371559874269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5771694173182324159664717 2164385314943371559874269)
              ·
                refine ⟨811644493103764334952851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164385314943371559874269 811644493103764334952851)
                ·
                  refine ⟨1217466739655646502429277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811644493103764334952851 1217466739655646502429277)
                  ·
                    refine ⟨456550027370867438410979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217466739655646502429277 456550027370867438410979)
                    ·
                      rfl

theorem cell22_1333692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_1333692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333692 prefixEnd_1333692 := by exact prefixLift 1333692
  have htrace : WordTrace (prefixWord ++ tailWord_1333692) baseStart_1333692 baseEnd_1333692 := by
    simpa [prefixWord, tailWord_1333692, baseEnd_1333692] using wordTrace_append hprefix tailTrace_1333692
  have hstable : (prefixWord ++ tailWord_1333692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333692).length < 2 ^ (prefixWord ++ tailWord_1333692).sum := by decide
  have hdescent : baseEnd_1333692 < baseStart_1333692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333750 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1333750 : Nat := 118140960795 + 1333750 * 2 ^ 59
def prefixEnd_1333750 : Nat := 4983230072969 + 3 ^ 40 * 1333750 * 2
def baseEnd_1333750 : Nat := 152189960652058206820267

theorem tailTrace_1333750 : CollatzResearch.WordTrace tailWord_1333750 prefixEnd_1333750 152189960652058206820267 := by
  unfold tailWord_1333750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040366182378688200631919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32430572612039340806740469 3040366182378688200631919)
  ·
    refine ⟨4560549273568032300947879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3040366182378688200631919 4560549273568032300947879)
    ·
      refine ⟨6840823910352048451421819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560549273568032300947879 6840823910352048451421819)
      ·
        refine ⟨10261235865528072677132729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840823910352048451421819 10261235865528072677132729)
        ·
          refine ⟨7695926899146054507849547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10261235865528072677132729 7695926899146054507849547)
          ·
            refine ⟨11543890348719081761774321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695926899146054507849547 11543890348719081761774321)
            ·
              refine ⟨8657917761539311321330741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11543890348719081761774321 8657917761539311321330741)
              ·
                refine ⟨811679790144310436374757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8657917761539311321330741 811679790144310436374757)
                ·
                  refine ⟨152189960652058206820267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811679790144310436374757 152189960652058206820267)
                  ·
                    rfl

theorem cell22_1333750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1333750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333750 prefixEnd_1333750 := by exact prefixLift 1333750
  have htrace : WordTrace (prefixWord ++ tailWord_1333750) baseStart_1333750 baseEnd_1333750 := by
    simpa [prefixWord, tailWord_1333750, baseEnd_1333750] using wordTrace_append hprefix tailTrace_1333750
  have hstable : (prefixWord ++ tailWord_1333750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333750).length < 2 ^ (prefixWord ++ tailWord_1333750).sum := by decide
  have hdescent : baseEnd_1333750 < baseStart_1333750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333761 : List Nat := [1, 2, 4, 1, 3, 11]
def baseStart_1333761 : Nat := 118140960795 + 1333761 * 2 ^ 59
def prefixEnd_1333761 : Nat := 4983230072969 + 3 ^ 40 * 1333761 * 2
def baseEnd_1333761 : Nat := 5636711697295978499207

theorem tailTrace_1333761 : CollatzResearch.WordTrace tailWord_1333761 prefixEnd_1333761 5636711697295978499207 := by
  unfold tailWord_1333761
  simp only [CollatzResearch.WordTrace]
  refine ⟨48646260121019160088761137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32430840080679440059174091 48646260121019160088761137)
  ·
    refine ⟨36484695090764370066570853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48646260121019160088761137 36484695090764370066570853)
    ·
      refine ⟨6840880329518319387482035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36484695090764370066570853 6840880329518319387482035)
      ·
        refine ⟨10261320494277479081223053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840880329518319387482035 10261320494277479081223053)
        ·
          refine ⟨3847995185354054655458645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10261320494277479081223053 3847995185354054655458645)
          ·
            refine ⟨5636711697295978499207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3847995185354054655458645 5636711697295978499207)
            ·
              rfl

theorem cell22_1333761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 11].length) (baseStart_1333761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333761 prefixEnd_1333761 := by exact prefixLift 1333761
  have htrace : WordTrace (prefixWord ++ tailWord_1333761) baseStart_1333761 baseEnd_1333761 := by
    simpa [prefixWord, tailWord_1333761, baseEnd_1333761] using wordTrace_append hprefix tailTrace_1333761
  have hstable : (prefixWord ++ tailWord_1333761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333761).length < 2 ^ (prefixWord ++ tailWord_1333761).sum := by decide
  have hdescent : baseEnd_1333761 < baseStart_1333761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333791 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_1333791 : Nat := 118140960795 + 1333791 * 2 ^ 59
def prefixEnd_1333791 : Nat := 4983230072969 + 3 ^ 40 * 1333791 * 2
def baseEnd_1333791 : Nat := 456583917094064180185675

theorem tailTrace_1333791 : CollatzResearch.WordTrace tailWord_1333791 prefixEnd_1333791 456583917094064180185675 := by
  unfold tailWord_1333791
  simp only [CollatzResearch.WordTrace]
  refine ⟨48647354310910475212353227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32431569540606983474902151 48647354310910475212353227)
  ·
    refine ⟨72971031466365712818529841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48647354310910475212353227 72971031466365712818529841)
    ·
      refine ⟨54728273599774284613897381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72971031466365712818529841 54728273599774284613897381)
      ·
        refine ⟨10261551299957678365105759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54728273599774284613897381 10261551299957678365105759)
        ·
          refine ⟨15392326949936517547658639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10261551299957678365105759 15392326949936517547658639)
          ·
            refine ⟨23088490424904776321487959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15392326949936517547658639 23088490424904776321487959)
            ·
              refine ⟨34632735637357164482231939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23088490424904776321487959 34632735637357164482231939)
              ·
                refine ⟨51949103456035746723347909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34632735637357164482231939 51949103456035746723347909)
                ·
                  refine ⟨9740456898006702510627733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51949103456035746723347909 9740456898006702510627733)
                  ·
                    refine ⟨456583917094064180185675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9740456898006702510627733 456583917094064180185675)
                    ·
                      rfl

theorem cell22_1333791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_1333791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333791 prefixEnd_1333791 := by exact prefixLift 1333791
  have htrace : WordTrace (prefixWord ++ tailWord_1333791) baseStart_1333791 baseEnd_1333791 := by
    simpa [prefixWord, tailWord_1333791, baseEnd_1333791] using wordTrace_append hprefix tailTrace_1333791
  have hstable : (prefixWord ++ tailWord_1333791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333791).length < 2 ^ (prefixWord ++ tailWord_1333791).sum := by decide
  have hdescent : baseEnd_1333791 < baseStart_1333791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333838 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1333838 : Nat := 118140960795 + 1333838 * 2 ^ 59
def prefixEnd_1333838 : Nat := 4983230072969 + 3 ^ 40 * 1333838 * 2
def baseEnd_1333838 : Nat := 456600006154571724260531

theorem tailTrace_1333838 : CollatzResearch.WordTrace tailWord_1333838 prefixEnd_1333838 456600006154571724260531 := by
  unfold tailWord_1333838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081133567717525279914271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32432712361160134826209445 6081133567717525279914271)
  ·
    refine ⟨9121700351576287919871407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6081133567717525279914271 9121700351576287919871407)
    ·
      refine ⟨13682550527364431879807111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9121700351576287919871407 13682550527364431879807111)
      ·
        refine ⟨20523825791046647819710667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13682550527364431879807111 20523825791046647819710667)
        ·
          refine ⟨30785738686569971729566001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20523825791046647819710667 30785738686569971729566001)
          ·
            refine ⟨23089304014927478797174501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30785738686569971729566001 23089304014927478797174501)
            ·
              refine ⟨4329244502798902274470219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23089304014927478797174501 4329244502798902274470219)
              ·
                refine ⟨6493866754198353411705329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329244502798902274470219 6493866754198353411705329)
                ·
                  refine ⟨4870400065648765058778997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6493866754198353411705329 4870400065648765058778997)
                  ·
                    refine ⟨456600006154571724260531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4870400065648765058778997 456600006154571724260531)
                    ·
                      rfl

theorem cell22_1333838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1333838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333838 prefixEnd_1333838 := by exact prefixLift 1333838
  have htrace : WordTrace (prefixWord ++ tailWord_1333838) baseStart_1333838 baseEnd_1333838 := by
    simpa [prefixWord, tailWord_1333838, baseEnd_1333838] using wordTrace_append hprefix tailTrace_1333838
  have hstable : (prefixWord ++ tailWord_1333838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333838).length < 2 ^ (prefixWord ++ tailWord_1333838).sum := by decide
  have hdescent : baseEnd_1333838 < baseStart_1333838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333861 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_1333861 : Nat := 118140960795 + 1333861 * 2 ^ 59
def prefixEnd_1333861 : Nat := 4983230072969 + 3 ^ 40 * 1333861 * 2
def baseEnd_1333861 : Nat := 456607879524607330935461

theorem tailTrace_1333861 : CollatzResearch.WordTrace tailWord_1333861 prefixEnd_1333861 456607879524607330935461 := by
  unfold tailWord_1333861
  simp only [CollatzResearch.WordTrace]
  refine ⟨48649907420656877167401437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32433271613771251444934291 48649907420656877167401437)
  ·
    refine ⟨18243715282746328937775539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48649907420656877167401437 18243715282746328937775539)
    ·
      refine ⟨27365572924119493406663309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18243715282746328937775539 27365572924119493406663309)
      ·
        refine ⟨10262089846544810027498741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27365572924119493406663309 10262089846544810027498741)
        ·
          refine ⟨962070923113575940078007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10262089846544810027498741 962070923113575940078007)
          ·
            refine ⟨1443106384670363910117011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962070923113575940078007 1443106384670363910117011)
            ·
              refine ⟨2164659577005545865175517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443106384670363910117011 2164659577005545865175517)
              ·
                refine ⟨811747341377079699440819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164659577005545865175517 811747341377079699440819)
                ·
                  refine ⟨1217621012065619549161229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811747341377079699440819 1217621012065619549161229)
                  ·
                    refine ⟨456607879524607330935461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217621012065619549161229 456607879524607330935461)
                    ·
                      rfl

theorem cell22_1333861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_1333861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333861 prefixEnd_1333861 := by exact prefixLift 1333861
  have htrace : WordTrace (prefixWord ++ tailWord_1333861) baseStart_1333861 baseEnd_1333861 := by
    simpa [prefixWord, tailWord_1333861, baseEnd_1333861] using wordTrace_append hprefix tailTrace_1333861
  have hstable : (prefixWord ++ tailWord_1333861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333861).length < 2 ^ (prefixWord ++ tailWord_1333861).sum := by decide
  have hdescent : baseEnd_1333861 < baseStart_1333861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333930 : List Nat := [3, 1, 5, 2, 11]
def baseStart_1333930 : Nat := 118140960795 + 1333930 * 2 ^ 59
def prefixEnd_1333930 : Nat := 4983230072969 + 3 ^ 40 * 1333930 * 2
def baseEnd_1333930 : Nat := 1879141973805408028643

theorem tailTrace_1333930 : CollatzResearch.WordTrace tailWord_1333930 prefixEnd_1333930 1879141973805408028643 := by
  unfold tailWord_1333930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12163106014351725487915811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32434949371604601301108829 12163106014351725487915811)
  ·
    refine ⟨18244659021527588231873717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12163106014351725487915811 18244659021527588231873717)
    ·
      refine ⟨1710436783268211396738161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18244659021527588231873717 1710436783268211396738161)
      ·
        refine ⟨1282827587451158547553621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1710436783268211396738161 1282827587451158547553621)
        ·
          refine ⟨1879141973805408028643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1282827587451158547553621 1879141973805408028643)
          ·
            rfl

theorem cell22_1333930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 11].length) (baseStart_1333930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333930 prefixEnd_1333930 := by exact prefixLift 1333930
  have htrace : WordTrace (prefixWord ++ tailWord_1333930) baseStart_1333930 baseEnd_1333930 := by
    simpa [prefixWord, tailWord_1333930, baseEnd_1333930] using wordTrace_append hprefix tailTrace_1333930
  have hstable : (prefixWord ++ tailWord_1333930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333930).length < 2 ^ (prefixWord ++ tailWord_1333930).sum := by decide
  have hdescent : baseEnd_1333930 < baseStart_1333930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333934 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1333934 : Nat := 118140960795 + 1333934 * 2 ^ 59
def prefixEnd_1333934 : Nat := 4983230072969 + 3 ^ 40 * 1333934 * 2
def baseEnd_1333934 : Nat := 456632868916459473860237

theorem tailTrace_1333934 : CollatzResearch.WordTrace tailWord_1333934 prefixEnd_1333934 456632868916459473860237 := by
  unfold tailWord_1333934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081571243674051329351107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32435046632928273756539237 6081571243674051329351107)
  ·
    refine ⟨9122356865511076994026661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6081571243674051329351107 9122356865511076994026661)
    ·
      refine ⟨1710441912283326936379999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9122356865511076994026661 1710441912283326936379999)
      ·
        refine ⟨2565662868424990404569999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710441912283326936379999 2565662868424990404569999)
        ·
          refine ⟨3848494302637485606854999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565662868424990404569999 3848494302637485606854999)
          ·
            refine ⟨5772741453956228410282499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848494302637485606854999 5772741453956228410282499)
            ·
              refine ⟨8659112180934342615423749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772741453956228410282499 8659112180934342615423749)
              ·
                refine ⟨1623583533925189240391953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8659112180934342615423749 1623583533925189240391953)
                ·
                  refine ⟨1217687650443891930293965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623583533925189240391953 1217687650443891930293965)
                  ·
                    refine ⟨456632868916459473860237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217687650443891930293965 456632868916459473860237)
                    ·
                      rfl

theorem cell22_1333934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1333934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333934 prefixEnd_1333934 := by exact prefixLift 1333934
  have htrace : WordTrace (prefixWord ++ tailWord_1333934) baseStart_1333934 baseEnd_1333934 := by
    simpa [prefixWord, tailWord_1333934, baseEnd_1333934] using wordTrace_append hprefix tailTrace_1333934
  have hstable : (prefixWord ++ tailWord_1333934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333934).length < 2 ^ (prefixWord ++ tailWord_1333934).sum := by decide
  have hdescent : baseEnd_1333934 < baseStart_1333934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333945 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_1333945 : Nat := 118140960795 + 1333945 * 2 ^ 59
def prefixEnd_1333945 : Nat := 4983230072969 + 3 ^ 40 * 1333945 * 2
def baseEnd_1333945 : Nat := 456636634441259111835203

theorem tailTrace_1333945 : CollatzResearch.WordTrace tailWord_1333945 prefixEnd_1333945 456636634441259111835203 := by
  unfold tailWord_1333945
  simp only [CollatzResearch.WordTrace]
  refine ⟨48652971152352559513459289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32435314101568373008972859 48652971152352559513459289)
  ·
    refine ⟨36489728364264419635094467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48652971152352559513459289 36489728364264419635094467)
    ·
      refine ⟨54734592546396629452641701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36489728364264419635094467 54734592546396629452641701)
      ·
        refine ⟨10262736102449368022370319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54734592546396629452641701 10262736102449368022370319)
        ·
          refine ⟨15394104153674052033555479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10262736102449368022370319 15394104153674052033555479)
          ·
            refine ⟨23091156230511078050333219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15394104153674052033555479 23091156230511078050333219)
            ·
              refine ⟨34636734345766617075499829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23091156230511078050333219 34636734345766617075499829)
              ·
                refine ⟨3247193844915620350828109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34636734345766617075499829 3247193844915620350828109)
                ·
                  refine ⟨1217697691843357631560541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3247193844915620350828109 1217697691843357631560541)
                  ·
                    refine ⟨456636634441259111835203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217697691843357631560541 456636634441259111835203)
                    ·
                      rfl

theorem cell22_1333945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_1333945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333945 prefixEnd_1333945 := by exact prefixLift 1333945
  have htrace : WordTrace (prefixWord ++ tailWord_1333945) baseStart_1333945 baseEnd_1333945 := by
    simpa [prefixWord, tailWord_1333945, baseEnd_1333945] using wordTrace_append hprefix tailTrace_1333945
  have hstable : (prefixWord ++ tailWord_1333945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333945).length < 2 ^ (prefixWord ++ tailWord_1333945).sum := by decide
  have hdescent : baseEnd_1333945 < baseStart_1333945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333962 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1333962 : Nat := 118140960795 + 1333962 * 2 ^ 59
def prefixEnd_1333962 : Nat := 4983230072969 + 3 ^ 40 * 1333962 * 2
def baseEnd_1333962 : Nat := 456642453888676734160151

theorem tailTrace_1333962 : CollatzResearch.WordTrace tailWord_1333962 prefixEnd_1333962 456642453888676734160151 := by
  unfold tailWord_1333962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12163397798322742854207035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32435727462193980944552093 12163397798322742854207035)
  ·
    refine ⟨18245096697484114281310553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12163397798322742854207035 18245096697484114281310553)
    ·
      refine ⟨13683822523113085710982915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18245096697484114281310553 13683822523113085710982915)
      ·
        refine ⟨20525733784669628566474373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13683822523113085710982915 20525733784669628566474373)
        ·
          refine ⟨3848575084625555356213945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20525733784669628566474373 3848575084625555356213945)
          ·
            refine ⟨2886431313469166517160459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3848575084625555356213945 2886431313469166517160459)
            ·
              refine ⟨4329646970203749775740689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886431313469166517160459 4329646970203749775740689)
              ·
                refine ⟨3247235227652812331805517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329646970203749775740689 3247235227652812331805517)
                ·
                  refine ⟨1217713210369804624427069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3247235227652812331805517 1217713210369804624427069)
                  ·
                    refine ⟨456642453888676734160151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217713210369804624427069 456642453888676734160151)
                    ·
                      rfl

theorem cell22_1333962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1333962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1333962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1333962 prefixEnd_1333962 := by exact prefixLift 1333962
  have htrace : WordTrace (prefixWord ++ tailWord_1333962) baseStart_1333962 baseEnd_1333962 := by
    simpa [prefixWord, tailWord_1333962, baseEnd_1333962] using wordTrace_append hprefix tailTrace_1333962
  have hstable : (prefixWord ++ tailWord_1333962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333962).length < 2 ^ (prefixWord ++ tailWord_1333962).sum := by decide
  have hdescent : baseEnd_1333962 < baseStart_1333962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334020 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1334020 : Nat := 118140960795 + 1334020 * 2 ^ 59
def prefixEnd_1334020 : Nat := 4983230072969 + 3 ^ 40 * 1334020 * 2
def baseEnd_1334020 : Nat := 152220769491327972069991

theorem tailTrace_1334020 : CollatzResearch.WordTrace tailWord_1334020 prefixEnd_1334020 152220769491327972069991 := by
  unfold tailWord_1334020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24327853313540423661219757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32437137751387231548293009 24327853313540423661219757)
  ·
    refine ⟨9122944992577658872957409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24327853313540423661219757 9122944992577658872957409)
    ·
      refine ⟨6842208744433244154718057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9122944992577658872957409 6842208744433244154718057)
      ·
        refine ⟨5131656558324933116038543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6842208744433244154718057 5131656558324933116038543)
        ·
          refine ⟨7697484837487399674057815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5131656558324933116038543 7697484837487399674057815)
          ·
            refine ⟨11546227256231099511086723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7697484837487399674057815 11546227256231099511086723)
            ·
              refine ⟨17319340884346649266630085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11546227256231099511086723 17319340884346649266630085)
              ·
                refine ⟨3247376415814996737493141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17319340884346649266630085 3247376415814996737493141)
                ·
                  refine ⟨152220769491327972069991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3247376415814996737493141 152220769491327972069991)
                  ·
                    rfl

theorem cell22_1334020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1334020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334020 prefixEnd_1334020 := by exact prefixLift 1334020
  have htrace : WordTrace (prefixWord ++ tailWord_1334020) baseStart_1334020 baseEnd_1334020 := by
    simpa [prefixWord, tailWord_1334020, baseEnd_1334020] using wordTrace_append hprefix tailTrace_1334020
  have hstable : (prefixWord ++ tailWord_1334020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334020).length < 2 ^ (prefixWord ++ tailWord_1334020).sum := by decide
  have hdescent : baseEnd_1334020 < baseStart_1334020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334035 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 6, 3]
def baseStart_1334035 : Nat := 118140960795 + 1334035 * 2 ^ 59
def prefixEnd_1334035 : Nat := 4983230072969 + 3 ^ 40 * 1334035 * 2
def baseEnd_1334035 : Nat := 456667443280528877084927

theorem tailTrace_1334035 : CollatzResearch.WordTrace tailWord_1334035 prefixEnd_1334035 456667443280528877084927 := by
  unfold tailWord_1334035
  simp only [CollatzResearch.WordTrace]
  refine ⟨48656253722026504884235559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32437502481351003256157039 48656253722026504884235559)
  ·
    refine ⟨72984380583039757326353339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48656253722026504884235559 72984380583039757326353339)
    ·
      refine ⟨109476570874559635989530009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72984380583039757326353339 109476570874559635989530009)
      ·
        refine ⟨82107428155919726992147507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109476570874559635989530009 82107428155919726992147507)
        ·
          refine ⟨123161142233879590488221261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82107428155919726992147507 123161142233879590488221261)
          ·
            refine ⟨46185428337704846433082973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123161142233879590488221261 46185428337704846433082973)
            ·
              refine ⟨17319535626639317412406115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46185428337704846433082973 17319535626639317412406115)
              ·
                refine ⟨25979303439958976118609173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17319535626639317412406115 25979303439958976118609173)
                ·
                  refine ⟨1217779848748077005559805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25979303439958976118609173 1217779848748077005559805)
                  ·
                    refine ⟨456667443280528877084927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217779848748077005559805 456667443280528877084927)
                    ·
                      rfl

theorem cell22_1334035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 3].length) (baseStart_1334035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334035 prefixEnd_1334035 := by exact prefixLift 1334035
  have htrace : WordTrace (prefixWord ++ tailWord_1334035) baseStart_1334035 baseEnd_1334035 := by
    simpa [prefixWord, tailWord_1334035, baseEnd_1334035] using wordTrace_append hprefix tailTrace_1334035
  have hstable : (prefixWord ++ tailWord_1334035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334035).length < 2 ^ (prefixWord ++ tailWord_1334035).sum := by decide
  have hdescent : baseEnd_1334035 < baseStart_1334035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334065 : List Nat := [1, 2, 2, 3, 2, 1, 4, 7]
def baseStart_1334065 : Nat := 118140960795 + 1334065 * 2 ^ 59
def prefixEnd_1334065 : Nat := 4983230072969 + 3 ^ 40 * 1334065 * 2
def baseEnd_1334065 : Nat := 50741968099290977648315

theorem tailTrace_1334065 : CollatzResearch.WordTrace tailWord_1334065 prefixEnd_1334065 50741968099290977648315 := by
  unfold tailWord_1334065
  simp only [CollatzResearch.WordTrace]
  refine ⟨48657347911917820007827649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32438231941278546671885099 48657347911917820007827649)
  ·
    refine ⟨36493010933938365005870737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48657347911917820007827649 36493010933938365005870737)
    ·
      refine ⟨27369758200453773754403053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36493010933938365005870737 27369758200453773754403053)
      ·
        refine ⟨10263659325170165157901145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27369758200453773754403053 10263659325170165157901145)
        ·
          refine ⟨7697744493877623868425859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10263659325170165157901145 7697744493877623868425859)
          ·
            refine ⟨11546616740816435802638789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7697744493877623868425859 11546616740816435802638789)
            ·
              refine ⟨2164990638903081712994773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11546616740816435802638789 2164990638903081712994773)
              ·
                refine ⟨50741968099290977648315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2164990638903081712994773 50741968099290977648315)
                ·
                  rfl

theorem cell22_1334065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 7].length) (baseStart_1334065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334065 prefixEnd_1334065 := by exact prefixLift 1334065
  have htrace : WordTrace (prefixWord ++ tailWord_1334065) baseStart_1334065 baseEnd_1334065 := by
    simpa [prefixWord, tailWord_1334065, baseEnd_1334065] using wordTrace_append hprefix tailTrace_1334065
  have hstable : (prefixWord ++ tailWord_1334065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334065).length < 2 ^ (prefixWord ++ tailWord_1334065).sum := by decide
  have hdescent : baseEnd_1334065 < baseStart_1334065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334069 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1334069 : Nat := 118140960795 + 1334069 * 2 ^ 59
def prefixEnd_1334069 : Nat := 4983230072969 + 3 ^ 40 * 1334069 * 2
def baseEnd_1334069 : Nat := 456679082175364121734823

theorem tailTrace_1334069 : CollatzResearch.WordTrace tailWord_1334069 prefixEnd_1334069 456679082175364121734823 := by
  unfold tailWord_1334069
  simp only [CollatzResearch.WordTrace]
  refine ⟨48657493803903328690973261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32438329202602219127315507 48657493803903328690973261)
  ·
    refine ⟨18246560176463748259114973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48657493803903328690973261 18246560176463748259114973)
    ·
      refine ⟨6842460066173905597168115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18246560176463748259114973 6842460066173905597168115)
      ·
        refine ⟨10263690099260858395752173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842460066173905597168115 10263690099260858395752173)
        ·
          refine ⟨3848883787222821898407065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10263690099260858395752173 3848883787222821898407065)
          ·
            refine ⟨2886662840417116423805299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3848883787222821898407065 2886662840417116423805299)
            ·
              refine ⟨4329994260625674635707949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886662840417116423805299 4329994260625674635707949)
              ·
                refine ⟨1623747847734627988390481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4329994260625674635707949 1623747847734627988390481)
                ·
                  refine ⟨1217810885800970991292861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623747847734627988390481 1217810885800970991292861)
                  ·
                    refine ⟨456679082175364121734823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217810885800970991292861 456679082175364121734823)
                    ·
                      rfl

theorem cell22_1334069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1334069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334069 prefixEnd_1334069 := by exact prefixLift 1334069
  have htrace : WordTrace (prefixWord ++ tailWord_1334069) baseStart_1334069 baseEnd_1334069 := by
    simpa [prefixWord, tailWord_1334069, baseEnd_1334069] using wordTrace_append hprefix tailTrace_1334069
  have hstable : (prefixWord ++ tailWord_1334069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334069).length < 2 ^ (prefixWord ++ tailWord_1334069).sum := by decide
  have hdescent : baseEnd_1334069 < baseStart_1334069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334086 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1334086 : Nat := 118140960795 + 1334086 * 2 ^ 59
def prefixEnd_1334086 : Nat := 4983230072969 + 3 ^ 40 * 1334086 * 2
def baseEnd_1334086 : Nat := 456684901622781744059771

theorem tailTrace_1334086 : CollatzResearch.WordTrace tailWord_1334086 prefixEnd_1334086 456684901622781744059771 := by
  unfold tailWord_1334086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520566057651304393573191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32438742563227827062894741 1520566057651304393573191)
  ·
    refine ⟨2280849086476956590359787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1520566057651304393573191 2280849086476956590359787)
    ·
      refine ⟨3421273629715434885539681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280849086476956590359787 3421273629715434885539681)
      ·
        refine ⟨2565955222286576164154761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3421273629715434885539681 2565955222286576164154761)
        ·
          refine ⟨1924466416714932123116071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2565955222286576164154761 1924466416714932123116071)
          ·
            refine ⟨2886699625072398184674107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924466416714932123116071 2886699625072398184674107)
            ·
              refine ⟨4330049437608597277011161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886699625072398184674107 4330049437608597277011161)
              ·
                refine ⟨3247537078206447957758371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330049437608597277011161 3247537078206447957758371)
                ·
                  refine ⟨4871305617309671936637557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247537078206447957758371 4871305617309671936637557)
                  ·
                    refine ⟨456684901622781744059771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4871305617309671936637557 456684901622781744059771)
                    ·
                      rfl

theorem cell22_1334086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1334086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334086 prefixEnd_1334086 := by exact prefixLift 1334086
  have htrace : WordTrace (prefixWord ++ tailWord_1334086) baseStart_1334086 baseEnd_1334086 := by
    simpa [prefixWord, tailWord_1334086, baseEnd_1334086] using wordTrace_append hprefix tailTrace_1334086
  have hstable : (prefixWord ++ tailWord_1334086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334086).length < 2 ^ (prefixWord ++ tailWord_1334086).sum := by decide
  have hdescent : baseEnd_1334086 < baseStart_1334086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334185 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_1334185 : Nat := 118140960795 + 1334185 * 2 ^ 59
def prefixEnd_1334185 : Nat := 4983230072969 + 3 ^ 40 * 1334185 * 2
def baseEnd_1334185 : Nat := 456718791345978485834467

theorem tailTrace_1334185 : CollatzResearch.WordTrace tailWord_1334185 prefixEnd_1334185 456718791345978485834467 := by
  unfold tailWord_1334185
  simp only [CollatzResearch.WordTrace]
  refine ⟨48661724671483080502196009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32441149780988720334797339 48661724671483080502196009)
  ·
    refine ⟨36496293503612310376647007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48661724671483080502196009 36496293503612310376647007)
    ·
      refine ⟨54744440255418465564970511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36496293503612310376647007 54744440255418465564970511)
      ·
        refine ⟨82116660383127698347455767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54744440255418465564970511 82116660383127698347455767)
        ·
          refine ⟨123174990574691547521183651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82116660383127698347455767 123174990574691547521183651)
          ·
            refine ⟨184762485862037321281775477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123174990574691547521183651 184762485862037321281775477)
            ·
              refine ⟨17321483049565998870166451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184762485862037321281775477 17321483049565998870166451)
              ·
                refine ⟨25982224574348998305249677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17321483049565998870166451 25982224574348998305249677)
                ·
                  refine ⟨9743334215380874364468629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25982224574348998305249677 9743334215380874364468629)
                  ·
                    refine ⟨456718791345978485834467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9743334215380874364468629 456718791345978485834467)
                    ·
                      rfl

theorem cell22_1334185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_1334185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334185 prefixEnd_1334185 := by exact prefixLift 1334185
  have htrace : WordTrace (prefixWord ++ tailWord_1334185) baseStart_1334185 baseEnd_1334185 := by
    simpa [prefixWord, tailWord_1334185, baseEnd_1334185] using wordTrace_append hprefix tailTrace_1334185
  have hstable : (prefixWord ++ tailWord_1334185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334185).length < 2 ^ (prefixWord ++ tailWord_1334185).sum := by decide
  have hdescent : baseEnd_1334185 < baseStart_1334185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334202 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_1334202 : Nat := 118140960795 + 1334202 * 2 ^ 59
def prefixEnd_1334202 : Nat := 4983230072969 + 3 ^ 40 * 1334202 * 2
def baseEnd_1334202 : Nat := 456724610793396108159415

theorem tailTrace_1334202 : CollatzResearch.WordTrace tailWord_1334202 prefixEnd_1334202 456724610793396108159415 := by
  unfold tailWord_1334202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165586178105373101391215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32441563141614328270376573 12165586178105373101391215)
  ·
    refine ⟨18248379267158059652086823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12165586178105373101391215 18248379267158059652086823)
    ·
      refine ⟨27372568900737089478130235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18248379267158059652086823 27372568900737089478130235)
      ·
        refine ⟨41058853351105634217195353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27372568900737089478130235 41058853351105634217195353)
        ·
          refine ⟨30794140013329225662896515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41058853351105634217195353 30794140013329225662896515)
          ·
            refine ⟨46191210019993838494344773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30794140013329225662896515 46191210019993838494344773)
            ·
              refine ⟨8660851878748844717689645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46191210019993838494344773 8660851878748844717689645)
              ·
                refine ⟨3247819454530816769133617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8660851878748844717689645 3247819454530816769133617)
                ·
                  refine ⟨2435864590898112576850213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247819454530816769133617 2435864590898112576850213)
                  ·
                    refine ⟨456724610793396108159415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2435864590898112576850213 456724610793396108159415)
                    ·
                      rfl

theorem cell22_1334202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_1334202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334202 prefixEnd_1334202 := by exact prefixLift 1334202
  have htrace : WordTrace (prefixWord ++ tailWord_1334202) baseStart_1334202 baseEnd_1334202 := by
    simpa [prefixWord, tailWord_1334202, baseEnd_1334202] using wordTrace_append hprefix tailTrace_1334202
  have hstable : (prefixWord ++ tailWord_1334202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334202).length < 2 ^ (prefixWord ++ tailWord_1334202).sum := by decide
  have hdescent : baseEnd_1334202 < baseStart_1334202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334277 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_1334277 : Nat := 118140960795 + 1334277 * 2 ^ 59
def prefixEnd_1334277 : Nat := 4983230072969 + 3 ^ 40 * 1334277 * 2
def baseEnd_1334277 : Nat := 456750284826120912534185

theorem tailTrace_1334277 : CollatzResearch.WordTrace tailWord_1334277 prefixEnd_1334277 456750284826120912534185 := by
  unfold tailWord_1334277
  simp only [CollatzResearch.WordTrace]
  refine ⟨48665080187149780214545085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32443386791433186809696723 48665080187149780214545085)
  ·
    refine ⟨18249405070181167580454407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48665080187149780214545085 18249405070181167580454407)
    ·
      refine ⟨27374107605271751370681611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18249405070181167580454407 27374107605271751370681611)
      ·
        refine ⟨41061161407907627056022417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27374107605271751370681611 41061161407907627056022417)
        ·
          refine ⟨30795871055930720292016813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41061161407907627056022417 30795871055930720292016813)
          ·
            refine ⟨11548451645974020109506305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30795871055930720292016813 11548451645974020109506305)
            ·
              refine ⟨8661338734480515082129729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11548451645974020109506305 8661338734480515082129729)
              ·
                refine ⟨6496004050860386311597297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8661338734480515082129729 6496004050860386311597297)
                ·
                  refine ⟨4872003038145289733697973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6496004050860386311597297 4872003038145289733697973)
                  ·
                    refine ⟨456750284826120912534185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4872003038145289733697973 456750284826120912534185)
                    ·
                      rfl

theorem cell22_1334277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_1334277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334277 prefixEnd_1334277 := by exact prefixLift 1334277
  have htrace : WordTrace (prefixWord ++ tailWord_1334277) baseStart_1334277 baseEnd_1334277 := by
    simpa [prefixWord, tailWord_1334277, baseEnd_1334277] using wordTrace_append hprefix tailTrace_1334277
  have hstable : (prefixWord ++ tailWord_1334277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334277).length < 2 ^ (prefixWord ++ tailWord_1334277).sum := by decide
  have hdescent : baseEnd_1334277 < baseStart_1334277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334279 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 5]
def baseStart_1334279 : Nat := 118140960795 + 1334279 * 2 ^ 59
def prefixEnd_1334279 : Nat := 4983230072969 + 3 ^ 40 * 1334279 * 2
def baseEnd_1334279 : Nat := 152250323155664524661393

theorem tailTrace_1334279 : CollatzResearch.WordTrace tailWord_1334279 prefixEnd_1334279 152250323155664524661393 := by
  unfold tailWord_1334279
  simp only [CollatzResearch.WordTrace]
  refine ⟨48665153133142534556117891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32443435422095023037411927 48665153133142534556117891)
  ·
    refine ⟨72997729699713801834176837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48665153133142534556117891 72997729699713801834176837)
    ·
      refine ⟨13687074318696337843908157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72997729699713801834176837 13687074318696337843908157)
      ·
        refine ⟨5132652869511126691465559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13687074318696337843908157 5132652869511126691465559)
        ·
          refine ⟨7698979304266690037198339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132652869511126691465559 7698979304266690037198339)
          ·
            refine ⟨11548468956400035055797509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7698979304266690037198339 11548468956400035055797509)
            ·
              refine ⟨2165337929325006572962033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11548468956400035055797509 2165337929325006572962033)
              ·
                refine ⟨1624003446993754929721525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165337929325006572962033 1624003446993754929721525)
                ·
                  refine ⟨152250323155664524661393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1624003446993754929721525 152250323155664524661393)
                  ·
                    rfl

theorem cell22_1334279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 5].length) (baseStart_1334279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334279 prefixEnd_1334279 := by exact prefixLift 1334279
  have htrace : WordTrace (prefixWord ++ tailWord_1334279) baseStart_1334279 baseEnd_1334279 := by
    simpa [prefixWord, tailWord_1334279, baseEnd_1334279] using wordTrace_append hprefix tailTrace_1334279
  have hstable : (prefixWord ++ tailWord_1334279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334279).length < 2 ^ (prefixWord ++ tailWord_1334279).sum := by decide
  have hdescent : baseEnd_1334279 < baseStart_1334279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334283 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 1, 3]
def baseStart_1334283 : Nat := 118140960795 + 1334283 * 2 ^ 59
def prefixEnd_1334283 : Nat := 4983230072969 + 3 ^ 40 * 1334283 * 2
def baseEnd_1334283 : Nat := 456752338748738896884167

theorem tailTrace_1334283 : CollatzResearch.WordTrace tailWord_1334283 prefixEnd_1334283 456752338748738896884167 := by
  unfold tailWord_1334283
  simp only [CollatzResearch.WordTrace]
  refine ⟨48665299025128043239263503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32443532683418695492842335 48665299025128043239263503)
  ·
    refine ⟨72997948537692064858895255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48665299025128043239263503 72997948537692064858895255)
    ·
      refine ⟨109496922806538097288342883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72997948537692064858895255 109496922806538097288342883)
      ·
        refine ⟨164245384209807145932514325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109496922806538097288342883 164245384209807145932514325)
        ·
          refine ⟨7699002384834709965586609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164245384209807145932514325 7699002384834709965586609)
          ·
            refine ⟨5774251788626032474189957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699002384834709965586609 5774251788626032474189957)
            ·
              refine ⟨1082672210367381088910617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5774251788626032474189957 1082672210367381088910617)
              ·
                refine ⟨812004157775535816682963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082672210367381088910617 812004157775535816682963)
                ·
                  refine ⟨1218006236663303725024445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812004157775535816682963 1218006236663303725024445)
                  ·
                    refine ⟨456752338748738896884167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218006236663303725024445 456752338748738896884167)
                    ·
                      rfl

theorem cell22_1334283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 3].length) (baseStart_1334283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334283 prefixEnd_1334283 := by exact prefixLift 1334283
  have htrace : WordTrace (prefixWord ++ tailWord_1334283) baseStart_1334283 baseEnd_1334283 := by
    simpa [prefixWord, tailWord_1334283, baseEnd_1334283] using wordTrace_append hprefix tailTrace_1334283
  have hstable : (prefixWord ++ tailWord_1334283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334283).length < 2 ^ (prefixWord ++ tailWord_1334283).sum := by decide
  have hdescent : baseEnd_1334283 < baseStart_1334283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334307 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 8]
def baseStart_1334307 : Nat := 118140960795 + 1334307 * 2 ^ 59
def prefixEnd_1334307 : Nat := 4983230072969 + 3 ^ 40 * 1334307 * 2
def baseEnd_1334307 : Nat := 152253518146403611428031

theorem tailTrace_1334307 : CollatzResearch.WordTrace tailWord_1334307 prefixEnd_1334307 152253518146403611428031 := by
  unfold tailWord_1334307
  simp only [CollatzResearch.WordTrace]
  refine ⟨48666174377041095338137175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32444116251360730225424783 48666174377041095338137175)
  ·
    refine ⟨72999261565561643007205763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48666174377041095338137175 72999261565561643007205763)
    ·
      refine ⟨109498892348342464510808645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72999261565561643007205763 109498892348342464510808645)
      ·
        refine ⟨20531042315314212095776621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109498892348342464510808645 20531042315314212095776621)
        ·
          refine ⟨7699140868242829535916233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20531042315314212095776621 7699140868242829535916233)
          ·
            refine ⟨5774355651182122151937175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699140868242829535916233 5774355651182122151937175)
            ·
              refine ⟨8661533476773183227905763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774355651182122151937175 8661533476773183227905763)
              ·
                refine ⟨12992300215159774841858645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661533476773183227905763 12992300215159774841858645)
                ·
                  refine ⟨152253518146403611428031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12992300215159774841858645 152253518146403611428031)
                  ·
                    rfl

theorem cell22_1334307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_1334307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334307 prefixEnd_1334307 := by exact prefixLift 1334307
  have htrace : WordTrace (prefixWord ++ tailWord_1334307) baseStart_1334307 baseEnd_1334307 := by
    simpa [prefixWord, tailWord_1334307, baseEnd_1334307] using wordTrace_append hprefix tailTrace_1334307
  have hstable : (prefixWord ++ tailWord_1334307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334307).length < 2 ^ (prefixWord ++ tailWord_1334307).sum := by decide
  have hdescent : baseEnd_1334307 < baseStart_1334307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334309 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_1334309 : Nat := 118140960795 + 1334309 * 2 ^ 59
def prefixEnd_1334309 : Nat := 4983230072969 + 3 ^ 40 * 1334309 * 2
def baseEnd_1334309 : Nat := 456761239080083495734087

theorem tailTrace_1334309 : CollatzResearch.WordTrace tailWord_1334309 prefixEnd_1334309 456761239080083495734087 := by
  unfold tailWord_1334309
  simp only [CollatzResearch.WordTrace]
  refine ⟨48666247323033849679709981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32444164882022566453139987 48666247323033849679709981)
  ·
    refine ⟨18249842746137693629891243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48666247323033849679709981 18249842746137693629891243)
    ·
      refine ⟨27374764119206540444836865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18249842746137693629891243 27374764119206540444836865)
      ·
        refine ⟨20531073089404905333627649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27374764119206540444836865 20531073089404905333627649)
        ·
          refine ⟨15398304817053679000220737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20531073089404905333627649 15398304817053679000220737)
          ·
            refine ⟨11548728612790259250165553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15398304817053679000220737 11548728612790259250165553)
            ·
              refine ⟨8661546459592694437624165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11548728612790259250165553 8661546459592694437624165)
              ·
                refine ⟨1624039961173630207054531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8661546459592694437624165 1624039961173630207054531)
                ·
                  refine ⟨2436059941760445310581797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624039961173630207054531 2436059941760445310581797)
                  ·
                    refine ⟨456761239080083495734087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436059941760445310581797 456761239080083495734087)
                    ·
                      rfl

theorem cell22_1334309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_1334309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334309 prefixEnd_1334309 := by exact prefixLift 1334309
  have htrace : WordTrace (prefixWord ++ tailWord_1334309) baseStart_1334309 baseEnd_1334309 := by
    simpa [prefixWord, tailWord_1334309, baseEnd_1334309] using wordTrace_append hprefix tailTrace_1334309
  have hstable : (prefixWord ++ tailWord_1334309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334309).length < 2 ^ (prefixWord ++ tailWord_1334309).sum := by decide
  have hdescent : baseEnd_1334309 < baseStart_1334309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334339 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 4, 3]
def baseStart_1334339 : Nat := 118140960795 + 1334339 * 2 ^ 59
def prefixEnd_1334339 : Nat := 4983230072969 + 3 ^ 40 * 1334339 * 2
def baseEnd_1334339 : Nat := 456771508693173417483995

theorem tailTrace_1334339 : CollatzResearch.WordTrace tailWord_1334339 prefixEnd_1334339 456771508693173417483995 := by
  unfold tailWord_1334339
  simp only [CollatzResearch.WordTrace]
  refine ⟨48667341512925164803302071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32444894341950109868868047 48667341512925164803302071)
  ·
    refine ⟨73001012269387747204953107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48667341512925164803302071 73001012269387747204953107)
    ·
      refine ⟨109501518404081620807429661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73001012269387747204953107 109501518404081620807429661)
      ·
        refine ⟨41063069401530607802786123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109501518404081620807429661 41063069401530607802786123)
        ·
          refine ⟨61594604102295911704179185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41063069401530607802786123 61594604102295911704179185)
          ·
            refine ⟨46195953076721933778134389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61594604102295911704179185 46195953076721933778134389)
            ·
              refine ⟨4330870600942681291700099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46195953076721933778134389 4330870600942681291700099)
              ·
                refine ⟨6496305901414021937550149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330870600942681291700099 6496305901414021937550149)
                ·
                  refine ⟨1218057356515129113290653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6496305901414021937550149 1218057356515129113290653)
                  ·
                    refine ⟨456771508693173417483995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218057356515129113290653 456771508693173417483995)
                    ·
                      rfl

theorem cell22_1334339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 3].length) (baseStart_1334339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334339 prefixEnd_1334339 := by exact prefixLift 1334339
  have htrace : WordTrace (prefixWord ++ tailWord_1334339) baseStart_1334339 baseEnd_1334339 := by
    simpa [prefixWord, tailWord_1334339, baseEnd_1334339] using wordTrace_append hprefix tailTrace_1334339
  have hstable : (prefixWord ++ tailWord_1334339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334339).length < 2 ^ (prefixWord ++ tailWord_1334339).sum := by decide
  have hdescent : baseEnd_1334339 < baseStart_1334339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334354 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1334354 : Nat := 118140960795 + 1334354 * 2 ^ 59
def prefixEnd_1334354 : Nat := 4983230072969 + 3 ^ 40 * 1334354 * 2
def baseEnd_1334354 : Nat := 456776643499718378358949

theorem tailTrace_1334354 : CollatzResearch.WordTrace tailWord_1334354 prefixEnd_1334354 456776643499718378358949 := by
  unfold tailWord_1334354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12166972151967705591274529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32445259071913881576732077 12166972151967705591274529)
  ·
    refine ⟨9125229113975779193455897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12166972151967705591274529 9125229113975779193455897)
    ·
      refine ⟨6843921835481834395091923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9125229113975779193455897 6843921835481834395091923)
      ·
        refine ⟨10265882753222751592637885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843921835481834395091923 10265882753222751592637885)
        ·
          refine ⟨3849706032458531847239207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10265882753222751592637885 3849706032458531847239207)
          ·
            refine ⟨5774559048687797770858811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849706032458531847239207 5774559048687797770858811)
            ·
              refine ⟨8661838573031696656288217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774559048687797770858811 8661838573031696656288217)
              ·
                refine ⟨6496378929773772492216163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8661838573031696656288217 6496378929773772492216163)
                ·
                  refine ⟨9744568394660658738324245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496378929773772492216163 9744568394660658738324245)
                  ·
                    refine ⟨456776643499718378358949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9744568394660658738324245 456776643499718378358949)
                    ·
                      rfl

theorem cell22_1334354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1334354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334354 prefixEnd_1334354 := by exact prefixLift 1334354
  have htrace : WordTrace (prefixWord ++ tailWord_1334354) baseStart_1334354 baseEnd_1334354 := by
    simpa [prefixWord, tailWord_1334354, baseEnd_1334354] using wordTrace_append hprefix tailTrace_1334354
  have hstable : (prefixWord ++ tailWord_1334354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334354).length < 2 ^ (prefixWord ++ tailWord_1334354).sum := by decide
  have hdescent : baseEnd_1334354 < baseStart_1334354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334356 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1334356 : Nat := 118140960795 + 1334356 * 2 ^ 59
def prefixEnd_1334356 : Nat := 4983230072969 + 3 ^ 40 * 1334356 * 2
def baseEnd_1334356 : Nat := 456777328140591039808943

theorem tailTrace_1334356 : CollatzResearch.WordTrace tailWord_1334356 prefixEnd_1334356 456777328140591039808943 := by
  unfold tailWord_1334356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24333980776931788353335461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32445307702575717804447281 24333980776931788353335461)
  ·
    refine ⟨4562621395674710316250399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24333980776931788353335461 4562621395674710316250399)
    ·
      refine ⟨6843932093512065474375599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562621395674710316250399 6843932093512065474375599)
      ·
        refine ⟨10265898140268098211563399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843932093512065474375599 10265898140268098211563399)
        ·
          refine ⟨15398847210402147317345099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10265898140268098211563399 15398847210402147317345099)
          ·
            refine ⟨23098270815603220976017649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15398847210402147317345099 23098270815603220976017649)
            ·
              refine ⟨17323703111702415732013237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23098270815603220976017649 17323703111702415732013237)
              ·
                refine ⟨1624097166722101474876241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17323703111702415732013237 1624097166722101474876241)
                ·
                  refine ⟨1218072875041576106157181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624097166722101474876241 1218072875041576106157181)
                  ·
                    refine ⟨456777328140591039808943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218072875041576106157181 456777328140591039808943)
                    ·
                      rfl

theorem cell22_1334356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1334356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334356 prefixEnd_1334356 := by exact prefixLift 1334356
  have htrace : WordTrace (prefixWord ++ tailWord_1334356) baseStart_1334356 baseEnd_1334356 := by
    simpa [prefixWord, tailWord_1334356, baseEnd_1334356] using wordTrace_append hprefix tailTrace_1334356
  have hstable : (prefixWord ++ tailWord_1334356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334356).length < 2 ^ (prefixWord ++ tailWord_1334356).sum := by decide
  have hdescent : baseEnd_1334356 < baseStart_1334356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334367 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_1334367 : Nat := 118140960795 + 1334367 * 2 ^ 59
def prefixEnd_1334367 : Nat := 4983230072969 + 3 ^ 40 * 1334367 * 2
def baseEnd_1334367 : Nat := 456781093665390677783909

theorem tailTrace_1334367 : CollatzResearch.WordTrace tailWord_1334367 prefixEnd_1334367 456781093665390677783909 := by
  unfold tailWord_1334367
  simp only [CollatzResearch.WordTrace]
  refine ⟨48668362756823725585321355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32445575171215817056880903 48668362756823725585321355)
  ·
    refine ⟨73002544135235588377982033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48668362756823725585321355 73002544135235588377982033)
    ·
      refine ⟨54751908101426691283486525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73002544135235588377982033 54751908101426691283486525)
      ·
        refine ⟨20531965538035009231307447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54751908101426691283486525 20531965538035009231307447)
        ·
          refine ⟨30797948307052513846961171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20531965538035009231307447 30797948307052513846961171)
          ·
            refine ⟨46196922460578770770441757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30797948307052513846961171 46196922460578770770441757)
            ·
              refine ⟨17323845922717039038915659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46196922460578770770441757 17323845922717039038915659)
              ·
                refine ⟨25985768884075558558373489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17323845922717039038915659 25985768884075558558373489)
                ·
                  refine ⟨19489326663056668918780117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25985768884075558558373489 19489326663056668918780117)
                  ·
                    refine ⟨456781093665390677783909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19489326663056668918780117 456781093665390677783909)
                    ·
                      rfl

theorem cell22_1334367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_1334367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334367 prefixEnd_1334367 := by exact prefixLift 1334367
  have htrace : WordTrace (prefixWord ++ tailWord_1334367) baseStart_1334367 baseEnd_1334367 := by
    simpa [prefixWord, tailWord_1334367, baseEnd_1334367] using wordTrace_append hprefix tailTrace_1334367
  have hstable : (prefixWord ++ tailWord_1334367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334367).length < 2 ^ (prefixWord ++ tailWord_1334367).sum := by decide
  have hdescent : baseEnd_1334367 < baseStart_1334367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334369 : List Nat := [1, 2, 3, 1, 1, 2, 6, 6]
def baseStart_1334369 : Nat := 118140960795 + 1334369 * 2 ^ 59
def prefixEnd_1334369 : Nat := 4983230072969 + 3 ^ 40 * 1334369 * 2
def baseEnd_1334369 : Nat := 50753530922918148803767

theorem tailTrace_1334369 : CollatzResearch.WordTrace tailWord_1334369 prefixEnd_1334369 50753530922918148803767 := by
  unfold tailWord_1334369
  simp only [CollatzResearch.WordTrace]
  refine ⟨48668435702816479926894161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32445623801877653284596107 48668435702816479926894161)
  ·
    refine ⟨36501326777112359945170621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48668435702816479926894161 36501326777112359945170621)
    ·
      refine ⟨13687997541417134979438983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36501326777112359945170621 13687997541417134979438983)
      ·
        refine ⟨20531996312125702469158475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13687997541417134979438983 20531996312125702469158475)
        ·
          refine ⟨30797994468188553703737713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20531996312125702469158475 30797994468188553703737713)
          ·
            refine ⟨23098495851141415277803285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30797994468188553703737713 23098495851141415277803285)
            ·
              refine ⟨1082741993022253841147029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23098495851141415277803285 1082741993022253841147029)
              ·
                refine ⟨50753530922918148803767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1082741993022253841147029 50753530922918148803767)
                ·
                  rfl

theorem cell22_1334369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 6].length) (baseStart_1334369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334369 prefixEnd_1334369 := by exact prefixLift 1334369
  have htrace : WordTrace (prefixWord ++ tailWord_1334369) baseStart_1334369 baseEnd_1334369 := by
    simpa [prefixWord, tailWord_1334369, baseEnd_1334369] using wordTrace_append hprefix tailTrace_1334369
  have hstable : (prefixWord ++ tailWord_1334369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334369).length < 2 ^ (prefixWord ++ tailWord_1334369).sum := by decide
  have hdescent : baseEnd_1334369 < baseStart_1334369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334504 : List Nat := [2, 1, 4, 1, 2, 1, 11]
def baseStart_1334504 : Nat := 118140960795 + 1334504 * 2 ^ 59
def prefixEnd_1334504 : Nat := 4983230072969 + 3 ^ 40 * 1334504 * 2
def baseEnd_1334504 : Nat := 16919555243154369892907

theorem tailTrace_1334504 : CollatzResearch.WordTrace tailWord_1334504 prefixEnd_1334504 16919555243154369892907 := by
  unfold tailWord_1334504
  simp only [CollatzResearch.WordTrace]
  refine ⟨24336679778663698991529283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32448906371551598655372377 24336679778663698991529283)
  ·
    refine ⟨36505019667995548487293925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24336679778663698991529283 36505019667995548487293925)
    ·
      refine ⟨6844691187749165341367611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36505019667995548487293925 6844691187749165341367611)
      ·
        refine ⟨10267036781623748012051417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844691187749165341367611 10267036781623748012051417)
        ·
          refine ⟨7700277586217811009038563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10267036781623748012051417 7700277586217811009038563)
          ·
            refine ⟨11550416379326716513557845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7700277586217811009038563 11550416379326716513557845)
            ·
              refine ⟨16919555243154369892907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11550416379326716513557845 16919555243154369892907)
              ·
                rfl

theorem cell22_1334504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 11].length) (baseStart_1334504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334504 prefixEnd_1334504 := by exact prefixLift 1334504
  have htrace : WordTrace (prefixWord ++ tailWord_1334504) baseStart_1334504 baseEnd_1334504 := by
    simpa [prefixWord, tailWord_1334504, baseEnd_1334504] using wordTrace_append hprefix tailTrace_1334504
  have hstable : (prefixWord ++ tailWord_1334504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334504).length < 2 ^ (prefixWord ++ tailWord_1334504).sum := by decide
  have hdescent : baseEnd_1334504 < baseStart_1334504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334508 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_1334508 : Nat := 118140960795 + 1334508 * 2 ^ 59
def prefixEnd_1334508 : Nat := 4983230072969 + 3 ^ 40 * 1334508 * 2
def baseEnd_1334508 : Nat := 456829360846913310008477

theorem tailTrace_1334508 : CollatzResearch.WordTrace tailWord_1334508 prefixEnd_1334508 456829360846913310008477 := by
  unfold tailWord_1334508
  simp only [CollatzResearch.WordTrace]
  refine ⟨24336752724656453333102089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32449003632875271110802785 24336752724656453333102089)
  ·
    refine ⟨18252564543492339999826567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24336752724656453333102089 18252564543492339999826567)
    ·
      refine ⟨27378846815238509999739851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18252564543492339999826567 27378846815238509999739851)
      ·
        refine ⟨41068270222857764999609777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27378846815238509999739851 41068270222857764999609777)
        ·
          refine ⟨30801202667143323749707333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41068270222857764999609777 30801202667143323749707333)
          ·
            refine ⟨5775225500089373203070125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30801202667143323749707333 5775225500089373203070125)
            ·
              refine ⟨2165709562533514951151297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5775225500089373203070125 2165709562533514951151297)
              ·
                refine ⟨1624282171900136213363473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165709562533514951151297 1624282171900136213363473)
                ·
                  refine ⟨1218211628925102160022605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624282171900136213363473 1218211628925102160022605)
                  ·
                    refine ⟨456829360846913310008477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218211628925102160022605 456829360846913310008477)
                    ·
                      rfl

theorem cell22_1334508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_1334508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334508 prefixEnd_1334508 := by exact prefixLift 1334508
  have htrace : WordTrace (prefixWord ++ tailWord_1334508) baseStart_1334508 baseEnd_1334508 := by
    simpa [prefixWord, tailWord_1334508, baseEnd_1334508] using wordTrace_append hprefix tailTrace_1334508
  have hstable : (prefixWord ++ tailWord_1334508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334508).length < 2 ^ (prefixWord ++ tailWord_1334508).sum := by decide
  have hdescent : baseEnd_1334508 < baseStart_1334508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334570 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1334570 : Nat := 118140960795 + 1334570 * 2 ^ 59
def prefixEnd_1334570 : Nat := 4983230072969 + 3 ^ 40 * 1334570 * 2
def baseEnd_1334570 : Nat := 456850584713965814958287

theorem tailTrace_1334570 : CollatzResearch.WordTrace tailWord_1334570 prefixEnd_1334570 456850584713965814958287 := by
  unfold tailWord_1334570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168941693772072813740291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32450511183392194169974109 12168941693772072813740291)
  ·
    refine ⟨18253412540658109220610437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12168941693772072813740291 18253412540658109220610437)
    ·
      refine ⟨3422514851373395478864457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18253412540658109220610437 3422514851373395478864457)
      ·
        refine ⟨2566886138530046609148343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3422514851373395478864457 2566886138530046609148343)
        ·
          refine ⟨3850329207795069913722515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566886138530046609148343 3850329207795069913722515)
          ·
            refine ⟨5775493811692604870583773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850329207795069913722515 5775493811692604870583773)
            ·
              refine ⟨2165810179384726826468915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5775493811692604870583773 2165810179384726826468915)
              ·
                refine ⟨3248715269077090239703373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165810179384726826468915 3248715269077090239703373)
                ·
                  refine ⟨1218268225903908839888765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3248715269077090239703373 1218268225903908839888765)
                  ·
                    refine ⟨456850584713965814958287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218268225903908839888765 456850584713965814958287)
                    ·
                      rfl

theorem cell22_1334570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1334570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334570 prefixEnd_1334570 := by exact prefixLift 1334570
  have htrace : WordTrace (prefixWord ++ tailWord_1334570) baseStart_1334570 baseEnd_1334570 := by
    simpa [prefixWord, tailWord_1334570, baseEnd_1334570] using wordTrace_append hprefix tailTrace_1334570
  have hstable : (prefixWord ++ tailWord_1334570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334570).length < 2 ^ (prefixWord ++ tailWord_1334570).sum := by decide
  have hdescent : baseEnd_1334570 < baseStart_1334570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334621 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1334621 : Nat := 118140960795 + 1334621 * 2 ^ 59
def prefixEnd_1334621 : Nat := 4983230072969 + 3 ^ 40 * 1334621 * 2
def baseEnd_1334621 : Nat := 456868043056218681933131

theorem tailTrace_1334621 : CollatzResearch.WordTrace tailWord_1334621 prefixEnd_1334621 456868043056218681933131 := by
  unfold tailWord_1334621
  simp only [CollatzResearch.WordTrace]
  refine ⟨48677626897903526965067717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32451751265269017976711811 48677626897903526965067717)
  ·
    refine ⟨9127055043356911305950197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48677626897903526965067717 9127055043356911305950197)
    ·
      refine ⟨855661410314710434932831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9127055043356911305950197 855661410314710434932831)
      ·
        refine ⟨1283492115472065652399247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855661410314710434932831 1283492115472065652399247)
        ·
          refine ⟨1925238173208098478598871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283492115472065652399247 1925238173208098478598871)
          ·
            refine ⟨2887857259812147717898307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925238173208098478598871 2887857259812147717898307)
            ·
              refine ⟨4331785889718221576847461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887857259812147717898307 4331785889718221576847461)
              ·
                refine ⟨812209854322166545658899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4331785889718221576847461 812209854322166545658899)
                ·
                  refine ⟨1218314781483249818488349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812209854322166545658899 1218314781483249818488349)
                  ·
                    refine ⟨456868043056218681933131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218314781483249818488349 456868043056218681933131)
                    ·
                      rfl

theorem cell22_1334621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1334621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334621 prefixEnd_1334621 := by exact prefixLift 1334621
  have htrace : WordTrace (prefixWord ++ tailWord_1334621) baseStart_1334621 baseEnd_1334621 := by
    simpa [prefixWord, tailWord_1334621, baseEnd_1334621] using wordTrace_append hprefix tailTrace_1334621
  have hstable : (prefixWord ++ tailWord_1334621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334621).length < 2 ^ (prefixWord ++ tailWord_1334621).sum := by decide
  have hdescent : baseEnd_1334621 < baseStart_1334621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334641 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_1334641 : Nat := 118140960795 + 1334641 * 2 ^ 59
def prefixEnd_1334641 : Nat := 4983230072969 + 3 ^ 40 * 1334641 * 2
def baseEnd_1334641 : Nat := 456874889464945296433069

theorem tailTrace_1334641 : CollatzResearch.WordTrace tailWord_1334641 prefixEnd_1334641 456874889464945296433069 := by
  unfold tailWord_1334641
  simp only [CollatzResearch.WordTrace]
  refine ⟨48678356357831070380795777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32452237571887380253863851 48678356357831070380795777)
  ·
    refine ⟨36508767268373302785596833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48678356357831070380795777 36508767268373302785596833)
    ·
      refine ⟨27381575451279977089197625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36508767268373302785596833 27381575451279977089197625)
      ·
        refine ⟨20536181588459982816898219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27381575451279977089197625 20536181588459982816898219)
        ·
          refine ⟨30804272382689974225347329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20536181588459982816898219 30804272382689974225347329)
          ·
            refine ⟨23103204287017480669010497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30804272382689974225347329 23103204287017480669010497)
            ·
              refine ⟨17327403215263110501757873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23103204287017480669010497 17327403215263110501757873)
              ·
                refine ⟨12995552411447332876318405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17327403215263110501757873 12995552411447332876318405)
                ·
                  refine ⟨2436666077146374914309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12995552411447332876318405 2436666077146374914309701)
                  ·
                    refine ⟨456874889464945296433069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436666077146374914309701 456874889464945296433069)
                    ·
                      rfl

theorem cell22_1334641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_1334641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334641 prefixEnd_1334641 := by exact prefixLift 1334641
  have htrace : WordTrace (prefixWord ++ tailWord_1334641) baseStart_1334641 baseEnd_1334641 := by
    simpa [prefixWord, tailWord_1334641, baseEnd_1334641] using wordTrace_append hprefix tailTrace_1334641
  have hstable : (prefixWord ++ tailWord_1334641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334641).length < 2 ^ (prefixWord ++ tailWord_1334641).sum := by decide
  have hdescent : baseEnd_1334641 < baseStart_1334641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334778 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_1334778 : Nat := 118140960795 + 1334778 * 2 ^ 59
def prefixEnd_1334778 : Nat := 4983230072969 + 3 ^ 40 * 1334778 * 2
def baseEnd_1334778 : Nat := 456921787364722605757649

theorem tailTrace_1334778 : CollatzResearch.WordTrace tailWord_1334778 prefixEnd_1334778 456921787364722605757649 := by
  unfold tailWord_1334778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12170838289583685694633247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32455568772223161852355325 12170838289583685694633247)
  ·
    refine ⟨18256257434375528541949871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12170838289583685694633247 18256257434375528541949871)
    ·
      refine ⟨27384386151563292812924807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18256257434375528541949871 27384386151563292812924807)
      ·
        refine ⟨41076579227344939219387211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27384386151563292812924807 41076579227344939219387211)
        ·
          refine ⟨61614868841017408829080817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41076579227344939219387211 61614868841017408829080817)
          ·
            refine ⟨46211151630763056621810613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61614868841017408829080817 46211151630763056621810613)
            ·
              refine ⟨4332295465384036558294745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46211151630763056621810613 4332295465384036558294745)
              ·
                refine ⟨3249221599038027418721059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4332295465384036558294745 3249221599038027418721059)
                ·
                  refine ⟨4873832398557041128081589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249221599038027418721059 4873832398557041128081589)
                  ·
                    refine ⟨456921787364722605757649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4873832398557041128081589 456921787364722605757649)
                    ·
                      rfl

theorem cell22_1334778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_1334778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334778 prefixEnd_1334778 := by exact prefixLift 1334778
  have htrace : WordTrace (prefixWord ++ tailWord_1334778) baseStart_1334778 baseEnd_1334778 := by
    simpa [prefixWord, tailWord_1334778, baseEnd_1334778] using wordTrace_append hprefix tailTrace_1334778
  have hstable : (prefixWord ++ tailWord_1334778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334778).length < 2 ^ (prefixWord ++ tailWord_1334778).sum := by decide
  have hdescent : baseEnd_1334778 < baseStart_1334778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334793 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_1334793 : Nat := 118140960795 + 1334793 * 2 ^ 59
def prefixEnd_1334793 : Nat := 4983230072969 + 3 ^ 40 * 1334793 * 2
def baseEnd_1334793 : Nat := 456926922171267566632603

theorem tailTrace_1334793 : CollatzResearch.WordTrace tailWord_1334793 prefixEnd_1334793 456926922171267566632603 := by
  unfold tailWord_1334793
  simp only [CollatzResearch.WordTrace]
  refine ⟨48683900253280400340329033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32455933502186933560219355 48683900253280400340329033)
  ·
    refine ⟨36512925189960300255246775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48683900253280400340329033 36512925189960300255246775)
    ·
      refine ⟨54769387784940450382870163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36512925189960300255246775 54769387784940450382870163)
      ·
        refine ⟨82154081677410675574305245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54769387784940450382870163 82154081677410675574305245)
        ·
          refine ⟨30807780629029003340364467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82154081677410675574305245 30807780629029003340364467)
          ·
            refine ⟨46211670943543505010546701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30807780629029003340364467 46211670943543505010546701)
            ·
              refine ⟨17329376603828814378955013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46211670943543505010546701 17329376603828814378955013)
              ·
                refine ⟨3249258113217902696054065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17329376603828814378955013 3249258113217902696054065)
                ·
                  refine ⟨2436943584913427022040549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249258113217902696054065 2436943584913427022040549)
                  ·
                    refine ⟨456926922171267566632603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436943584913427022040549 456926922171267566632603)
                    ·
                      rfl

theorem cell22_1334793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_1334793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334793 prefixEnd_1334793 := by exact prefixLift 1334793
  have htrace : WordTrace (prefixWord ++ tailWord_1334793) baseStart_1334793 baseEnd_1334793 := by
    simpa [prefixWord, tailWord_1334793, baseEnd_1334793] using wordTrace_append hprefix tailTrace_1334793
  have hstable : (prefixWord ++ tailWord_1334793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334793).length < 2 ^ (prefixWord ++ tailWord_1334793).sum := by decide
  have hdescent : baseEnd_1334793 < baseStart_1334793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334853 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 7]
def baseStart_1334853 : Nat := 118140960795 + 1334853 * 2 ^ 59
def prefixEnd_1334853 : Nat := 4983230072969 + 3 ^ 40 * 1334853 * 2
def baseEnd_1334853 : Nat := 152315820465815803377473

theorem tailTrace_1334853 : CollatzResearch.WordTrace tailWord_1334853 prefixEnd_1334853 152315820465815803377473 := by
  unfold tailWord_1334853
  simp only [CollatzResearch.WordTrace]
  refine ⟨48686088633063030587513213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32457392422042020391675475 48686088633063030587513213)
  ·
    refine ⟨18257283237398636470317455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48686088633063030587513213 18257283237398636470317455)
    ·
      refine ⟨27385924856097954705476183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18257283237398636470317455 27385924856097954705476183)
      ·
        refine ⟨41078887284146932058214275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27385924856097954705476183 41078887284146932058214275)
        ·
          refine ⟨61618330926220398087321413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41078887284146932058214275 61618330926220398087321413)
          ·
            refine ⟨11553437048666324641372765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61618330926220398087321413 11553437048666324641372765)
            ·
              refine ⟨4332538893249871740514787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11553437048666324641372765 4332538893249871740514787)
              ·
                refine ⟨6498808339874807610772181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332538893249871740514787 6498808339874807610772181)
                ·
                  refine ⟨152315820465815803377473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6498808339874807610772181 152315820465815803377473)
                  ·
                    rfl

theorem cell22_1334853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_1334853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334853 prefixEnd_1334853 := by exact prefixLift 1334853
  have htrace : WordTrace (prefixWord ++ tailWord_1334853) baseStart_1334853 baseEnd_1334853 := by
    simpa [prefixWord, tailWord_1334853, baseEnd_1334853] using wordTrace_append hprefix tailTrace_1334853
  have hstable : (prefixWord ++ tailWord_1334853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334853).length < 2 ^ (prefixWord ++ tailWord_1334853).sum := by decide
  have hdescent : baseEnd_1334853 < baseStart_1334853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334928 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_1334928 : Nat := 118140960795 + 1334928 * 2 ^ 59
def prefixEnd_1334928 : Nat := 4983230072969 + 3 ^ 40 * 1334928 * 2
def baseEnd_1334928 : Nat := 456973135430172214507189

theorem tailTrace_1334928 : CollatzResearch.WordTrace tailWord_1334928 prefixEnd_1334928 456973135430172214507189 := by
  unfold tailWord_1334928
  simp only [CollatzResearch.WordTrace]
  refine ⟨24344412053895659198246719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32459216071860878930995625 24344412053895659198246719)
  ·
    refine ⟨36516618080843488797370079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24344412053895659198246719 36516618080843488797370079)
    ·
      refine ⟨54774927121265233196055119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36516618080843488797370079 54774927121265233196055119)
      ·
        refine ⟨82162390681897849794082679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54774927121265233196055119 82162390681897849794082679)
        ·
          refine ⟨123243586022846774691124019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82162390681897849794082679 123243586022846774691124019)
          ·
            refine ⟨184865379034270162036686029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123243586022846774691124019 184865379034270162036686029)
            ·
              refine ⟨69324517137851310763757261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184865379034270162036686029 69324517137851310763757261)
              ·
                refine ⟨25996693926694241536408973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69324517137851310763757261 25996693926694241536408973)
                ·
                  refine ⟨9748760222510340576153365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25996693926694241536408973 9748760222510340576153365)
                  ·
                    refine ⟨456973135430172214507189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9748760222510340576153365 456973135430172214507189)
                    ·
                      rfl

theorem cell22_1334928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_1334928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334928 prefixEnd_1334928 := by exact prefixLift 1334928
  have htrace : WordTrace (prefixWord ++ tailWord_1334928) baseStart_1334928 baseEnd_1334928 := by
    simpa [prefixWord, tailWord_1334928, baseEnd_1334928] using wordTrace_append hprefix tailTrace_1334928
  have hstable : (prefixWord ++ tailWord_1334928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334928).length < 2 ^ (prefixWord ++ tailWord_1334928).sum := by decide
  have hdescent : baseEnd_1334928 < baseStart_1334928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334966 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1334966 : Nat := 118140960795 + 1334966 * 2 ^ 59
def prefixEnd_1334966 : Nat := 4983230072969 + 3 ^ 40 * 1334966 * 2
def baseEnd_1334966 : Nat := 152328714535584260685691

theorem tailTrace_1334966 : CollatzResearch.WordTrace tailWord_1334966 prefixEnd_1334966 152328714535584260685691 := by
  unfold tailWord_1334966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043138130103353180398547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32460140054435767257584501 3043138130103353180398547)
  ·
    refine ⟨4564707195155029770597821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3043138130103353180398547 4564707195155029770597821)
    ·
      refine ⟨1711765198183136163974183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4564707195155029770597821 1711765198183136163974183)
      ·
        refine ⟨2567647797274704245961275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711765198183136163974183 2567647797274704245961275)
        ·
          refine ⟨3851471695912056368941913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567647797274704245961275 3851471695912056368941913)
          ·
            refine ⟨2888603771934042276706435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3851471695912056368941913 2888603771934042276706435)
            ·
              refine ⟨4332905657901063415059653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2888603771934042276706435 4332905657901063415059653)
              ·
                refine ⟨812419810856449390323685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4332905657901063415059653 812419810856449390323685)
                ·
                  refine ⟨152328714535584260685691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 812419810856449390323685 152328714535584260685691)
                  ·
                    rfl

theorem cell22_1334966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1334966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334966 prefixEnd_1334966 := by exact prefixLift 1334966
  have htrace : WordTrace (prefixWord ++ tailWord_1334966) baseStart_1334966 baseEnd_1334966 := by
    simpa [prefixWord, tailWord_1334966, baseEnd_1334966] using wordTrace_append hprefix tailTrace_1334966
  have hstable : (prefixWord ++ tailWord_1334966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334966).length < 2 ^ (prefixWord ++ tailWord_1334966).sum := by decide
  have hdescent : baseEnd_1334966 < baseStart_1334966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334990 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1334990 : Nat := 118140960795 + 1334990 * 2 ^ 59
def prefixEnd_1334990 : Nat := 4983230072969 + 3 ^ 40 * 1334990 * 2
def baseEnd_1334990 : Nat := 456994359297224719456999

theorem tailTrace_1334990 : CollatzResearch.WordTrace tailWord_1334990 prefixEnd_1334990 456994359297224719456999 := by
  unfold tailWord_1334990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086385679195837873156303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32460723622377801990166949 6086385679195837873156303)
  ·
    refine ⟨9129578518793756809734455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6086385679195837873156303 9129578518793756809734455)
    ·
      refine ⟨13694367778190635214601683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9129578518793756809734455 13694367778190635214601683)
      ·
        refine ⟨20541551667285952821902525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13694367778190635214601683 20541551667285952821902525)
        ·
          refine ⟨7703081875232232308213447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20541551667285952821902525 7703081875232232308213447)
          ·
            refine ⟨11554622812848348462320171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703081875232232308213447 11554622812848348462320171)
            ·
              refine ⟨17331934219272522693480257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11554622812848348462320171 17331934219272522693480257)
              ·
                refine ⟨12998950664454392020110193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17331934219272522693480257 12998950664454392020110193)
                ·
                  refine ⟨9749212998340794015082645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12998950664454392020110193 9749212998340794015082645)
                  ·
                    refine ⟨456994359297224719456999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9749212998340794015082645 456994359297224719456999)
                    ·
                      rfl

theorem cell22_1334990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1334990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1334990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1334990 prefixEnd_1334990 := by exact prefixLift 1334990
  have htrace : WordTrace (prefixWord ++ tailWord_1334990) baseStart_1334990 baseEnd_1334990 := by
    simpa [prefixWord, tailWord_1334990, baseEnd_1334990] using wordTrace_append hprefix tailTrace_1334990
  have hstable : (prefixWord ++ tailWord_1334990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334990).length < 2 ^ (prefixWord ++ tailWord_1334990).sum := by decide
  have hdescent : baseEnd_1334990 < baseStart_1334990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335020 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1335020 : Nat := 118140960795 + 1335020 * 2 ^ 59
def prefixEnd_1335020 : Nat := 4983230072969 + 3 ^ 40 * 1335020 * 2
def baseEnd_1335020 : Nat := 457004628910314641206907

theorem tailTrace_1335020 : CollatzResearch.WordTrace tailWord_1335020 prefixEnd_1335020 457004628910314641206907 := by
  unfold tailWord_1335020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24346089811729009054421257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32461453082305345405895009 24346089811729009054421257)
  ·
    refine ⟨18259567358796756790815943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24346089811729009054421257 18259567358796756790815943)
    ·
      refine ⟨27389351038195135186223915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18259567358796756790815943 27389351038195135186223915)
      ·
        refine ⟨41084026557292702779335873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27389351038195135186223915 41084026557292702779335873)
        ·
          refine ⟨30813019917969527084501905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41084026557292702779335873 30813019917969527084501905)
          ·
            refine ⟨23109764938477145313376429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30813019917969527084501905 23109764938477145313376429)
            ·
              refine ⟨8666161851928929492516161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23109764938477145313376429 8666161851928929492516161)
              ·
                refine ⟨6499621388946697119387121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8666161851928929492516161 6499621388946697119387121)
                ·
                  refine ⟨4874716041710022839540341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6499621388946697119387121 4874716041710022839540341)
                  ·
                    refine ⟨457004628910314641206907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4874716041710022839540341 457004628910314641206907)
                    ·
                      rfl

theorem cell22_1335020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1335020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335020 prefixEnd_1335020 := by exact prefixLift 1335020
  have htrace : WordTrace (prefixWord ++ tailWord_1335020) baseStart_1335020 baseEnd_1335020 := by
    simpa [prefixWord, tailWord_1335020, baseEnd_1335020] using wordTrace_append hprefix tailTrace_1335020
  have hstable : (prefixWord ++ tailWord_1335020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335020).length < 2 ^ (prefixWord ++ tailWord_1335020).sum := by decide
  have hdescent : baseEnd_1335020 < baseStart_1335020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335035 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 3, 4]
def baseStart_1335035 : Nat := 118140960795 + 1335035 * 2 ^ 59
def prefixEnd_1335035 : Nat := 4983230072969 + 3 ^ 40 * 1335035 * 2
def baseEnd_1335035 : Nat := 457009763716859602081861

theorem tailTrace_1335035 : CollatzResearch.WordTrace tailWord_1335035 prefixEnd_1335035 457009763716859602081861 := by
  unfold tailWord_1335035
  simp only [CollatzResearch.WordTrace]
  refine ⟨48692726718403675670638559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32461817812269117113759039 48692726718403675670638559)
  ·
    refine ⟨73039090077605513505957839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48692726718403675670638559 73039090077605513505957839)
    ·
      refine ⟨109558635116408270258936759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73039090077605513505957839 109558635116408270258936759)
      ·
        refine ⟨164337952674612405388405139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109558635116408270258936759 164337952674612405388405139)
        ·
          refine ⟨246506929011918608082607709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164337952674612405388405139 246506929011918608082607709)
          ·
            refine ⟨92440098379469478030977891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246506929011918608082607709 92440098379469478030977891)
            ·
              refine ⟨138660147569204217046466837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92440098379469478030977891 138660147569204217046466837)
              ·
                refine ⟨6499694417306447674053133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138660147569204217046466837 6499694417306447674053133)
                ·
                  refine ⟨2437385406489917877769925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6499694417306447674053133 2437385406489917877769925)
                  ·
                    refine ⟨457009763716859602081861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437385406489917877769925 457009763716859602081861)
                    ·
                      rfl

theorem cell22_1335035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_1335035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335035 prefixEnd_1335035 := by exact prefixLift 1335035
  have htrace : WordTrace (prefixWord ++ tailWord_1335035) baseStart_1335035 baseEnd_1335035 := by
    simpa [prefixWord, tailWord_1335035, baseEnd_1335035] using wordTrace_append hprefix tailTrace_1335035
  have hstable : (prefixWord ++ tailWord_1335035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335035).length < 2 ^ (prefixWord ++ tailWord_1335035).sum := by decide
  have hdescent : baseEnd_1335035 < baseStart_1335035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335052 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_1335052 : Nat := 118140960795 + 1335052 * 2 ^ 59
def prefixEnd_1335052 : Nat := 4983230072969 + 3 ^ 40 * 1335052 * 2
def baseEnd_1335052 : Nat := 457015583164277224406809

theorem tailTrace_1335052 : CollatzResearch.WordTrace tailWord_1335052 prefixEnd_1335052 457015583164277224406809 := by
  unfold tailWord_1335052
  simp only [CollatzResearch.WordTrace]
  refine ⟨24346673379671043787003705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32462231172894725049338273 24346673379671043787003705)
  ·
    refine ⟨18260005034753282840252779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24346673379671043787003705 18260005034753282840252779)
    ·
      refine ⟨27390007552129924260379169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18260005034753282840252779 27390007552129924260379169)
      ·
        refine ⟨20542505664097443195284377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27390007552129924260379169 20542505664097443195284377)
        ·
          refine ⟨15406879248073082396463283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20542505664097443195284377 15406879248073082396463283)
          ·
            refine ⟨23110318872109623594694925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15406879248073082396463283 23110318872109623594694925)
            ·
              refine ⟨8666369577041108848010597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23110318872109623594694925 8666369577041108848010597)
              ·
                refine ⟨1624944295695207909001987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8666369577041108848010597 1624944295695207909001987)
                ·
                  refine ⟨2437416443542811863502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624944295695207909001987 2437416443542811863502981)
                  ·
                    refine ⟨457015583164277224406809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437416443542811863502981 457015583164277224406809)
                    ·
                      rfl

theorem cell22_1335052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_1335052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335052 prefixEnd_1335052 := by exact prefixLift 1335052
  have htrace : WordTrace (prefixWord ++ tailWord_1335052) baseStart_1335052 baseEnd_1335052 := by
    simpa [prefixWord, tailWord_1335052, baseEnd_1335052] using wordTrace_append hprefix tailTrace_1335052
  have hstable : (prefixWord ++ tailWord_1335052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335052).length < 2 ^ (prefixWord ++ tailWord_1335052).sum := by decide
  have hdescent : baseEnd_1335052 < baseStart_1335052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335144 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1335144 : Nat := 118140960795 + 1335144 * 2 ^ 59
def prefixEnd_1335144 : Nat := 4983230072969 + 3 ^ 40 * 1335144 * 2
def baseEnd_1335144 : Nat := 457047076644419651106527

theorem tailTrace_1335144 : CollatzResearch.WordTrace tailWord_1335144 prefixEnd_1335144 457047076644419651106527 := by
  unfold tailWord_1335144
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348351137504393643178243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32464468183339191524237657 24348351137504393643178243)
  ·
    refine ⟨36522526706256590464767365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24348351137504393643178243 36522526706256590464767365)
    ·
      refine ⟨6847973757423110712143881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36522526706256590464767365 6847973757423110712143881)
      ·
        refine ⟨5135980318067333034107911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6847973757423110712143881 5135980318067333034107911)
        ·
          refine ⟨7703970477100999551161867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135980318067333034107911 7703970477100999551161867)
          ·
            refine ⟨11555955715651499326742801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703970477100999551161867 11555955715651499326742801)
            ·
              refine ⟨8666966786738624495057101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11555955715651499326742801 8666966786738624495057101)
              ·
                refine ⟨3250112545026984185646413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8666966786738624495057101 3250112545026984185646413)
                ·
                  refine ⟨1218792204385119069617405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3250112545026984185646413 1218792204385119069617405)
                  ·
                    refine ⟨457047076644419651106527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218792204385119069617405 457047076644419651106527)
                    ·
                      rfl

theorem cell22_1335144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1335144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335144 prefixEnd_1335144 := by exact prefixLift 1335144
  have htrace : WordTrace (prefixWord ++ tailWord_1335144) baseStart_1335144 baseEnd_1335144 := by
    simpa [prefixWord, tailWord_1335144, baseEnd_1335144] using wordTrace_append hprefix tailTrace_1335144
  have hstable : (prefixWord ++ tailWord_1335144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335144).length < 2 ^ (prefixWord ++ tailWord_1335144).sum := by decide
  have hdescent : baseEnd_1335144 < baseStart_1335144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335146 : List Nat := [3, 1, 3, 4, 1, 2, 1, 7]
def baseStart_1335146 : Nat := 118140960795 + 1335146 * 2 ^ 59
def prefixEnd_1335146 : Nat := 4983230072969 + 3 ^ 40 * 1335146 * 2
def baseEnd_1335146 : Nat := 50783084587254701395169

theorem tailTrace_1335146 : CollatzResearch.WordTrace tailWord_1335146 prefixEnd_1335146 50783084587254701395169 := by
  unfold tailWord_1335146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12174193805250385406982323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32464516814001027751952861 12174193805250385406982323)
  ·
    refine ⟨18261290707875578110473485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12174193805250385406982323 18261290707875578110473485)
    ·
      refine ⟨6847984015453341791427557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18261290707875578110473485 6847984015453341791427557)
      ·
        refine ⟨1283997002897501585892667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6847984015453341791427557 1283997002897501585892667)
        ·
          refine ⟨1925995504346252378839001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283997002897501585892667 1925995504346252378839001)
          ·
            refine ⟨1444496628259689284129251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1925995504346252378839001 1444496628259689284129251)
            ·
              refine ⟨2166744942389533926193877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444496628259689284129251 2166744942389533926193877)
              ·
                refine ⟨50783084587254701395169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2166744942389533926193877 50783084587254701395169)
                ·
                  rfl

theorem cell22_1335146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_1335146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335146 prefixEnd_1335146 := by exact prefixLift 1335146
  have htrace : WordTrace (prefixWord ++ tailWord_1335146) baseStart_1335146 baseEnd_1335146 := by
    simpa [prefixWord, tailWord_1335146, baseEnd_1335146] using wordTrace_append hprefix tailTrace_1335146
  have hstable : (prefixWord ++ tailWord_1335146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335146).length < 2 ^ (prefixWord ++ tailWord_1335146).sum := by decide
  have hdescent : baseEnd_1335146 < baseStart_1335146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335221 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1335221 : Nat := 118140960795 + 1335221 * 2 ^ 59
def prefixEnd_1335221 : Nat := 4983230072969 + 3 ^ 40 * 1335221 * 2
def baseEnd_1335221 : Nat := 457073435318017116931291

theorem tailTrace_1335221 : CollatzResearch.WordTrace tailWord_1335221 prefixEnd_1335221 457073435318017116931291 := by
  unfold tailWord_1335221
  simp only [CollatzResearch.WordTrace]
  refine ⟨48699510695729829436909517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32466340463819886291273011 48699510695729829436909517)
  ·
    refine ⟨18262316510898686038841069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48699510695729829436909517 18262316510898686038841069)
    ·
      refine ⟨6848368691587007264565401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18262316510898686038841069 6848368691587007264565401)
      ·
        refine ⟨5136276518690255448424051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6848368691587007264565401 5136276518690255448424051)
        ·
          refine ⟨7704414778035383172636077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136276518690255448424051 7704414778035383172636077)
          ·
            refine ⟨2889155541763268689738529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7704414778035383172636077 2889155541763268689738529)
            ·
              refine ⟨2166866656322451517303897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2889155541763268689738529 2166866656322451517303897)
              ·
                refine ⟨1625149992241838637977923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166866656322451517303897 1625149992241838637977923)
                ·
                  refine ⟨2437724988362757956966885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625149992241838637977923 2437724988362757956966885)
                  ·
                    refine ⟨457073435318017116931291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437724988362757956966885 457073435318017116931291)
                    ·
                      rfl

theorem cell22_1335221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1335221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335221 prefixEnd_1335221 := by exact prefixLift 1335221
  have htrace : WordTrace (prefixWord ++ tailWord_1335221) baseStart_1335221 baseEnd_1335221 := by
    simpa [prefixWord, tailWord_1335221, baseEnd_1335221] using wordTrace_append hprefix tailTrace_1335221
  have hstable : (prefixWord ++ tailWord_1335221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335221).length < 2 ^ (prefixWord ++ tailWord_1335221).sum := by decide
  have hdescent : baseEnd_1335221 < baseStart_1335221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335232 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_1335232 : Nat := 118140960795 + 1335232 * 2 ^ 59
def prefixEnd_1335232 : Nat := 4983230072969 + 3 ^ 40 * 1335232 * 2
def baseEnd_1335232 : Nat := 457077200842816754906257

theorem tailTrace_1335232 : CollatzResearch.WordTrace tailWord_1335232 prefixEnd_1335232 457077200842816754906257 := by
  unfold tailWord_1335232
  simp only [CollatzResearch.WordTrace]
  refine ⟨24349955949344989157779975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32466607932459985543706633 24349955949344989157779975)
  ·
    refine ⟨36524933924017483736669963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24349955949344989157779975 36524933924017483736669963)
    ·
      refine ⟨54787400886026225605004945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36524933924017483736669963 54787400886026225605004945)
      ·
        refine ⟨41090550664519669203753709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54787400886026225605004945 41090550664519669203753709)
        ·
          refine ⟨15408956499194875951407641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41090550664519669203753709 15408956499194875951407641)
          ·
            refine ⟨11556717374396156963555731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15408956499194875951407641 11556717374396156963555731)
            ·
              refine ⟨17335076061594235445333597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11556717374396156963555731 17335076061594235445333597)
              ·
                refine ⟨6500653523097838292000099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17335076061594235445333597 6500653523097838292000099)
                ·
                  refine ⟨9750980284646757438000149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6500653523097838292000099 9750980284646757438000149)
                  ·
                    refine ⟨457077200842816754906257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9750980284646757438000149 457077200842816754906257)
                    ·
                      rfl

theorem cell22_1335232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_1335232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335232 prefixEnd_1335232 := by exact prefixLift 1335232
  have htrace : WordTrace (prefixWord ++ tailWord_1335232) baseStart_1335232 baseEnd_1335232 := by
    simpa [prefixWord, tailWord_1335232, baseEnd_1335232] using wordTrace_append hprefix tailTrace_1335232
  have hstable : (prefixWord ++ tailWord_1335232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335232).length < 2 ^ (prefixWord ++ tailWord_1335232).sum := by decide
  have hdescent : baseEnd_1335232 < baseStart_1335232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335253 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 4]
def baseStart_1335253 : Nat := 118140960795 + 1335253 * 2 ^ 59
def prefixEnd_1335253 : Nat := 4983230072969 + 3 ^ 40 * 1335253 * 2
def baseEnd_1335253 : Nat := 152361463190659900043731

theorem tailTrace_1335253 : CollatzResearch.WordTrace tailWord_1335253 prefixEnd_1335253 152361463190659900043731 := by
  unfold tailWord_1335253
  simp only [CollatzResearch.WordTrace]
  refine ⟨48700677831613898902074413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32467118554409265934716275 48700677831613898902074413)
  ·
    refine ⟨18262754186855212088277905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48700677831613898902074413 18262754186855212088277905)
    ·
      refine ⟨13697065640141409066208429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18262754186855212088277905 13697065640141409066208429)
      ·
        refine ⟨5136399615053028399828161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13697065640141409066208429 5136399615053028399828161)
        ·
          refine ⟨3852299711289771299871121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5136399615053028399828161 3852299711289771299871121)
          ·
            refine ⟨2889224783467328474903341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3852299711289771299871121 2889224783467328474903341)
            ·
              refine ⟨1083459293800248178088753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2889224783467328474903341 1083459293800248178088753)
              ·
                refine ⟨812594470350186133566565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083459293800248178088753 812594470350186133566565)
                ·
                  refine ⟨152361463190659900043731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 812594470350186133566565 152361463190659900043731)
                  ·
                    rfl

theorem cell22_1335253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_1335253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335253 prefixEnd_1335253 := by exact prefixLift 1335253
  have htrace : WordTrace (prefixWord ++ tailWord_1335253) baseStart_1335253 baseEnd_1335253 := by
    simpa [prefixWord, tailWord_1335253, baseEnd_1335253] using wordTrace_append hprefix tailTrace_1335253
  have hstable : (prefixWord ++ tailWord_1335253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335253).length < 2 ^ (prefixWord ++ tailWord_1335253).sum := by decide
  have hdescent : baseEnd_1335253 < baseStart_1335253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335279 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 5, 3]
def baseStart_1335279 : Nat := 118140960795 + 1335279 * 2 ^ 59
def prefixEnd_1335279 : Nat := 4983230072969 + 3 ^ 40 * 1335279 * 2
def baseEnd_1335279 : Nat := 457093289903324298981113

theorem tailTrace_1335279 : CollatzResearch.WordTrace tailWord_1335279 prefixEnd_1335279 457093289903324298981113 := by
  unfold tailWord_1335279
  simp only [CollatzResearch.WordTrace]
  refine ⟨48701626129519705342520891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32467750753013136895013927 48701626129519705342520891)
  ·
    refine ⟨73052439194279558013781337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48701626129519705342520891 73052439194279558013781337)
    ·
      refine ⟨54789329395709668510336003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73052439194279558013781337 54789329395709668510336003)
      ·
        refine ⟨82183994093564502765504005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54789329395709668510336003 82183994093564502765504005)
        ·
          refine ⟨15409498892543344268532001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82183994093564502765504005 15409498892543344268532001)
          ·
            refine ⟨11557124169407508201399001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15409498892543344268532001 11557124169407508201399001)
            ·
              refine ⟨8667843127055631151049251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11557124169407508201399001 8667843127055631151049251)
              ·
                refine ⟨13001764690583446726573877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667843127055631151049251 13001764690583446726573877)
                ·
                  refine ⟨1218915439742198130616301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13001764690583446726573877 1218915439742198130616301)
                  ·
                    refine ⟨457093289903324298981113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218915439742198130616301 457093289903324298981113)
                    ·
                      rfl

theorem cell22_1335279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_1335279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335279 prefixEnd_1335279 := by exact prefixLift 1335279
  have htrace : WordTrace (prefixWord ++ tailWord_1335279) baseStart_1335279 baseEnd_1335279 := by
    simpa [prefixWord, tailWord_1335279, baseEnd_1335279] using wordTrace_append hprefix tailTrace_1335279
  have hstable : (prefixWord ++ tailWord_1335279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335279).length < 2 ^ (prefixWord ++ tailWord_1335279).sum := by decide
  have hdescent : baseEnd_1335279 < baseStart_1335279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335324 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1335324 : Nat := 118140960795 + 1335324 * 2 ^ 59
def prefixEnd_1335324 : Nat := 4983230072969 + 3 ^ 40 * 1335324 * 2
def baseEnd_1335324 : Nat := 457108694322959181605975

theorem tailTrace_1335324 : CollatzResearch.WordTrace tailWord_1335324 prefixEnd_1335324 457108694322959181605975 := by
  unfold tailWord_1335324
  simp only [CollatzResearch.WordTrace]
  refine ⟨24351633707178339013954513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32468844942904452018606017 24351633707178339013954513)
  ·
    refine ⟨18263725280383754260465885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24351633707178339013954513 18263725280383754260465885)
    ·
      refine ⟨6848896980143907847674707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18263725280383754260465885 6848896980143907847674707)
      ·
        refine ⟨10273345470215861771512061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848896980143907847674707 10273345470215861771512061)
        ·
          refine ⟨3852504551330948164317023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10273345470215861771512061 3852504551330948164317023)
          ·
            refine ⟨5778756826996422246475535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852504551330948164317023 5778756826996422246475535)
            ·
              refine ⟨8668135240494633369713303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778756826996422246475535 8668135240494633369713303)
              ·
                refine ⟨13002202860741950054569955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668135240494633369713303 13002202860741950054569955)
                ·
                  refine ⟨19503304291112925081854933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13002202860741950054569955 19503304291112925081854933)
                  ·
                    refine ⟨457108694322959181605975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19503304291112925081854933 457108694322959181605975)
                    ·
                      rfl

theorem cell22_1335324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1335324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335324 prefixEnd_1335324 := by exact prefixLift 1335324
  have htrace : WordTrace (prefixWord ++ tailWord_1335324) baseStart_1335324 baseEnd_1335324 := by
    simpa [prefixWord, tailWord_1335324, baseEnd_1335324] using wordTrace_append hprefix tailTrace_1335324
  have hstable : (prefixWord ++ tailWord_1335324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335324).length < 2 ^ (prefixWord ++ tailWord_1335324).sum := by decide
  have hdescent : baseEnd_1335324 < baseStart_1335324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335356 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_1335356 : Nat := 118140960795 + 1335356 * 2 ^ 59
def prefixEnd_1335356 : Nat := 4983230072969 + 3 ^ 40 * 1335356 * 2
def baseEnd_1335356 : Nat := 457119648576921764805877

theorem tailTrace_1335356 : CollatzResearch.WordTrace tailWord_1335356 prefixEnd_1335356 457119648576921764805877 := by
  unfold tailWord_1335356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24352217275120373746536961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32469623033493831662049281 24352217275120373746536961)
  ·
    refine ⟨18264162956340280309902721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24352217275120373746536961 18264162956340280309902721)
    ·
      refine ⟨13698122217255210232427041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18264162956340280309902721 13698122217255210232427041)
      ·
        refine ⟨10273591662941407674320281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13698122217255210232427041 10273591662941407674320281)
        ·
          refine ⟨7705193747206055755740211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10273591662941407674320281 7705193747206055755740211)
          ·
            refine ⟨11557790620809083633610317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705193747206055755740211 11557790620809083633610317)
            ·
              refine ⟨4334171482803406362603869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11557790620809083633610317 4334171482803406362603869)
              ·
                refine ⟨1625314306051277385976451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4334171482803406362603869 1625314306051277385976451)
                ·
                  refine ⟨2437971459076916078964677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625314306051277385976451 2437971459076916078964677)
                  ·
                    refine ⟨457119648576921764805877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437971459076916078964677 457119648576921764805877)
                    ·
                      rfl

theorem cell22_1335356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_1335356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335356 prefixEnd_1335356 := by exact prefixLift 1335356
  have htrace : WordTrace (prefixWord ++ tailWord_1335356) baseStart_1335356 baseEnd_1335356 := by
    simpa [prefixWord, tailWord_1335356, baseEnd_1335356] using wordTrace_append hprefix tailTrace_1335356
  have hstable : (prefixWord ++ tailWord_1335356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335356).length < 2 ^ (prefixWord ++ tailWord_1335356).sum := by decide
  have hdescent : baseEnd_1335356 < baseStart_1335356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335384 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1335384 : Nat := 118140960795 + 1335384 * 2 ^ 59
def prefixEnd_1335384 : Nat := 4983230072969 + 3 ^ 40 * 1335384 * 2
def baseEnd_1335384 : Nat := 457129233549139025105791

theorem tailTrace_1335384 : CollatzResearch.WordTrace tailWord_1335384 prefixEnd_1335384 457129233549139025105791 := by
  unfold tailWord_1335384
  simp only [CollatzResearch.WordTrace]
  refine ⟨24352727897069654137546603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32470303862759538850062137 24352727897069654137546603)
  ·
    refine ⟨36529091845604481206319905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24352727897069654137546603 36529091845604481206319905)
    ·
      refine ⟨27396818884203360904739929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36529091845604481206319905 27396818884203360904739929)
      ·
        refine ⟨20547614163152520678554947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27396818884203360904739929 20547614163152520678554947)
        ·
          refine ⟨30821421244728781017832421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20547614163152520678554947 30821421244728781017832421)
          ·
            refine ⟨5779016483386646440843579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30821421244728781017832421 5779016483386646440843579)
            ·
              refine ⟨8668524725079969661265369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779016483386646440843579 8668524725079969661265369)
              ·
                refine ⟨6501393543809977245949027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8668524725079969661265369 6501393543809977245949027)
                ·
                  refine ⟨9752090315714965868923541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6501393543809977245949027 9752090315714965868923541)
                  ·
                    refine ⟨457129233549139025105791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9752090315714965868923541 457129233549139025105791)
                    ·
                      rfl

theorem cell22_1335384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1335384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335384 prefixEnd_1335384 := by exact prefixLift 1335384
  have htrace : WordTrace (prefixWord ++ tailWord_1335384) baseStart_1335384 baseEnd_1335384 := by
    simpa [prefixWord, tailWord_1335384, baseEnd_1335384] using wordTrace_append hprefix tailTrace_1335384
  have hstable : (prefixWord ++ tailWord_1335384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335384).length < 2 ^ (prefixWord ++ tailWord_1335384).sum := by decide
  have hdescent : baseEnd_1335384 < baseStart_1335384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335399 : List Nat := [1, 1, 5, 1, 1, 2, 3, 8]
def baseStart_1335399 : Nat := 118140960795 + 1335399 * 2 ^ 59
def prefixEnd_1335399 : Nat := 4983230072969 + 3 ^ 40 * 1335399 * 2
def baseEnd_1335399 : Nat := 50792707595075998442305

theorem tailTrace_1335399 : CollatzResearch.WordTrace tailWord_1335399 prefixEnd_1335399 50792707595075998442305 := by
  unfold tailWord_1335399
  simp only [CollatzResearch.WordTrace]
  refine ⟨48706002889084965836889251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32470668592723310557926167 48706002889084965836889251)
  ·
    refine ⟨73059004333627448755333877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48706002889084965836889251 73059004333627448755333877)
    ·
      refine ⟨6849281656277573320812551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73059004333627448755333877 6849281656277573320812551)
      ·
        refine ⟨10273922484416359981218827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6849281656277573320812551 10273922484416359981218827)
        ·
          refine ⟨15410883726624539971828241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10273922484416359981218827 15410883726624539971828241)
          ·
            refine ⟨11558162794968404978871181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15410883726624539971828241 11558162794968404978871181)
            ·
              refine ⟨4334311048113151867076693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11558162794968404978871181 4334311048113151867076693)
              ·
                refine ⟨50792707595075998442305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4334311048113151867076693 50792707595075998442305)
                ·
                  rfl

theorem cell22_1335399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 8].length) (baseStart_1335399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335399 prefixEnd_1335399 := by exact prefixLift 1335399
  have htrace : WordTrace (prefixWord ++ tailWord_1335399) baseStart_1335399 baseEnd_1335399 := by
    simpa [prefixWord, tailWord_1335399, baseEnd_1335399] using wordTrace_append hprefix tailTrace_1335399
  have hstable : (prefixWord ++ tailWord_1335399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335399).length < 2 ^ (prefixWord ++ tailWord_1335399).sum := by decide
  have hdescent : baseEnd_1335399 < baseStart_1335399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335459 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_1335459 : Nat := 118140960795 + 1335459 * 2 ^ 59
def prefixEnd_1335459 : Nat := 4983230072969 + 3 ^ 40 * 1335459 * 2
def baseEnd_1335459 : Nat := 457154907581863829480561

theorem tailTrace_1335459 : CollatzResearch.WordTrace tailWord_1335459 prefixEnd_1335459 457154907581863829480561 := by
  unfold tailWord_1335459
  simp only [CollatzResearch.WordTrace]
  refine ⟨48708191268867596084073431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32472127512578397389382287 48708191268867596084073431)
  ·
    refine ⟨73062286903301394126110147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48708191268867596084073431 73062286903301394126110147)
    ·
      refine ⟨109593430354952091189165221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73062286903301394126110147 109593430354952091189165221)
      ·
        refine ⟨20548768191553517097968479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109593430354952091189165221 20548768191553517097968479)
        ·
          refine ⟨30823152287330275646952719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20548768191553517097968479 30823152287330275646952719)
          ·
            refine ⟨46234728430995413470429079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30823152287330275646952719 46234728430995413470429079)
            ·
              refine ⟨69352092646493120205643619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46234728430995413470429079 69352092646493120205643619)
              ·
                refine ⟨104028138969739680308465429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69352092646493120205643619 104028138969739680308465429)
                ·
                  refine ⟨4876319014206547514459317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104028138969739680308465429 4876319014206547514459317)
                  ·
                    refine ⟨457154907581863829480561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4876319014206547514459317 457154907581863829480561)
                    ·
                      rfl

theorem cell22_1335459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_1335459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335459 prefixEnd_1335459 := by exact prefixLift 1335459
  have htrace : WordTrace (prefixWord ++ tailWord_1335459) baseStart_1335459 baseEnd_1335459 := by
    simpa [prefixWord, tailWord_1335459, baseEnd_1335459] using wordTrace_append hprefix tailTrace_1335459
  have hstable : (prefixWord ++ tailWord_1335459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335459).length < 2 ^ (prefixWord ++ tailWord_1335459).sum := by decide
  have hdescent : baseEnd_1335459 < baseStart_1335459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335506 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1335506 : Nat := 118140960795 + 1335506 * 2 ^ 59
def prefixEnd_1335506 : Nat := 4983230072969 + 3 ^ 40 * 1335506 * 2
def baseEnd_1335506 : Nat := 152390332214123791185139

theorem tailTrace_1335506 : CollatzResearch.WordTrace tailWord_1335506 prefixEnd_1335506 152390332214123791185139 := by
  unfold tailWord_1335506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12177476374924330777758593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32473270333131548740689581 12177476374924330777758593)
  ·
    refine ⟨9133107281193248083318945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12177476374924330777758593 9133107281193248083318945)
    ·
      refine ⟨6849830460894936062489209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9133107281193248083318945 6849830460894936062489209)
      ·
        refine ⟨5137372845671202046866907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6849830460894936062489209 5137372845671202046866907)
        ·
          refine ⟨7706059268506803070300361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137372845671202046866907 7706059268506803070300361)
          ·
            refine ⟨5779544451380102302725271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7706059268506803070300361 5779544451380102302725271)
            ·
              refine ⟨8669316677070153454087907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779544451380102302725271 8669316677070153454087907)
              ·
                refine ⟨13003975015605230181131861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8669316677070153454087907 13003975015605230181131861)
                ·
                  refine ⟨152390332214123791185139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13003975015605230181131861 152390332214123791185139)
                  ·
                    rfl

theorem cell22_1335506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1335506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335506 prefixEnd_1335506 := by exact prefixLift 1335506
  have htrace : WordTrace (prefixWord ++ tailWord_1335506) baseStart_1335506 baseEnd_1335506 := by
    simpa [prefixWord, tailWord_1335506, baseEnd_1335506] using wordTrace_append hprefix tailTrace_1335506
  have hstable : (prefixWord ++ tailWord_1335506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335506).length < 2 ^ (prefixWord ++ tailWord_1335506).sum := by decide
  have hdescent : baseEnd_1335506 < baseStart_1335506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335521 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1335521 : Nat := 118140960795 + 1335521 * 2 ^ 59
def prefixEnd_1335521 : Nat := 4983230072969 + 3 ^ 40 * 1335521 * 2
def baseEnd_1335521 : Nat := 457176131448916334430371

theorem tailTrace_1335521 : CollatzResearch.WordTrace tailWord_1335521 prefixEnd_1335521 457176131448916334430371 := by
  unfold tailWord_1335521
  simp only [CollatzResearch.WordTrace]
  refine ⟨48710452594642980672830417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32473635063095320448553611 48710452594642980672830417)
  ·
    refine ⟨36532839445982235504622813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48710452594642980672830417 36532839445982235504622813)
    ·
      refine ⟨13699814792243338314233555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36532839445982235504622813 13699814792243338314233555)
      ·
        refine ⟨20549722188365007471350333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13699814792243338314233555 20549722188365007471350333)
        ·
          refine ⟨7706145820636877801756375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20549722188365007471350333 7706145820636877801756375)
          ·
            refine ⟨11559218730955316702634563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7706145820636877801756375 11559218730955316702634563)
            ·
              refine ⟨17338828096432975053951845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11559218730955316702634563 17338828096432975053951845)
              ·
                refine ⟨3251030268081182822615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17338828096432975053951845 3251030268081182822615971)
                ·
                  refine ⟨4876545402121774233923957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251030268081182822615971 4876545402121774233923957)
                  ·
                    refine ⟨457176131448916334430371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4876545402121774233923957 457176131448916334430371)
                    ·
                      rfl

theorem cell22_1335521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1335521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335521 prefixEnd_1335521 := by exact prefixLift 1335521
  have htrace : WordTrace (prefixWord ++ tailWord_1335521) baseStart_1335521 baseEnd_1335521 := by
    simpa [prefixWord, tailWord_1335521, baseEnd_1335521] using wordTrace_append hprefix tailTrace_1335521
  have hstable : (prefixWord ++ tailWord_1335521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335521).length < 2 ^ (prefixWord ++ tailWord_1335521).sum := by decide
  have hdescent : baseEnd_1335521 < baseStart_1335521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335525 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_1335525 : Nat := 118140960795 + 1335525 * 2 ^ 59
def prefixEnd_1335525 : Nat := 4983230072969 + 3 ^ 40 * 1335525 * 2
def baseEnd_1335525 : Nat := 457177500730661657330359

theorem tailTrace_1335525 : CollatzResearch.WordTrace tailWord_1335525 prefixEnd_1335525 457177500730661657330359 := by
  unfold tailWord_1335525
  simp only [CollatzResearch.WordTrace]
  refine ⟨48710598486628489355976029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32473732324418992903984019 48710598486628489355976029)
  ·
    refine ⟨18266474432485683508491011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48710598486628489355976029 18266474432485683508491011)
    ·
      refine ⟨27399711648728525262736517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18266474432485683508491011 27399711648728525262736517)
      ·
        refine ⟨5137445934136598486763097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27399711648728525262736517 5137445934136598486763097)
        ·
          refine ⟨3853084450602448865072323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5137445934136598486763097 3853084450602448865072323)
          ·
            refine ⟨5779626675903673297608485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853084450602448865072323 5779626675903673297608485)
            ·
              refine ⟨1083680001731938743301591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5779626675903673297608485 1083680001731938743301591)
              ·
                refine ⟨1625520002597908114952387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083680001731938743301591 1625520002597908114952387)
                ·
                  refine ⟨2438280003896862172428581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625520002597908114952387 2438280003896862172428581)
                  ·
                    refine ⟨457177500730661657330359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438280003896862172428581 457177500730661657330359)
                    ·
                      rfl

theorem cell22_1335525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_1335525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335525 prefixEnd_1335525 := by exact prefixLift 1335525
  have htrace : WordTrace (prefixWord ++ tailWord_1335525) baseStart_1335525 baseEnd_1335525 := by
    simpa [prefixWord, tailWord_1335525, baseEnd_1335525] using wordTrace_append hprefix tailTrace_1335525
  have hstable : (prefixWord ++ tailWord_1335525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335525).length < 2 ^ (prefixWord ++ tailWord_1335525).sum := by decide
  have hdescent : baseEnd_1335525 < baseStart_1335525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335536 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_1335536 : Nat := 118140960795 + 1335536 * 2 ^ 59
def prefixEnd_1335536 : Nat := 4983230072969 + 3 ^ 40 * 1335536 * 2
def baseEnd_1335536 : Nat := 457181266255461295305325

theorem tailTrace_1335536 : CollatzResearch.WordTrace tailWord_1335536 prefixEnd_1335536 457181266255461295305325 := by
  unfold tailWord_1335536
  simp only [CollatzResearch.WordTrace]
  refine ⟨24355499844794319117313231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32473999793059092156417641 24355499844794319117313231)
  ·
    refine ⟨36533249767191478675969847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24355499844794319117313231 36533249767191478675969847)
    ·
      refine ⟨54799874650787218013954771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36533249767191478675969847 54799874650787218013954771)
      ·
        refine ⟨82199811976180827020932157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54799874650787218013954771 82199811976180827020932157)
        ·
          refine ⟨30824929491067810132849559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82199811976180827020932157 30824929491067810132849559)
          ·
            refine ⟨46237394236601715199274339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30824929491067810132849559 46237394236601715199274339)
            ·
              refine ⟨69356091354902572798911509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46237394236601715199274339 69356091354902572798911509)
              ·
                refine ⟨3251066782261058099948977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69356091354902572798911509 3251066782261058099948977)
                ·
                  refine ⟨2438300086695793574961733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3251066782261058099948977 2438300086695793574961733)
                  ·
                    refine ⟨457181266255461295305325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438300086695793574961733 457181266255461295305325)
                    ·
                      rfl

theorem cell22_1335536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_1335536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335536 prefixEnd_1335536 := by exact prefixLift 1335536
  have htrace : WordTrace (prefixWord ++ tailWord_1335536) baseStart_1335536 baseEnd_1335536 := by
    simpa [prefixWord, tailWord_1335536, baseEnd_1335536] using wordTrace_append hprefix tailTrace_1335536
  have hstable : (prefixWord ++ tailWord_1335536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335536).length < 2 ^ (prefixWord ++ tailWord_1335536).sum := by decide
  have hdescent : baseEnd_1335536 < baseStart_1335536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335555 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 2, 3]
def baseStart_1335555 : Nat := 118140960795 + 1335555 * 2 ^ 59
def prefixEnd_1335555 : Nat := 4983230072969 + 3 ^ 40 * 1335555 * 2
def baseEnd_1335555 : Nat := 457187770343751579080267

theorem tailTrace_1335555 : CollatzResearch.WordTrace tailWord_1335555 prefixEnd_1335555 457187770343751579080267 := by
  unfold tailWord_1335555
  simp only [CollatzResearch.WordTrace]
  refine ⟨48711692676519804479568119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32474461784346536319712079 48711692676519804479568119)
  ·
    refine ⟨73067539014779706719352179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48711692676519804479568119 73067539014779706719352179)
    ·
      refine ⟨109601308522169560079028269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73067539014779706719352179 109601308522169560079028269)
      ·
        refine ⟨41100490695813585029635601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109601308522169560079028269 41100490695813585029635601)
        ·
          refine ⟨30825368021860188772226701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41100490695813585029635601 30825368021860188772226701)
          ·
            refine ⟨11559513008197570789585013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30825368021860188772226701 11559513008197570789585013)
            ·
              refine ⟨1083704344518522261523595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11559513008197570789585013 1083704344518522261523595)
              ·
                refine ⟨1625556516777783392285393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083704344518522261523595 1625556516777783392285393)
                ·
                  refine ⟨1219167387583337544214045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625556516777783392285393 1219167387583337544214045)
                  ·
                    refine ⟨457187770343751579080267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219167387583337544214045 457187770343751579080267)
                    ·
                      rfl

theorem cell22_1335555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 3].length) (baseStart_1335555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335555 prefixEnd_1335555 := by exact prefixLift 1335555
  have htrace : WordTrace (prefixWord ++ tailWord_1335555) baseStart_1335555 baseEnd_1335555 := by
    simpa [prefixWord, tailWord_1335555, baseEnd_1335555] using wordTrace_append hprefix tailTrace_1335555
  have hstable : (prefixWord ++ tailWord_1335555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335555).length < 2 ^ (prefixWord ++ tailWord_1335555).sum := by decide
  have hdescent : baseEnd_1335555 < baseStart_1335555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335566 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1335566 : Nat := 118140960795 + 1335566 * 2 ^ 59
def prefixEnd_1335566 : Nat := 4983230072969 + 3 ^ 40 * 1335566 * 2
def baseEnd_1335566 : Nat := 457191535868551217055233

theorem tailTrace_1335566 : CollatzResearch.WordTrace tailWord_1335566 prefixEnd_1335566 457191535868551217055233 := by
  unfold tailWord_1335566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089011734934994169777319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32474729252986635572145701 6089011734934994169777319)
  ·
    refine ⟨9133517602402491254665979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089011734934994169777319 9133517602402491254665979)
    ·
      refine ⟨13700276403603736881998969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9133517602402491254665979 13700276403603736881998969)
      ·
        refine ⟨10275207302702802661499227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13700276403603736881998969 10275207302702802661499227)
        ·
          refine ⟨15412810954054203992248841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10275207302702802661499227 15412810954054203992248841)
          ·
            refine ⟨11559608215540652994186631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15412810954054203992248841 11559608215540652994186631)
            ·
              refine ⟨17339412323310979491279947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11559608215540652994186631 17339412323310979491279947)
              ·
                refine ⟨26009118484966469236919921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17339412323310979491279947 26009118484966469236919921)
                ·
                  refine ⟨19506838863724851927689941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26009118484966469236919921 19506838863724851927689941)
                  ·
                    refine ⟨457191535868551217055233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19506838863724851927689941 457191535868551217055233)
                    ·
                      rfl

theorem cell22_1335566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1335566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335566 prefixEnd_1335566 := by exact prefixLift 1335566
  have htrace : WordTrace (prefixWord ++ tailWord_1335566) baseStart_1335566 baseEnd_1335566 := by
    simpa [prefixWord, tailWord_1335566, baseEnd_1335566] using wordTrace_append hprefix tailTrace_1335566
  have hstable : (prefixWord ++ tailWord_1335566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335566).length < 2 ^ (prefixWord ++ tailWord_1335566).sum := by decide
  have hdescent : baseEnd_1335566 < baseStart_1335566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335591 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 4]
def baseStart_1335591 : Nat := 118140960795 + 1335591 * 2 ^ 59
def prefixEnd_1335591 : Nat := 4983230072969 + 3 ^ 40 * 1335591 * 2
def baseEnd_1335591 : Nat := 152400031293153161726719

theorem tailTrace_1335591 : CollatzResearch.WordTrace tailWord_1335591 prefixEnd_1335591 152400031293153161726719 := by
  unfold tailWord_1335591
  simp only [CollatzResearch.WordTrace]
  refine ⟨48713005704389382627878627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32475337136259588418585751 48713005704389382627878627)
  ·
    refine ⟨73069508556584073941817941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48713005704389382627878627 73069508556584073941817941)
    ·
      refine ⟨856283303397469616505679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 73069508556584073941817941 856283303397469616505679)
      ·
        refine ⟨1284424955096204424758519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856283303397469616505679 1284424955096204424758519)
        ·
          refine ⟨1926637432644306637137779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284424955096204424758519 1926637432644306637137779)
          ·
            refine ⟨2889956148966459955706669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926637432644306637137779 2889956148966459955706669)
            ·
              refine ⟨1083733555862422483390001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2889956148966459955706669 1083733555862422483390001)
              ·
                refine ⟨812800166896816862542501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083733555862422483390001 812800166896816862542501)
                ·
                  refine ⟨152400031293153161726719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 812800166896816862542501 152400031293153161726719)
                  ·
                    rfl

theorem cell22_1335591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 4].length) (baseStart_1335591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335591 prefixEnd_1335591 := by exact prefixLift 1335591
  have htrace : WordTrace (prefixWord ++ tailWord_1335591) baseStart_1335591 baseEnd_1335591 := by
    simpa [prefixWord, tailWord_1335591, baseEnd_1335591] using wordTrace_append hprefix tailTrace_1335591
  have hstable : (prefixWord ++ tailWord_1335591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335591).length < 2 ^ (prefixWord ++ tailWord_1335591).sum := by decide
  have hdescent : baseEnd_1335591 < baseStart_1335591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335596 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_1335596 : Nat := 118140960795 + 1335596 * 2 ^ 59
def prefixEnd_1335596 : Nat := 4983230072969 + 3 ^ 40 * 1335596 * 2
def baseEnd_1335596 : Nat := 152400601827213712935047

theorem tailTrace_1335596 : CollatzResearch.WordTrace tailWord_1335596 prefixEnd_1335596 152400601827213712935047 := by
  unfold tailWord_1335596
  simp only [CollatzResearch.WordTrace]
  refine ⟨24356594034685634240905321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32475458712914178987873761 24356594034685634240905321)
  ·
    refine ⟨18267445526014225680678991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24356594034685634240905321 18267445526014225680678991)
    ·
      refine ⟨27401168289021338521018487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18267445526014225680678991 27401168289021338521018487)
      ·
        refine ⟨41101752433532007781527731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27401168289021338521018487 41101752433532007781527731)
        ·
          refine ⟨61652628650298011672291597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41101752433532007781527731 61652628650298011672291597)
          ·
            refine ⟨23119735743861754377109349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61652628650298011672291597 23119735743861754377109349)
            ·
              refine ⟨4334950451974078945708003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23119735743861754377109349 4334950451974078945708003)
              ·
                refine ⟨6502425677961118418562005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334950451974078945708003 6502425677961118418562005)
                ·
                  refine ⟨152400601827213712935047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6502425677961118418562005 152400601827213712935047)
                  ·
                    rfl

theorem cell22_1335596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_1335596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335596 prefixEnd_1335596 := by exact prefixLift 1335596
  have htrace : WordTrace (prefixWord ++ tailWord_1335596) baseStart_1335596 baseEnd_1335596 := by
    simpa [prefixWord, tailWord_1335596, baseEnd_1335596] using wordTrace_append hprefix tailTrace_1335596
  have hstable : (prefixWord ++ tailWord_1335596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335596).length < 2 ^ (prefixWord ++ tailWord_1335596).sum := by decide
  have hdescent : baseEnd_1335596 < baseStart_1335596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335673 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_1335673 : Nat := 118140960795 + 1335673 * 2 ^ 59
def prefixEnd_1335673 : Nat := 4983230072969 + 3 ^ 40 * 1335673 * 2
def baseEnd_1335673 : Nat := 457228164155238604629905

theorem tailTrace_1335673 : CollatzResearch.WordTrace tailWord_1335673 prefixEnd_1335673 457228164155238604629905 := by
  unfold tailWord_1335673
  simp only [CollatzResearch.WordTrace]
  refine ⟨48715996490092310632363673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32477330993394873754909115 48715996490092310632363673)
  ·
    refine ⟨36536997367569232974272755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48715996490092310632363673 36536997367569232974272755)
    ·
      refine ⟨54805496051353849461409133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36536997367569232974272755 54805496051353849461409133)
      ·
        refine ⟨20552061019257693548028425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54805496051353849461409133 20552061019257693548028425)
        ·
          refine ⟨15414045764443270161021319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20552061019257693548028425 15414045764443270161021319)
          ·
            refine ⟨23121068646664905241531979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15414045764443270161021319 23121068646664905241531979)
            ·
              refine ⟨34681602969997357862297969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23121068646664905241531979 34681602969997357862297969)
              ·
                refine ⟨26011202227498018396723477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34681602969997357862297969 26011202227498018396723477)
                ·
                  refine ⟨1219275104413969612346413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26011202227498018396723477 1219275104413969612346413)
                  ·
                    refine ⟨457228164155238604629905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219275104413969612346413 457228164155238604629905)
                    ·
                      rfl

theorem cell22_1335673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_1335673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335673 prefixEnd_1335673 := by exact prefixLift 1335673
  have htrace : WordTrace (prefixWord ++ tailWord_1335673) baseStart_1335673 baseEnd_1335673 := by
    simpa [prefixWord, tailWord_1335673, baseEnd_1335673] using wordTrace_append hprefix tailTrace_1335673
  have hstable : (prefixWord ++ tailWord_1335673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335673).length < 2 ^ (prefixWord ++ tailWord_1335673).sum := by decide
  have hdescent : baseEnd_1335673 < baseStart_1335673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335688 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1335688 : Nat := 118140960795 + 1335688 * 2 ^ 59
def prefixEnd_1335688 : Nat := 4983230072969 + 3 ^ 40 * 1335688 * 2
def baseEnd_1335688 : Nat := 457233298961783565504859

theorem tailTrace_1335688 : CollatzResearch.WordTrace tailWord_1335688 prefixEnd_1335688 457233298961783565504859 := by
  unfold tailWord_1335688
  simp only [CollatzResearch.WordTrace]
  refine ⟨24358271792518984097079859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32477695723358645462773145 24358271792518984097079859)
  ·
    refine ⟨36537407688778476145619789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24358271792518984097079859 36537407688778476145619789)
    ·
      refine ⟨13701527883291928554607421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36537407688778476145619789 13701527883291928554607421)
      ·
        refine ⟨5138072956234473207977783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13701527883291928554607421 5138072956234473207977783)
        ·
          refine ⟨7707109434351709811966675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5138072956234473207977783 7707109434351709811966675)
          ·
            refine ⟨11560664151527564717950013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707109434351709811966675 11560664151527564717950013)
            ·
              refine ⟨4335249056822836769231255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11560664151527564717950013 4335249056822836769231255)
              ·
                refine ⟨6502873585234255153846883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335249056822836769231255 6502873585234255153846883)
                ·
                  refine ⟨9754310377851382730770325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6502873585234255153846883 9754310377851382730770325)
                  ·
                    refine ⟨457233298961783565504859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9754310377851382730770325 457233298961783565504859)
                    ·
                      rfl

theorem cell22_1335688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1335688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335688 prefixEnd_1335688 := by exact prefixLift 1335688
  have htrace : WordTrace (prefixWord ++ tailWord_1335688) baseStart_1335688 baseEnd_1335688 := by
    simpa [prefixWord, tailWord_1335688, baseEnd_1335688] using wordTrace_append hprefix tailTrace_1335688
  have hstable : (prefixWord ++ tailWord_1335688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335688).length < 2 ^ (prefixWord ++ tailWord_1335688).sum := by decide
  have hdescent : baseEnd_1335688 < baseStart_1335688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335694 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_1335694 : Nat := 118140960795 + 1335694 * 2 ^ 59
def prefixEnd_1335694 : Nat := 4983230072969 + 3 ^ 40 * 1335694 * 2
def baseEnd_1335694 : Nat := 457235352884401549854841

theorem tailTrace_1335694 : CollatzResearch.WordTrace tailWord_1335694 prefixEnd_1335694 457235352884401549854841 := by
  unfold tailWord_1335694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089595302877028902359767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32477841615344154145918757 6089595302877028902359767)
  ·
    refine ⟨9134392954315543353539651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089595302877028902359767 9134392954315543353539651)
    ·
      refine ⟨13701589431473315030309477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134392954315543353539651 13701589431473315030309477)
      ·
        refine ⟨2569048018401246568183027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13701589431473315030309477 2569048018401246568183027)
        ·
          refine ⟨3853572027601869852274541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569048018401246568183027 3853572027601869852274541)
          ·
            refine ⟨1445089510350701194602953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3853572027601869852274541 1445089510350701194602953)
            ·
              refine ⟨1083817132763025895952215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445089510350701194602953 1083817132763025895952215)
              ·
                refine ⟨1625725699144538843928323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083817132763025895952215 1625725699144538843928323)
                ·
                  refine ⟨2438588548716808265892485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625725699144538843928323 2438588548716808265892485)
                  ·
                    refine ⟨457235352884401549854841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438588548716808265892485 457235352884401549854841)
                    ·
                      rfl

theorem cell22_1335694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_1335694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335694 prefixEnd_1335694 := by exact prefixLift 1335694
  have htrace : WordTrace (prefixWord ++ tailWord_1335694) baseStart_1335694 baseEnd_1335694 := by
    simpa [prefixWord, tailWord_1335694, baseEnd_1335694] using wordTrace_append hprefix tailTrace_1335694
  have hstable : (prefixWord ++ tailWord_1335694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335694).length < 2 ^ (prefixWord ++ tailWord_1335694).sum := by decide
  have hdescent : baseEnd_1335694 < baseStart_1335694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335735 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 3, 3]
def baseStart_1335735 : Nat := 118140960795 + 1335735 * 2 ^ 59
def prefixEnd_1335735 : Nat := 4983230072969 + 3 ^ 40 * 1335735 * 2
def baseEnd_1335735 : Nat := 457249388022291109579715

theorem tailTrace_1335735 : CollatzResearch.WordTrace tailWord_1335735 prefixEnd_1335735 457249388022291109579715 := by
  unfold tailWord_1335735
  simp only [CollatzResearch.WordTrace]
  refine ⟨48718257815867695221120659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32478838543911796814080439 48718257815867695221120659)
  ·
    refine ⟨73077386723801542831680989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48718257815867695221120659 73077386723801542831680989)
    ·
      refine ⟨27404020021425578561880371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73077386723801542831680989 27404020021425578561880371)
      ·
        refine ⟨41106030032138367842820557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27404020021425578561880371 41106030032138367842820557)
        ·
          refine ⟨15414761262051887941057709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41106030032138367842820557 15414761262051887941057709)
          ·
            refine ⟨5780535473269457977896641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15414761262051887941057709 5780535473269457977896641)
            ·
              refine ⟨4335401604952093483422481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5780535473269457977896641 4335401604952093483422481)
              ·
                refine ⟨3251551203714070112566861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4335401604952093483422481 3251551203714070112566861)
                ·
                  refine ⟨1219331701392776292212573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3251551203714070112566861 1219331701392776292212573)
                  ·
                    refine ⟨457249388022291109579715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219331701392776292212573 457249388022291109579715)
                    ·
                      rfl

theorem cell22_1335735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_1335735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335735 prefixEnd_1335735 := by exact prefixLift 1335735
  have htrace : WordTrace (prefixWord ++ tailWord_1335735) baseStart_1335735 baseEnd_1335735 := by
    simpa [prefixWord, tailWord_1335735, baseEnd_1335735] using wordTrace_append hprefix tailTrace_1335735
  have hstable : (prefixWord ++ tailWord_1335735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335735).length < 2 ^ (prefixWord ++ tailWord_1335735).sum := by decide
  have hdescent : baseEnd_1335735 < baseStart_1335735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335769 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 1, 3]
def baseStart_1335769 : Nat := 118140960795 + 1335769 * 2 ^ 59
def prefixEnd_1335769 : Nat := 4983230072969 + 3 ^ 40 * 1335769 * 2
def baseEnd_1335769 : Nat := 457261026917126354229611

theorem tailTrace_1335769 : CollatzResearch.WordTrace tailWord_1335769 prefixEnd_1335769 457261026917126354229611 := by
  unfold tailWord_1335769
  simp only [CollatzResearch.WordTrace]
  refine ⟨48719497897744519027858361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32479665265163012685238907 48719497897744519027858361)
  ·
    refine ⟨36539623423308389270893771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48719497897744519027858361 36539623423308389270893771)
    ·
      refine ⟨54809435134962583906340657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36539623423308389270893771 54809435134962583906340657)
      ·
        refine ⟨41107076351221937929755493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54809435134962583906340657 41107076351221937929755493)
        ·
          refine ⟨7707576815854113361829155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41107076351221937929755493 7707576815854113361829155)
          ·
            refine ⟨11561365223781170042743733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707576815854113361829155 11561365223781170042743733)
            ·
              refine ⟨1083877989729484691507225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11561365223781170042743733 1083877989729484691507225)
              ·
                refine ⟨812908492297113518630419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083877989729484691507225 812908492297113518630419)
                ·
                  refine ⟨1219362738445670277945629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812908492297113518630419 1219362738445670277945629)
                  ·
                    refine ⟨457261026917126354229611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219362738445670277945629 457261026917126354229611)
                    ·
                      rfl

theorem cell22_1335769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_1335769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335769 prefixEnd_1335769 := by exact prefixLift 1335769
  have htrace : WordTrace (prefixWord ++ tailWord_1335769) baseStart_1335769 baseEnd_1335769 := by
    simpa [prefixWord, tailWord_1335769, baseEnd_1335769] using wordTrace_append hprefix tailTrace_1335769
  have hstable : (prefixWord ++ tailWord_1335769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335769).length < 2 ^ (prefixWord ++ tailWord_1335769).sum := by decide
  have hdescent : baseEnd_1335769 < baseStart_1335769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335793 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 8]
def baseStart_1335793 : Nat := 118140960795 + 1335793 * 2 ^ 59
def prefixEnd_1335793 : Nat := 4983230072969 + 3 ^ 40 * 1335793 * 2
def baseEnd_1335793 : Nat := 152423080869199430543179

theorem tailTrace_1335793 : CollatzResearch.WordTrace tailWord_1335793 prefixEnd_1335793 152423080869199430543179 := by
  unfold tailWord_1335793
  simp only [CollatzResearch.WordTrace]
  refine ⟨48720373249657571126732033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32480248833105047417821355 48720373249657571126732033)
  ·
    refine ⟨36540279937243178345049025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48720373249657571126732033 36540279937243178345049025)
    ·
      refine ⟨27405209952932383758786769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36540279937243178345049025 27405209952932383758786769)
      ·
        refine ⟨20553907464699287819090077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27405209952932383758786769 20553907464699287819090077)
        ·
          refine ⟨7707715299262232932158779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20553907464699287819090077 7707715299262232932158779)
          ·
            refine ⟨11561572948893349398238169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707715299262232932158779 11561572948893349398238169)
            ·
              refine ⟨8671179711670012048678627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11561572948893349398238169 8671179711670012048678627)
              ·
                refine ⟨13006769567505018073017941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671179711670012048678627 13006769567505018073017941)
                ·
                  refine ⟨152423080869199430543179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13006769567505018073017941 152423080869199430543179)
                  ·
                    rfl

theorem cell22_1335793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_1335793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335793 prefixEnd_1335793 := by exact prefixLift 1335793
  have htrace : WordTrace (prefixWord ++ tailWord_1335793) baseStart_1335793 baseEnd_1335793 := by
    simpa [prefixWord, tailWord_1335793, baseEnd_1335793] using wordTrace_append hprefix tailTrace_1335793
  have hstable : (prefixWord ++ tailWord_1335793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335793).length < 2 ^ (prefixWord ++ tailWord_1335793).sum := by decide
  have hdescent : baseEnd_1335793 < baseStart_1335793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335906 : List Nat := [3, 3, 2, 3, 1, 2, 2, 6]
def baseStart_1335906 : Nat := 118140960795 + 1335906 * 2 ^ 59
def prefixEnd_1335906 : Nat := 4983230072969 + 3 ^ 40 * 1335906 * 2
def baseEnd_1335906 : Nat := 50811991646322629283799

theorem tailTrace_1335906 : CollatzResearch.WordTrace tailWord_1335906 prefixEnd_1335906 50811991646322629283799 := by
  unfold tailWord_1335906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12181123674562047856398893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32482996465498794283730381 12181123674562047856398893)
  ·
    refine ⟨4567921377960767946149585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12181123674562047856398893 4567921377960767946149585)
    ·
      refine ⟨3425941033470575959612189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4567921377960767946149585 3425941033470575959612189)
      ·
        refine ⟨1284727887551465984854571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3425941033470575959612189 1284727887551465984854571)
        ·
          refine ⟨1927091831327198977281857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284727887551465984854571 1927091831327198977281857)
          ·
            refine ⟨1445318873495399232961393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1927091831327198977281857 1445318873495399232961393)
            ·
              refine ⟨1083989155121549424721045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445318873495399232961393 1083989155121549424721045)
              ·
                refine ⟨50811991646322629283799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1083989155121549424721045 50811991646322629283799)
                ·
                  rfl

theorem cell22_1335906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_1335906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335906 prefixEnd_1335906 := by exact prefixLift 1335906
  have htrace : WordTrace (prefixWord ++ tailWord_1335906) baseStart_1335906 baseEnd_1335906 := by
    simpa [prefixWord, tailWord_1335906, baseEnd_1335906] using wordTrace_append hprefix tailTrace_1335906
  have hstable : (prefixWord ++ tailWord_1335906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335906).length < 2 ^ (prefixWord ++ tailWord_1335906).sum := by decide
  have hdescent : baseEnd_1335906 < baseStart_1335906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335964 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1335964 : Nat := 118140960795 + 1335964 * 2 ^ 59
def prefixEnd_1335964 : Nat := 4983230072969 + 3 ^ 40 * 1335964 * 2
def baseEnd_1335964 : Nat := 457327779402210845604013

theorem tailTrace_1335964 : CollatzResearch.WordTrace tailWord_1335964 prefixEnd_1335964 457327779402210845604013 := by
  unfold tailWord_1335964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24363305066019033665603473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32484406754692044887471297 24363305066019033665603473)
  ·
    refine ⟨18272478799514275249202605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24363305066019033665603473 18272478799514275249202605)
    ·
      refine ⟨6852179549817853218450977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18272478799514275249202605 6852179549817853218450977)
      ·
        refine ⟨5139134662363389913838233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6852179549817853218450977 5139134662363389913838233)
        ·
          refine ⟨3854350996772542435378675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5139134662363389913838233 3854350996772542435378675)
          ·
            refine ⟨5781526495158813653068013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854350996772542435378675 5781526495158813653068013)
            ·
              refine ⟨2168072435684555119900505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5781526495158813653068013 2168072435684555119900505)
              ·
                refine ⟨1626054326763416339925379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168072435684555119900505 1626054326763416339925379)
                ·
                  refine ⟨2439081490145124509888069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626054326763416339925379 2439081490145124509888069)
                  ·
                    refine ⟨457327779402210845604013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439081490145124509888069 457327779402210845604013)
                    ·
                      rfl

theorem cell22_1335964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1335964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335964 prefixEnd_1335964 := by exact prefixLift 1335964
  have htrace : WordTrace (prefixWord ++ tailWord_1335964) baseStart_1335964 baseEnd_1335964 := by
    simpa [prefixWord, tailWord_1335964, baseEnd_1335964] using wordTrace_append hprefix tailTrace_1335964
  have hstable : (prefixWord ++ tailWord_1335964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335964).length < 2 ^ (prefixWord ++ tailWord_1335964).sum := by decide
  have hdescent : baseEnd_1335964 < baseStart_1335964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335981 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1335981 : Nat := 118140960795 + 1335981 * 2 ^ 59
def prefixEnd_1335981 : Nat := 4983230072969 + 3 ^ 40 * 1335981 * 2
def baseEnd_1335981 : Nat := 457333598849628467928961

theorem tailTrace_1335981 : CollatzResearch.WordTrace tailWord_1335981 prefixEnd_1335981 457333598849628467928961 := by
  unfold tailWord_1335981
  simp only [CollatzResearch.WordTrace]
  refine ⟨48727230172976479234575797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32484820115317652823050531 48727230172976479234575797)
  ·
    refine ⟨4568177828716544928241481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48727230172976479234575797 4568177828716544928241481)
    ·
      refine ⟨3426133371537408696181111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4568177828716544928241481 3426133371537408696181111)
      ·
        refine ⟨5139200057306113044271667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426133371537408696181111 5139200057306113044271667)
        ·
          refine ⟨7708800085959169566407501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139200057306113044271667 7708800085959169566407501)
          ·
            refine ⟨2890800032234688587402813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7708800085959169566407501 2890800032234688587402813)
            ·
              refine ⟨1084050012088008220276055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2890800032234688587402813 1084050012088008220276055)
              ·
                refine ⟨1626075018132012330414083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084050012088008220276055 1626075018132012330414083)
                ·
                  refine ⟨2439112527198018495621125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626075018132012330414083 2439112527198018495621125)
                  ·
                    refine ⟨457333598849628467928961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439112527198018495621125 457333598849628467928961)
                    ·
                      rfl

theorem cell22_1335981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1335981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335981 prefixEnd_1335981 := by exact prefixLift 1335981
  have htrace : WordTrace (prefixWord ++ tailWord_1335981) baseStart_1335981 baseEnd_1335981 := by
    simpa [prefixWord, tailWord_1335981, baseEnd_1335981] using wordTrace_append hprefix tailTrace_1335981
  have hstable : (prefixWord ++ tailWord_1335981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335981).length < 2 ^ (prefixWord ++ tailWord_1335981).sum := by decide
  have hdescent : baseEnd_1335981 < baseStart_1335981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335994 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_1335994 : Nat := 118140960795 + 1335994 * 2 ^ 59
def prefixEnd_1335994 : Nat := 4983230072969 + 3 ^ 40 * 1335994 * 2
def baseEnd_1335994 : Nat := 457338049015300767353921

theorem tailTrace_1335994 : CollatzResearch.WordTrace tailWord_1335994 prefixEnd_1335994 457338049015300767353921 := by
  unfold tailWord_1335994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12181926080482345613699759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32485136214619588303199357 12181926080482345613699759)
  ·
    refine ⟨18272889120723518420549639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12181926080482345613699759 18272889120723518420549639)
    ·
      refine ⟨27409333681085277630824459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18272889120723518420549639 27409333681085277630824459)
      ·
        refine ⟨41114000521627916446236689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27409333681085277630824459 41114000521627916446236689)
        ·
          refine ⟨30835500391220937334677517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41114000521627916446236689 30835500391220937334677517)
          ·
            refine ⟨11563312646707851500504069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30835500391220937334677517 11563312646707851500504069)
            ·
              refine ⟨2168121121257722156344513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11563312646707851500504069 2168121121257722156344513)
              ·
                refine ⟨1626090840943291617258385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168121121257722156344513 1626090840943291617258385)
                ·
                  refine ⟨1219568130707468712943789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1626090840943291617258385 1219568130707468712943789)
                  ·
                    refine ⟨457338049015300767353921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219568130707468712943789 457338049015300767353921)
                    ·
                      rfl

theorem cell22_1335994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_1335994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1335994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1335994 prefixEnd_1335994 := by exact prefixLift 1335994
  have htrace : WordTrace (prefixWord ++ tailWord_1335994) baseStart_1335994 baseEnd_1335994 := by
    simpa [prefixWord, tailWord_1335994, baseEnd_1335994] using wordTrace_append hprefix tailTrace_1335994
  have hstable : (prefixWord ++ tailWord_1335994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335994).length < 2 ^ (prefixWord ++ tailWord_1335994).sum := by decide
  have hdescent : baseEnd_1335994 < baseStart_1335994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336172 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1336172 : Nat := 118140960795 + 1336172 * 2 ^ 59
def prefixEnd_1336172 : Nat := 4983230072969 + 3 ^ 40 * 1336172 * 2
def baseEnd_1336172 : Nat := 457398982052967636403375

theorem tailTrace_1336172 : CollatzResearch.WordTrace tailWord_1336172 prefixEnd_1336172 457398982052967636403375 := by
  unfold tailWord_1336172
  simp only [CollatzResearch.WordTrace]
  refine ⟨24367098257642259427389385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32489464343523012569852513 24367098257642259427389385)
  ·
    refine ⟨18275323693231694570542039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24367098257642259427389385 18275323693231694570542039)
    ·
      refine ⟨27412985539847541855813059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18275323693231694570542039 27412985539847541855813059)
      ·
        refine ⟨41119478309771312783719589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27412985539847541855813059 41119478309771312783719589)
        ·
          refine ⟨7709902183082121146947423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41119478309771312783719589 7709902183082121146947423)
          ·
            refine ⟨11564853274623181720421135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7709902183082121146947423 11564853274623181720421135)
            ·
              refine ⟨17347279911934772580631703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11564853274623181720421135 17347279911934772580631703)
              ·
                refine ⟨26020919867902158870947555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17347279911934772580631703 26020919867902158870947555)
                ·
                  refine ⟨39031379801853238306421333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26020919867902158870947555 39031379801853238306421333)
                  ·
                    refine ⟨457398982052967636403375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39031379801853238306421333 457398982052967636403375)
                    ·
                      rfl

theorem cell22_1336172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1336172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336172 prefixEnd_1336172 := by exact prefixLift 1336172
  have htrace : WordTrace (prefixWord ++ tailWord_1336172) baseStart_1336172 baseEnd_1336172 := by
    simpa [prefixWord, tailWord_1336172, baseEnd_1336172] using wordTrace_append hprefix tailTrace_1336172
  have hstable : (prefixWord ++ tailWord_1336172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336172).length < 2 ^ (prefixWord ++ tailWord_1336172).sum := by decide
  have hdescent : baseEnd_1336172 < baseStart_1336172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336249 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 6]
def baseStart_1336249 : Nat := 118140960795 + 1336249 * 2 ^ 59
def prefixEnd_1336249 : Nat := 4983230072969 + 3 ^ 40 * 1336249 * 2
def baseEnd_1336249 : Nat := 152475113575521700742713

theorem tailTrace_1336249 : CollatzResearch.WordTrace tailWord_1336249 prefixEnd_1336249 152475113575521700742713 := by
  unfold tailWord_1336249
  simp only [CollatzResearch.WordTrace]
  refine ⟨48737004936005561005331801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32491336624003707336887867 48737004936005561005331801)
  ·
    refine ⟨36552753702004170753998851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48737004936005561005331801 36552753702004170753998851)
    ·
      refine ⟨54829130553006256130998277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36552753702004170753998851 54829130553006256130998277)
      ·
        refine ⟨10280461978688673024562177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54829130553006256130998277 10280461978688673024562177)
        ·
          refine ⟨7710346484016504768421633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10280461978688673024562177 7710346484016504768421633)
          ·
            refine ⟨5782759863012378576316225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7710346484016504768421633 5782759863012378576316225)
            ·
              refine ⟨4337069897259283932237169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5782759863012378576316225 4337069897259283932237169)
              ·
                refine ⟨3252802422944462949177877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337069897259283932237169 3252802422944462949177877)
                ·
                  refine ⟨152475113575521700742713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3252802422944462949177877 152475113575521700742713)
                  ·
                    rfl

theorem cell22_1336249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_1336249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336249 prefixEnd_1336249 := by exact prefixLift 1336249
  have htrace : WordTrace (prefixWord ++ tailWord_1336249) baseStart_1336249 baseEnd_1336249 := by
    simpa [prefixWord, tailWord_1336249, baseEnd_1336249] using wordTrace_append hprefix tailTrace_1336249
  have hstable : (prefixWord ++ tailWord_1336249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336249).length < 2 ^ (prefixWord ++ tailWord_1336249).sum := by decide
  have hdescent : baseEnd_1336249 < baseStart_1336249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336281 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_1336281 : Nat := 118140960795 + 1336281 * 2 ^ 59
def prefixEnd_1336281 : Nat := 4983230072969 + 3 ^ 40 * 1336281 * 2
def baseEnd_1336281 : Nat := 457436294980527685428041

theorem tailTrace_1336281 : CollatzResearch.WordTrace tailWord_1336281 prefixEnd_1336281 457436294980527685428041 := by
  unfold tailWord_1336281
  simp only [CollatzResearch.WordTrace]
  refine ⟨48738172071889630470496697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32492114714593086980331131 48738172071889630470496697)
  ·
    refine ⟨36553629053917222852872523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48738172071889630470496697 36553629053917222852872523)
    ·
      refine ⟨54830443580875834279308785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36553629053917222852872523 54830443580875834279308785)
      ·
        refine ⟨41122832685656875709481589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54830443580875834279308785 41122832685656875709481589)
        ·
          refine ⟨3855265564280332097763899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41122832685656875709481589 3855265564280332097763899)
          ·
            refine ⟨5782898346420498146645849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855265564280332097763899 5782898346420498146645849)
            ·
              refine ⟨4337173759815373609984387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5782898346420498146645849 4337173759815373609984387)
              ·
                refine ⟨6505760639723060414976581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337173759815373609984387 6505760639723060414976581)
                ·
                  refine ⟨1219830119948073827808109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6505760639723060414976581 1219830119948073827808109)
                  ·
                    refine ⟨457436294980527685428041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219830119948073827808109 457436294980527685428041)
                    ·
                      rfl

theorem cell22_1336281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_1336281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336281 prefixEnd_1336281 := by exact prefixLift 1336281
  have htrace : WordTrace (prefixWord ++ tailWord_1336281) baseStart_1336281 baseEnd_1336281 := by
    simpa [prefixWord, tailWord_1336281, baseEnd_1336281] using wordTrace_append hprefix tailTrace_1336281
  have hstable : (prefixWord ++ tailWord_1336281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336281).length < 2 ^ (prefixWord ++ tailWord_1336281).sum := by decide
  have hdescent : baseEnd_1336281 < baseStart_1336281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336298 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1336298 : Nat := 118140960795 + 1336298 * 2 ^ 59
def prefixEnd_1336298 : Nat := 4983230072969 + 3 ^ 40 * 1336298 * 2
def baseEnd_1336298 : Nat := 457442114427945307752989

theorem tailTrace_1336298 : CollatzResearch.WordTrace tailWord_1336298 prefixEnd_1336298 457442114427945307752989 := by
  unfold tailWord_1336298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12184698028207010593466387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32492528075218694915910365 12184698028207010593466387)
  ·
    refine ⟨18277047042310515890199581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12184698028207010593466387 18277047042310515890199581)
    ·
      refine ⟨6853892640866443458824843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18277047042310515890199581 6853892640866443458824843)
      ·
        refine ⟨10280838961299665188237265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6853892640866443458824843 10280838961299665188237265)
        ·
          refine ⟨7710629220974748891177949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10280838961299665188237265 7710629220974748891177949)
          ·
            refine ⟨2891485957865530834191731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7710629220974748891177949 2891485957865530834191731)
            ·
              refine ⟨4337228936798296251287597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891485957865530834191731 4337228936798296251287597)
              ·
                refine ⟨1626460851299361094232849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4337228936798296251287597 1626460851299361094232849)
                ·
                  refine ⟨1219845638474520820674637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1626460851299361094232849 1219845638474520820674637)
                  ·
                    refine ⟨457442114427945307752989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219845638474520820674637 457442114427945307752989)
                    ·
                      rfl

theorem cell22_1336298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1336298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336298 prefixEnd_1336298 := by exact prefixLift 1336298
  have htrace : WordTrace (prefixWord ++ tailWord_1336298) baseStart_1336298 baseEnd_1336298 := by
    simpa [prefixWord, tailWord_1336298, baseEnd_1336298] using wordTrace_append hprefix tailTrace_1336298
  have hstable : (prefixWord ++ tailWord_1336298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336298).length < 2 ^ (prefixWord ++ tailWord_1336298).sum := by decide
  have hdescent : baseEnd_1336298 < baseStart_1336298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336384 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_1336384 : Nat := 118140960795 + 1336384 * 2 ^ 59
def prefixEnd_1336384 : Nat := 4983230072969 + 3 ^ 40 * 1336384 * 2
def baseEnd_1336384 : Nat := 152490517995156583367575

theorem tailTrace_1336384 : CollatzResearch.WordTrace tailWord_1336384 prefixEnd_1336384 152490517995156583367575 := by
  unfold tailWord_1336384
  simp only [CollatzResearch.WordTrace]
  refine ⟨24370964395258239530748103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32494619193677652707664137 24370964395258239530748103)
  ·
    refine ⟨36556446592887359296122155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24370964395258239530748103 36556446592887359296122155)
    ·
      refine ⟨54834669889331038944183233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36556446592887359296122155 54834669889331038944183233)
      ·
        refine ⟨41126002416998279208137425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54834669889331038944183233 41126002416998279208137425)
        ·
          refine ⟨30844501812748709406103069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41126002416998279208137425 30844501812748709406103069)
          ·
            refine ⟨11566688179780766027288651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30844501812748709406103069 11566688179780766027288651)
            ·
              refine ⟨17350032269671149040932977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11566688179780766027288651 17350032269671149040932977)
              ·
                refine ⟨13012524202253361780699733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17350032269671149040932977 13012524202253361780699733)
                ·
                  refine ⟨152490517995156583367575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13012524202253361780699733 152490517995156583367575)
                  ·
                    rfl

theorem cell22_1336384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_1336384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336384 prefixEnd_1336384 := by exact prefixLift 1336384
  have htrace : WordTrace (prefixWord ++ tailWord_1336384) baseStart_1336384 baseEnd_1336384 := by
    simpa [prefixWord, tailWord_1336384, baseEnd_1336384] using wordTrace_append hprefix tailTrace_1336384
  have hstable : (prefixWord ++ tailWord_1336384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336384).length < 2 ^ (prefixWord ++ tailWord_1336384).sum := by decide
  have hdescent : baseEnd_1336384 < baseStart_1336384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336390 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1336390 : Nat := 118140960795 + 1336390 * 2 ^ 59
def prefixEnd_1336390 : Nat := 4983230072969 + 3 ^ 40 * 1336390 * 2
def baseEnd_1336390 : Nat := 152491202636029244817569

theorem tailTrace_1336390 : CollatzResearch.WordTrace tailWord_1336390 prefixEnd_1336390 152491202636029244817569 := by
  unfold tailWord_1336390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523192113390460690194207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32494765085663161390809749 1523192113390460690194207)
  ·
    refine ⟨2284788170085691035291311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1523192113390460690194207 2284788170085691035291311)
    ·
      refine ⟨3427182255128536552936967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284788170085691035291311 3427182255128536552936967)
      ·
        refine ⟨5140773382692804829405451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427182255128536552936967 5140773382692804829405451)
        ·
          refine ⟨7711160074039207244108177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140773382692804829405451 7711160074039207244108177)
          ·
            refine ⟨5783370055529405433081133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711160074039207244108177 5783370055529405433081133)
            ·
              refine ⟨2168763770823527037405425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5783370055529405433081133 2168763770823527037405425)
              ·
                refine ⟨1626572828117645278054069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168763770823527037405425 1626572828117645278054069)
                ·
                  refine ⟨152491202636029244817569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1626572828117645278054069 152491202636029244817569)
                  ·
                    rfl

theorem cell22_1336390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1336390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336390 prefixEnd_1336390 := by exact prefixLift 1336390
  have htrace : WordTrace (prefixWord ++ tailWord_1336390) baseStart_1336390 baseEnd_1336390 := by
    simpa [prefixWord, tailWord_1336390, baseEnd_1336390] using wordTrace_append hprefix tailTrace_1336390
  have hstable : (prefixWord ++ tailWord_1336390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336390).length < 2 ^ (prefixWord ++ tailWord_1336390).sum := by decide
  have hdescent : baseEnd_1336390 < baseStart_1336390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336418 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1336418 : Nat := 118140960795 + 1336418 * 2 ^ 59
def prefixEnd_1336418 : Nat := 4983230072969 + 3 ^ 40 * 1336418 * 2
def baseEnd_1336418 : Nat := 152494397626768331584207

theorem tailTrace_1336418 : CollatzResearch.WordTrace tailWord_1336418 prefixEnd_1336418 152494397626768331584207 := by
  unfold tailWord_1336418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12185792218098325717058477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32495445914928868578822605 12185792218098325717058477)
  ·
    refine ⟨4569672081786872143896929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12185792218098325717058477 4569672081786872143896929)
    ·
      refine ⟨3427254061340154107922697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4569672081786872143896929 3427254061340154107922697)
      ·
        refine ⟨2570440546005115580942023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3427254061340154107922697 2570440546005115580942023)
        ·
          refine ⟨3855660819007673371413035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570440546005115580942023 3855660819007673371413035)
          ·
            refine ⟨5783491228511510057119553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855660819007673371413035 5783491228511510057119553)
            ·
              refine ⟨4337618421383632542839665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783491228511510057119553 4337618421383632542839665)
              ·
                refine ⟨3253213816037724407129749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337618421383632542839665 3253213816037724407129749)
                ·
                  refine ⟨152494397626768331584207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3253213816037724407129749 152494397626768331584207)
                  ·
                    rfl

theorem cell22_1336418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1336418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336418 prefixEnd_1336418 := by exact prefixLift 1336418
  have htrace : WordTrace (prefixWord ++ tailWord_1336418) baseStart_1336418 baseEnd_1336418 := by
    simpa [prefixWord, tailWord_1336418, baseEnd_1336418] using wordTrace_append hprefix tailTrace_1336418
  have hstable : (prefixWord ++ tailWord_1336418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336418).length < 2 ^ (prefixWord ++ tailWord_1336418).sum := by decide
  have hdescent : baseEnd_1336418 < baseStart_1336418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336431 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 2, 4]
def baseStart_1336431 : Nat := 118140960795 + 1336431 * 2 ^ 59
def prefixEnd_1336431 : Nat := 4983230072969 + 3 ^ 40 * 1336431 * 2
def baseEnd_1336431 : Nat := 457487643045977294177581

theorem tailTrace_1336431 : CollatzResearch.WordTrace tailWord_1336431 prefixEnd_1336431 457487643045977294177581 := by
  unfold tailWord_1336431
  simp only [CollatzResearch.WordTrace]
  refine ⟨48743643021346206088457147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32495762014230804058971431 48743643021346206088457147)
  ·
    refine ⟨73115464532019309132685721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48743643021346206088457147 73115464532019309132685721)
    ·
      refine ⟨54836598399014481849514291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73115464532019309132685721 54836598399014481849514291)
      ·
        refine ⟨82254897598521722774271437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54836598399014481849514291 82254897598521722774271437)
        ·
          refine ⟨30845586599445646040351789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82254897598521722774271437 30845586599445646040351789)
          ·
            refine ⟨11567094974792117265131921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30845586599445646040351789 11567094974792117265131921)
            ·
              refine ⟨8675321231094087948848941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11567094974792117265131921 8675321231094087948848941)
              ·
                refine ⟨3253245461660282980818353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8675321231094087948848941 3253245461660282980818353)
                ·
                  refine ⟨2439934096245212235613765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253245461660282980818353 2439934096245212235613765)
                  ·
                    refine ⟨457487643045977294177581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439934096245212235613765 457487643045977294177581)
                    ·
                      rfl

theorem cell22_1336431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_1336431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336431 prefixEnd_1336431 := by exact prefixLift 1336431
  have htrace : WordTrace (prefixWord ++ tailWord_1336431) baseStart_1336431 baseEnd_1336431 := by
    simpa [prefixWord, tailWord_1336431, baseEnd_1336431] using wordTrace_append hprefix tailTrace_1336431
  have hstable : (prefixWord ++ tailWord_1336431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336431).length < 2 ^ (prefixWord ++ tailWord_1336431).sum := by decide
  have hdescent : baseEnd_1336431 < baseStart_1336431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336506 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1336506 : Nat := 118140960795 + 1336506 * 2 ^ 59
def prefixEnd_1336506 : Nat := 4983230072969 + 3 ^ 40 * 1336506 * 2
def baseEnd_1336506 : Nat := 457513317078702098552351

theorem tailTrace_1336506 : CollatzResearch.WordTrace tailWord_1336506 prefixEnd_1336506 457513317078702098552351 := by
  unfold tailWord_1336506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186594624018623474359343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32497585664049662598291581 12186594624018623474359343)
  ·
    refine ⟨18279891936027935211539015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186594624018623474359343 18279891936027935211539015)
    ·
      refine ⟨27419837904041902817308523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279891936027935211539015 27419837904041902817308523)
      ·
        refine ⟨41129756856062854225962785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27419837904041902817308523 41129756856062854225962785)
        ·
          refine ⟨30847317642047140669472089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41129756856062854225962785 30847317642047140669472089)
          ·
            refine ⟨23135488231535355502104067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30847317642047140669472089 23135488231535355502104067)
            ·
              refine ⟨34703232347303033253156101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23135488231535355502104067 34703232347303033253156101)
              ·
                refine ⟨6506856065119318734966769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34703232347303033253156101 6506856065119318734966769)
                ·
                  refine ⟨4880142048839489051225077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6506856065119318734966769 4880142048839489051225077)
                  ·
                    refine ⟨457513317078702098552351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4880142048839489051225077 457513317078702098552351)
                    ·
                      rfl

theorem cell22_1336506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1336506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336506 prefixEnd_1336506 := by exact prefixLift 1336506
  have htrace : WordTrace (prefixWord ++ tailWord_1336506) baseStart_1336506 baseEnd_1336506 := by
    simpa [prefixWord, tailWord_1336506, baseEnd_1336506] using wordTrace_append hprefix tailTrace_1336506
  have hstable : (prefixWord ++ tailWord_1336506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336506).length < 2 ^ (prefixWord ++ tailWord_1336506).sum := by decide
  have hdescent : baseEnd_1336506 < baseStart_1336506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336508 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_1336508 : Nat := 118140960795 + 1336508 * 2 ^ 59
def prefixEnd_1336508 : Nat := 4983230072969 + 3 ^ 40 * 1336508 * 2
def baseEnd_1336508 : Nat := 152504667239858253334115

theorem tailTrace_1336508 : CollatzResearch.WordTrace tailWord_1336508 prefixEnd_1336508 152504667239858253334115 := by
  unfold tailWord_1336508
  simp only [CollatzResearch.WordTrace]
  refine ⟨24373225721033624119505089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32497634294711498826006785 24373225721033624119505089)
  ·
    refine ⟨18279919290775218089628817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24373225721033624119505089 18279919290775218089628817)
    ·
      refine ⟨13709939468081413567221613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18279919290775218089628817 13709939468081413567221613)
      ·
        refine ⟨5141227300530530087708105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13709939468081413567221613 5141227300530530087708105)
        ·
          refine ⟨3855920475397897565781079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5141227300530530087708105 3855920475397897565781079)
          ·
            refine ⟨5783880713096846348671619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855920475397897565781079 5783880713096846348671619)
            ·
              refine ⟨8675821069645269523007429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783880713096846348671619 8675821069645269523007429)
              ·
                refine ⟨1626716450558488035563893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8675821069645269523007429 1626716450558488035563893)
                ·
                  refine ⟨152504667239858253334115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1626716450558488035563893 152504667239858253334115)
                  ·
                    rfl

theorem cell22_1336508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_1336508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336508 prefixEnd_1336508 := by exact prefixLift 1336508
  have htrace : WordTrace (prefixWord ++ tailWord_1336508) baseStart_1336508 baseEnd_1336508 := by
    simpa [prefixWord, tailWord_1336508, baseEnd_1336508] using wordTrace_append hprefix tailTrace_1336508
  have hstable : (prefixWord ++ tailWord_1336508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336508).length < 2 ^ (prefixWord ++ tailWord_1336508).sum := by decide
  have hdescent : baseEnd_1336508 < baseStart_1336508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336512 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 1, 3]
def baseStart_1336512 : Nat := 118140960795 + 1336512 * 2 ^ 59
def prefixEnd_1336512 : Nat := 4983230072969 + 3 ^ 40 * 1336512 * 2
def baseEnd_1336512 : Nat := 457515371001320082902333

theorem tailTrace_1336512 : CollatzResearch.WordTrace tailWord_1336512 prefixEnd_1336512 457515371001320082902333 := by
  unfold tailWord_1336512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24373298667026378461077895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32497731556035171281437193 24373298667026378461077895)
  ·
    refine ⟨36559948000539567691616843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24373298667026378461077895 36559948000539567691616843)
    ·
      refine ⟨54839922000809351537425265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36559948000539567691616843 54839922000809351537425265)
      ·
        refine ⟨41129941500607013653068949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54839922000809351537425265 41129941500607013653068949)
        ·
          refine ⟨1927966007840953764987607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41129941500607013653068949 1927966007840953764987607)
          ·
            refine ⟨2891949011761430647481411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927966007840953764987607 2891949011761430647481411)
            ·
              refine ⟨4337923517642145971222117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891949011761430647481411 4337923517642145971222117)
              ·
                refine ⟨813360659557902369604147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4337923517642145971222117 813360659557902369604147)
                ·
                  refine ⟨1220040989336853554406221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813360659557902369604147 1220040989336853554406221)
                  ·
                    refine ⟨457515371001320082902333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220040989336853554406221 457515371001320082902333)
                    ·
                      rfl

theorem cell22_1336512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_1336512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336512 prefixEnd_1336512 := by exact prefixLift 1336512
  have htrace : WordTrace (prefixWord ++ tailWord_1336512) baseStart_1336512 baseEnd_1336512 := by
    simpa [prefixWord, tailWord_1336512, baseEnd_1336512] using wordTrace_append hprefix tailTrace_1336512
  have hstable : (prefixWord ++ tailWord_1336512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336512).length < 2 ^ (prefixWord ++ tailWord_1336512).sum := by decide
  have hdescent : baseEnd_1336512 < baseStart_1336512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336514 : List Nat := [3, 5, 1, 1, 3, 1, 1, 7]
def baseStart_1336514 : Nat := 118140960795 + 1336514 * 2 ^ 59
def prefixEnd_1336514 : Nat := 4983230072969 + 3 ^ 40 * 1336514 * 2
def baseEnd_1336514 : Nat := 50835117293576971594703

theorem tailTrace_1336514 : CollatzResearch.WordTrace tailWord_1336514 prefixEnd_1336514 50835117293576971594703 := by
  unfold tailWord_1336514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186667570011377815932149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32497780186697007509152397 12186667570011377815932149)
  ·
    refine ⟨1142500084688566670243639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12186667570011377815932149 1142500084688566670243639)
    ·
      refine ⟨1713750127032850005365459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142500084688566670243639 1713750127032850005365459)
      ·
        refine ⟨2570625190549275008048189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713750127032850005365459 2570625190549275008048189)
        ·
          refine ⟨963984446455978128018071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2570625190549275008048189 963984446455978128018071)
          ·
            refine ⟨1445976669683967192027107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963984446455978128018071 1445976669683967192027107)
            ·
              refine ⟨2168965004525950788040661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445976669683967192027107 2168965004525950788040661)
              ·
                refine ⟨50835117293576971594703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2168965004525950788040661 50835117293576971594703)
                ·
                  rfl

theorem cell22_1336514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_1336514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336514 prefixEnd_1336514 := by exact prefixLift 1336514
  have htrace : WordTrace (prefixWord ++ tailWord_1336514) baseStart_1336514 baseEnd_1336514 := by
    simpa [prefixWord, tailWord_1336514, baseEnd_1336514] using wordTrace_append hprefix tailTrace_1336514
  have hstable : (prefixWord ++ tailWord_1336514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336514).length < 2 ^ (prefixWord ++ tailWord_1336514).sum := by decide
  have hdescent : baseEnd_1336514 < baseStart_1336514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336538 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_1336538 : Nat := 118140960795 + 1336538 * 2 ^ 59
def prefixEnd_1336538 : Nat := 4983230072969 + 3 ^ 40 * 1336538 * 2
def baseEnd_1336538 : Nat := 457524271332664681752253

theorem tailTrace_1336538 : CollatzResearch.WordTrace tailWord_1336538 prefixEnd_1336538 457524271332664681752253 := by
  unfold tailWord_1336538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186886407989640840650567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32498363754639042241734845 12186886407989640840650567)
  ·
    refine ⟨18280329611984461260975851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186886407989640840650567 18280329611984461260975851)
    ·
      refine ⟨27420494417976691891463777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18280329611984461260975851 27420494417976691891463777)
      ·
        refine ⟨20565370813482518918597833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27420494417976691891463777 20565370813482518918597833)
        ·
          refine ⟨15424028110111889188948375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20565370813482518918597833 15424028110111889188948375)
          ·
            refine ⟨23136042165167833783422563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15424028110111889188948375 23136042165167833783422563)
            ·
              refine ⟨34704063247751750675133845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23136042165167833783422563 34704063247751750675133845)
              ·
                refine ⟨1626752964738363312896899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34704063247751750675133845 1626752964738363312896899)
                ·
                  refine ⟨2440129447107544969345349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626752964738363312896899 2440129447107544969345349)
                  ·
                    refine ⟨457524271332664681752253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440129447107544969345349 457524271332664681752253)
                    ·
                      rfl

theorem cell22_1336538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_1336538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336538 prefixEnd_1336538 := by exact prefixLift 1336538
  have htrace : WordTrace (prefixWord ++ tailWord_1336538) baseStart_1336538 baseEnd_1336538 := by
    simpa [prefixWord, tailWord_1336538, baseEnd_1336538] using wordTrace_append hprefix tailTrace_1336538
  have hstable : (prefixWord ++ tailWord_1336538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336538).length < 2 ^ (prefixWord ++ tailWord_1336538).sum := by decide
  have hdescent : baseEnd_1336538 < baseStart_1336538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336555 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 1, 4]
def baseStart_1336555 : Nat := 118140960795 + 1336555 * 2 ^ 59
def prefixEnd_1336555 : Nat := 4983230072969 + 3 ^ 40 * 1336555 * 2
def baseEnd_1336555 : Nat := 457530090780082304077201

theorem tailTrace_1336555 : CollatzResearch.WordTrace tailWord_1336555 prefixEnd_1336555 457530090780082304077201 := by
  unfold tailWord_1336555
  simp only [CollatzResearch.WordTrace]
  refine ⟨48748165672896975265971119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32498777115264650177314079 48748165672896975265971119)
  ·
    refine ⟨73122248509345462898956679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48748165672896975265971119 73122248509345462898956679)
    ·
      refine ⟨109683372764018194348435019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73122248509345462898956679 109683372764018194348435019)
      ·
        refine ⟨164525059146027291522652529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109683372764018194348435019 164525059146027291522652529)
        ·
          refine ⟨123393794359520468641989397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164525059146027291522652529 123393794359520468641989397)
          ·
            refine ⟨5784084110602521967593253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123393794359520468641989397 5784084110602521967593253)
            ·
              refine ⟨1084515770737972868923735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5784084110602521967593253 1084515770737972868923735)
              ·
                refine ⟨1626773656106959303385603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084515770737972868923735 1626773656106959303385603)
                ·
                  refine ⟨2440160484160438955078405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626773656106959303385603 2440160484160438955078405)
                  ·
                    refine ⟨457530090780082304077201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440160484160438955078405 457530090780082304077201)
                    ·
                      rfl

theorem cell22_1336555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 4].length) (baseStart_1336555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336555 prefixEnd_1336555 := by exact prefixLift 1336555
  have htrace : WordTrace (prefixWord ++ tailWord_1336555) baseStart_1336555 baseEnd_1336555 := by
    simpa [prefixWord, tailWord_1336555, baseEnd_1336555] using wordTrace_append hprefix tailTrace_1336555
  have hstable : (prefixWord ++ tailWord_1336555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336555).length < 2 ^ (prefixWord ++ tailWord_1336555).sum := by decide
  have hdescent : baseEnd_1336555 < baseStart_1336555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336581 : List Nat := [1, 3, 1, 1, 2, 1, 4, 9]
def baseStart_1336581 : Nat := 118140960795 + 1336581 * 2 ^ 59
def prefixEnd_1336581 : Nat := 4983230072969 + 3 ^ 40 * 1336581 * 2
def baseEnd_1336581 : Nat := 50837665679047433658569

theorem tailTrace_1336581 : CollatzResearch.WordTrace tailWord_1336581 prefixEnd_1336581 50837665679047433658569 := by
  unfold tailWord_1336581
  simp only [CollatzResearch.WordTrace]
  refine ⟨48749113970802781706417597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32499409313868521137611731 48749113970802781706417597)
  ·
    refine ⟨18280917739051043139906599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48749113970802781706417597 18280917739051043139906599)
    ·
      refine ⟨27421376608576564709859899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18280917739051043139906599 27421376608576564709859899)
      ·
        refine ⟨41132064912864847064789849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27421376608576564709859899 41132064912864847064789849)
        ·
          refine ⟨30849048684648635298592387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41132064912864847064789849 30849048684648635298592387)
          ·
            refine ⟨46273573026972952947888581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30849048684648635298592387 46273573026972952947888581)
            ·
              refine ⟨8676294942557428677729109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46273573026972952947888581 8676294942557428677729109)
              ·
                refine ⟨50837665679047433658569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8676294942557428677729109 50837665679047433658569)
                ·
                  rfl

theorem cell22_1336581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 9].length) (baseStart_1336581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336581 prefixEnd_1336581 := by exact prefixLift 1336581
  have htrace : WordTrace (prefixWord ++ tailWord_1336581) baseStart_1336581 baseEnd_1336581 := by
    simpa [prefixWord, tailWord_1336581, baseEnd_1336581] using wordTrace_append hprefix tailTrace_1336581
  have hstable : (prefixWord ++ tailWord_1336581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336581).length < 2 ^ (prefixWord ++ tailWord_1336581).sum := by decide
  have hdescent : baseEnd_1336581 < baseStart_1336581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336658 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1336658 : Nat := 118140960795 + 1336658 * 2 ^ 59
def prefixEnd_1336658 : Nat := 4983230072969 + 3 ^ 40 * 1336658 * 2
def baseEnd_1336658 : Nat := 457565349785024368751885

theorem tailTrace_1336658 : CollatzResearch.WordTrace tailWord_1336658 prefixEnd_1336658 457565349785024368751885 := by
  unfold tailWord_1336658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12187980597880955964242657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32501281594349215904647085 12187980597880955964242657)
  ·
    refine ⟨9140985448410716973181993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12187980597880955964242657 9140985448410716973181993)
    ·
      refine ⟨6855739086308037729886495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9140985448410716973181993 6855739086308037729886495)
      ·
        refine ⟨10283608629462056594829743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6855739086308037729886495 10283608629462056594829743)
        ·
          refine ⟨15425412944193084892244615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10283608629462056594829743 15425412944193084892244615)
          ·
            refine ⟨23138119416289627338366923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15425412944193084892244615 23138119416289627338366923)
            ·
              refine ⟨34707179124434441007550385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23138119416289627338366923 34707179124434441007550385)
              ·
                refine ⟨26030384343325830755662789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34707179124434441007550385 26030384343325830755662789)
                ·
                  refine ⟨4880697064373593266686773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26030384343325830755662789 4880697064373593266686773)
                  ·
                    refine ⟨457565349785024368751885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4880697064373593266686773 457565349785024368751885)
                    ·
                      rfl

theorem cell22_1336658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1336658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336658 prefixEnd_1336658 := by exact prefixLift 1336658
  have htrace : WordTrace (prefixWord ++ tailWord_1336658) baseStart_1336658 baseEnd_1336658 := by
    simpa [prefixWord, tailWord_1336658, baseEnd_1336658] using wordTrace_append hprefix tailTrace_1336658
  have hstable : (prefixWord ++ tailWord_1336658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336658).length < 2 ^ (prefixWord ++ tailWord_1336658).sum := by decide
  have hdescent : baseEnd_1336658 < baseStart_1336658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336688 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_1336688 : Nat := 118140960795 + 1336688 * 2 ^ 59
def prefixEnd_1336688 : Nat := 4983230072969 + 3 ^ 40 * 1336688 * 2
def baseEnd_1336688 : Nat := 152525206466038096833931

theorem tailTrace_1336688 : CollatzResearch.WordTrace tailWord_1336688 prefixEnd_1336688 152525206466038096833931 := by
  unfold tailWord_1336688
  simp only [CollatzResearch.WordTrace]
  refine ⟨24376508290707569490281359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32502011054276759320375145 24376508290707569490281359)
  ·
    refine ⟨36564762436061354235422039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24376508290707569490281359 36564762436061354235422039)
    ·
      refine ⟨54847143654092031353133059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36564762436061354235422039 54847143654092031353133059)
      ·
        refine ⟨82270715481138047029699589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54847143654092031353133059 82270715481138047029699589)
        ·
          refine ⟨15425759152713383818068673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82270715481138047029699589 15425759152713383818068673)
          ·
            refine ⟨11569319364535037863551505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15425759152713383818068673 11569319364535037863551505)
            ·
              refine ⟨8676989523401278397663629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11569319364535037863551505 8676989523401278397663629)
              ·
                refine ⟨3253871071275479399123861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8676989523401278397663629 3253871071275479399123861)
                ·
                  refine ⟨152525206466038096833931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3253871071275479399123861 152525206466038096833931)
                  ·
                    rfl

theorem cell22_1336688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_1336688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336688 prefixEnd_1336688 := by exact prefixLift 1336688
  have htrace : WordTrace (prefixWord ++ tailWord_1336688) baseStart_1336688 baseEnd_1336688 := by
    simpa [prefixWord, tailWord_1336688, baseEnd_1336688] using wordTrace_append hprefix tailTrace_1336688
  have hstable : (prefixWord ++ tailWord_1336688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336688).length < 2 ^ (prefixWord ++ tailWord_1336688).sum := by decide
  have hdescent : baseEnd_1336688 < baseStart_1336688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336724 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1336724 : Nat := 118140960795 + 1336724 * 2 ^ 59
def prefixEnd_1336724 : Nat := 4983230072969 + 3 ^ 40 * 1336724 * 2
def baseEnd_1336724 : Nat := 457587942933822196601683

theorem tailTrace_1336724 : CollatzResearch.WordTrace tailWord_1336724 prefixEnd_1336724 457587942933822196601683 := by
  unfold tailWord_1336724
  simp only [CollatzResearch.WordTrace]
  refine ⟨24377164804642358564436613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32502886406189811419248817 24377164804642358564436613)
  ·
    refine ⟨4570718400870442230831865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24377164804642358564436613 4570718400870442230831865)
    ·
      refine ⟨3428038800652831673123899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4570718400870442230831865 3428038800652831673123899)
      ·
        refine ⟨5142058200979247509685849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428038800652831673123899 5142058200979247509685849)
        ·
          refine ⟨3856543650734435632264387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5142058200979247509685849 3856543650734435632264387)
          ·
            refine ⟨5784815476101653448396581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856543650734435632264387 5784815476101653448396581)
            ·
              refine ⟨1084652901769060021574359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5784815476101653448396581 1084652901769060021574359)
              ·
                refine ⟨1626979352653590032361539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084652901769060021574359 1626979352653590032361539)
                ·
                  refine ⟨2440469028980385048542309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626979352653590032361539 2440469028980385048542309)
                  ·
                    refine ⟨457587942933822196601683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440469028980385048542309 457587942933822196601683)
                    ·
                      rfl

theorem cell22_1336724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1336724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336724 prefixEnd_1336724 := by exact prefixLift 1336724
  have htrace : WordTrace (prefixWord ++ tailWord_1336724) baseStart_1336724 baseEnd_1336724 := by
    simpa [prefixWord, tailWord_1336724, baseEnd_1336724] using wordTrace_append hprefix tailTrace_1336724
  have hstable : (prefixWord ++ tailWord_1336724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336724).length < 2 ^ (prefixWord ++ tailWord_1336724).sum := by decide
  have hdescent : baseEnd_1336724 < baseStart_1336724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336887 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 2, 4]
def baseStart_1336887 : Nat := 118140960795 + 1336887 * 2 ^ 59
def prefixEnd_1336887 : Nat := 4983230072969 + 3 ^ 40 * 1336887 * 2
def baseEnd_1336887 : Nat := 457643741164944104776183

theorem tailTrace_1336887 : CollatzResearch.WordTrace tailWord_1336887 prefixEnd_1336887 457643741164944104776183 := by
  unfold tailWord_1336887
  simp only [CollatzResearch.WordTrace]
  refine ⟨48760274707694195967056915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32506849805129463978037943 48760274707694195967056915)
  ·
    refine ⟨73140412061541293950585373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48760274707694195967056915 73140412061541293950585373)
    ·
      refine ⟨27427654523077985231469515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73140412061541293950585373 27427654523077985231469515)
      ·
        refine ⟨41141481784616977847204273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27427654523077985231469515 41141481784616977847204273)
        ·
          refine ⟨30856111338462733385403205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41141481784616977847204273 30856111338462733385403205)
          ·
            refine ⟨5785520875961762509763101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30856111338462733385403205 5785520875961762509763101)
            ·
              refine ⟨2169570328485660941161163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5785520875961762509763101 2169570328485660941161163)
              ·
                refine ⟨3254355492728491411741745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169570328485660941161163 3254355492728491411741745)
                ·
                  refine ⟨2440766619546368558806309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254355492728491411741745 2440766619546368558806309)
                  ·
                    refine ⟨457643741164944104776183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440766619546368558806309 457643741164944104776183)
                    ·
                      rfl

theorem cell22_1336887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_1336887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336887 prefixEnd_1336887 := by exact prefixLift 1336887
  have htrace : WordTrace (prefixWord ++ tailWord_1336887) baseStart_1336887 baseEnd_1336887 := by
    simpa [prefixWord, tailWord_1336887, baseEnd_1336887] using wordTrace_append hprefix tailTrace_1336887
  have hstable : (prefixWord ++ tailWord_1336887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336887).length < 2 ^ (prefixWord ++ tailWord_1336887).sum := by decide
  have hdescent : baseEnd_1336887 < baseStart_1336887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336893 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1336893 : Nat := 118140960795 + 1336893 * 2 ^ 59
def prefixEnd_1336893 : Nat := 4983230072969 + 3 ^ 40 * 1336893 * 2
def baseEnd_1336893 : Nat := 457645795087562089126165

theorem tailTrace_1336893 : CollatzResearch.WordTrace tailWord_1336893 prefixEnd_1336893 457645795087562089126165 := by
  unfold tailWord_1336893
  simp only [CollatzResearch.WordTrace]
  refine ⟨48760493545672458991775333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32506995697114972661183555 48760493545672458991775333)
  ·
    refine ⟨9142592539813586060957875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48760493545672458991775333 9142592539813586060957875)
    ·
      refine ⟨13713888809720379091436813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9142592539813586060957875 13713888809720379091436813)
      ·
        refine ⟨5142708303645142159288805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13713888809720379091436813 5142708303645142159288805)
        ·
          refine ⟨964257806933464154866651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5142708303645142159288805 964257806933464154866651)
          ·
            refine ⟨1446386710400196232299977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964257806933464154866651 1446386710400196232299977)
            ·
              refine ⟨1084790032800147174224983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446386710400196232299977 1084790032800147174224983)
              ·
                refine ⟨1627185049200220761337475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084790032800147174224983 1627185049200220761337475)
                ·
                  refine ⟨2440777573800331142006213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627185049200220761337475 2440777573800331142006213)
                  ·
                    refine ⟨457645795087562089126165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440777573800331142006213 457645795087562089126165)
                    ·
                      rfl

theorem cell22_1336893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1336893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336893 prefixEnd_1336893 := by exact prefixLift 1336893
  have htrace : WordTrace (prefixWord ++ tailWord_1336893) baseStart_1336893 baseEnd_1336893 := by
    simpa [prefixWord, tailWord_1336893, baseEnd_1336893] using wordTrace_append hprefix tailTrace_1336893
  have hstable : (prefixWord ++ tailWord_1336893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336893).length < 2 ^ (prefixWord ++ tailWord_1336893).sum := by decide
  have hdescent : baseEnd_1336893 < baseStart_1336893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336945 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_1336945 : Nat := 118140960795 + 1336945 * 2 ^ 59
def prefixEnd_1336945 : Nat := 4983230072969 + 3 ^ 40 * 1336945 * 2
def baseEnd_1336945 : Nat := 457663595750251286826005

theorem tailTrace_1336945 : CollatzResearch.WordTrace tailWord_1336945 prefixEnd_1336945 457663595750251286826005 := by
  unfold tailWord_1336945
  simp only [CollatzResearch.WordTrace]
  refine ⟨48762390141484071872668289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32508260094322714581778859 48762390141484071872668289)
  ·
    refine ⟨36571792606113053904501217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48762390141484071872668289 36571792606113053904501217)
    ·
      refine ⟨27428844454584790428375913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36571792606113053904501217 27428844454584790428375913)
      ·
        refine ⟨20571633340938592821281935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27428844454584790428375913 20571633340938592821281935)
        ·
          refine ⟨30857450011407889231922903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20571633340938592821281935 30857450011407889231922903)
          ·
            refine ⟨46286175017111833847884355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30857450011407889231922903 46286175017111833847884355)
            ·
              refine ⟨69429262525667750771826533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46286175017111833847884355 69429262525667750771826533)
              ·
                refine ⟨13017986723562703269717475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69429262525667750771826533 13017986723562703269717475)
                ·
                  refine ⟨19526980085344054904576213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13017986723562703269717475 19526980085344054904576213)
                  ·
                    refine ⟨457663595750251286826005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19526980085344054904576213 457663595750251286826005)
                    ·
                      rfl

theorem cell22_1336945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_1336945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336945 prefixEnd_1336945 := by exact prefixLift 1336945
  have htrace : WordTrace (prefixWord ++ tailWord_1336945) baseStart_1336945 baseEnd_1336945 := by
    simpa [prefixWord, tailWord_1336945, baseEnd_1336945] using wordTrace_append hprefix tailTrace_1336945
  have hstable : (prefixWord ++ tailWord_1336945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336945).length < 2 ^ (prefixWord ++ tailWord_1336945).sum := by decide
  have hdescent : baseEnd_1336945 < baseStart_1336945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336968 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1336968 : Nat := 118140960795 + 1336968 * 2 ^ 59
def prefixEnd_1336968 : Nat := 4983230072969 + 3 ^ 40 * 1336968 * 2
def baseEnd_1336968 : Nat := 457671469120286893500935

theorem tailTrace_1336968 : CollatzResearch.WordTrace tailWord_1336968 prefixEnd_1336968 457671469120286893500935 := by
  unfold tailWord_1336968
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381614510200373400377779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32508819346933831200503705 24381614510200373400377779)
  ·
    refine ⟨36572421765300560100566669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24381614510200373400377779 36572421765300560100566669)
    ·
      refine ⟨13714658161987710037712501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36572421765300560100566669 13714658161987710037712501)
      ·
        refine ⟨1285749202686347816035547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13714658161987710037712501 1285749202686347816035547)
        ·
          refine ⟨1928623804029521724053321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285749202686347816035547 1928623804029521724053321)
          ·
            refine ⟨1446467853022141293039991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928623804029521724053321 1446467853022141293039991)
            ·
              refine ⟨2169701779533211939559987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446467853022141293039991 2169701779533211939559987)
              ·
                refine ⟨3254552669299817909339981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169701779533211939559987 3254552669299817909339981)
                ·
                  refine ⟨1220457250987431716002493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3254552669299817909339981 1220457250987431716002493)
                  ·
                    refine ⟨457671469120286893500935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220457250987431716002493 457671469120286893500935)
                    ·
                      rfl

theorem cell22_1336968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1336968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1336968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1336968 prefixEnd_1336968 := by exact prefixLift 1336968
  have htrace : WordTrace (prefixWord ++ tailWord_1336968) baseStart_1336968 baseEnd_1336968 := by
    simpa [prefixWord, tailWord_1336968, baseEnd_1336968] using wordTrace_append hprefix tailTrace_1336968
  have hstable : (prefixWord ++ tailWord_1336968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336968).length < 2 ^ (prefixWord ++ tailWord_1336968).sum := by decide
  have hdescent : baseEnd_1336968 < baseStart_1336968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337007 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 1, 5]
def baseStart_1337007 : Nat := 118140960795 + 1337007 * 2 ^ 59
def prefixEnd_1337007 : Nat := 4983230072969 + 3 ^ 40 * 1337007 * 2
def baseEnd_1337007 : Nat := 457684819617303791775815

theorem tailTrace_1337007 : CollatzResearch.WordTrace tailWord_1337007 prefixEnd_1337007 457684819617303791775815 := by
  unfold tailWord_1337007
  simp only [CollatzResearch.WordTrace]
  refine ⟨48764651467259456461425275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32509767644839637640950183 48764651467259456461425275)
  ·
    refine ⟨73146977200889184692137913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48764651467259456461425275 73146977200889184692137913)
    ·
      refine ⟨54860232900666888519103435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73146977200889184692137913 54860232900666888519103435)
      ·
        refine ⟨82290349351000332778655153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54860232900666888519103435 82290349351000332778655153)
        ·
          refine ⟨61717762013250249583991365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82290349351000332778655153 61717762013250249583991365)
          ·
            refine ⟨11572080377484421796998381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61717762013250249583991365 11572080377484421796998381)
            ·
              refine ⟨4339530141556658173874393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11572080377484421796998381 4339530141556658173874393)
              ·
                refine ⟨3254647606167493630405795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339530141556658173874393 3254647606167493630405795)
                ·
                  refine ⟨4881971409251240445608693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254647606167493630405795 4881971409251240445608693)
                  ·
                    refine ⟨457684819617303791775815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4881971409251240445608693 457684819617303791775815)
                    ·
                      rfl

theorem cell22_1337007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_1337007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337007 prefixEnd_1337007 := by exact prefixLift 1337007
  have htrace : WordTrace (prefixWord ++ tailWord_1337007) baseStart_1337007 baseEnd_1337007 := by
    simpa [prefixWord, tailWord_1337007, baseEnd_1337007] using wordTrace_append hprefix tailTrace_1337007
  have hstable : (prefixWord ++ tailWord_1337007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337007).length < 2 ^ (prefixWord ++ tailWord_1337007).sum := by decide
  have hdescent : baseEnd_1337007 < baseStart_1337007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337144 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_1337144 : Nat := 118140960795 + 1337144 * 2 ^ 59
def prefixEnd_1337144 : Nat := 4983230072969 + 3 ^ 40 * 1337144 * 2
def baseEnd_1337144 : Nat := 152577239172360367033465

theorem tailTrace_1337144 : CollatzResearch.WordTrace tailWord_1337144 prefixEnd_1337144 152577239172360367033465 := by
  unfold tailWord_1337144
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384824133881564429581243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32513098845175419239441657 24384824133881564429581243)
  ·
    refine ⟨36577236200822346644371865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24384824133881564429581243 36577236200822346644371865)
    ·
      refine ⟨27432927150616759983278899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36577236200822346644371865 27432927150616759983278899)
      ·
        refine ⟨41149390725925139974918349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27432927150616759983278899 41149390725925139974918349)
        ·
          refine ⟨15431021522221927490594381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41149390725925139974918349 15431021522221927490594381)
          ·
            refine ⟨5786633070833222808972893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15431021522221927490594381 5786633070833222808972893)
            ·
              refine ⟨2169987401562458553364835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5786633070833222808972893 2169987401562458553364835)
              ·
                refine ⟨3254981102343687830047253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169987401562458553364835 3254981102343687830047253)
                ·
                  refine ⟨152577239172360367033465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3254981102343687830047253 152577239172360367033465)
                  ·
                    rfl

theorem cell22_1337144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_1337144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337144 prefixEnd_1337144 := by exact prefixLift 1337144
  have htrace : WordTrace (prefixWord ++ tailWord_1337144) baseStart_1337144 baseEnd_1337144 := by
    simpa [prefixWord, tailWord_1337144, baseEnd_1337144] using wordTrace_append hprefix tailTrace_1337144
  have hstable : (prefixWord ++ tailWord_1337144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337144).length < 2 ^ (prefixWord ++ tailWord_1337144).sum := by decide
  have hdescent : baseEnd_1337144 < baseStart_1337144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337180 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1337180 : Nat := 118140960795 + 1337180 * 2 ^ 59
def prefixEnd_1337180 : Nat := 4983230072969 + 3 ^ 40 * 1337180 * 2
def baseEnd_1337180 : Nat := 457744041052789007200285

theorem tailTrace_1337180 : CollatzResearch.WordTrace tailWord_1337180 prefixEnd_1337180 457744041052789007200285 := by
  unfold tailWord_1337180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24385480647816353503736497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32513974197088471338315329 24385480647816353503736497)
  ·
    refine ⟨18289110485862265127802373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24385480647816353503736497 18289110485862265127802373)
    ·
      refine ⟨3429208216099174711462945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18289110485862265127802373 3429208216099174711462945)
      ·
        refine ⟨2571906162074381033597209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3429208216099174711462945 2571906162074381033597209)
        ·
          refine ⟨1928929621555785775197907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2571906162074381033597209 1928929621555785775197907)
          ·
            refine ⟨2893394432333678662796861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928929621555785775197907 2893394432333678662796861)
            ·
              refine ⟨1085022912125129498548823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2893394432333678662796861 1085022912125129498548823)
              ·
                refine ⟨1627534368187694247823235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085022912125129498548823 1627534368187694247823235)
                ·
                  refine ⟨2441301552281541371734853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627534368187694247823235 2441301552281541371734853)
                  ·
                    refine ⟨457744041052789007200285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2441301552281541371734853 457744041052789007200285)
                    ·
                      rfl

theorem cell22_1337180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1337180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337180 prefixEnd_1337180 := by exact prefixLift 1337180
  have htrace : WordTrace (prefixWord ++ tailWord_1337180) baseStart_1337180 baseEnd_1337180 := by
    simpa [prefixWord, tailWord_1337180, baseEnd_1337180] using wordTrace_append hprefix tailTrace_1337180
  have hstable : (prefixWord ++ tailWord_1337180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337180).length < 2 ^ (prefixWord ++ tailWord_1337180).sum := by decide
  have hdescent : baseEnd_1337180 < baseStart_1337180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337221 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_1337221 : Nat := 118140960795 + 1337221 * 2 ^ 59
def prefixEnd_1337221 : Nat := 4983230072969 + 3 ^ 40 * 1337221 * 2
def baseEnd_1337221 : Nat := 457758076190678566925159

theorem tailTrace_1337221 : CollatzResearch.WordTrace tailWord_1337221 prefixEnd_1337221 457758076190678566925159 := by
  unfold tailWord_1337221
  simp only [CollatzResearch.WordTrace]
  refine ⟨48772456688484171009715517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32514971125656114006477011 48772456688484171009715517)
  ·
    refine ⟨18289671258181564128643319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48772456688484171009715517 18289671258181564128643319)
    ·
      refine ⟨27434506887272346192964979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18289671258181564128643319 27434506887272346192964979)
      ·
        refine ⟨41151760330908519289447469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27434506887272346192964979 41151760330908519289447469)
        ·
          refine ⟨15431910124090694733542801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41151760330908519289447469 15431910124090694733542801)
          ·
            refine ⟨11573932593068021050157101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15431910124090694733542801 11573932593068021050157101)
            ·
              refine ⟨4340224722400507893808913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11573932593068021050157101 4340224722400507893808913)
              ·
                refine ⟨3255168541800380920356685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340224722400507893808913 3255168541800380920356685)
                ·
                  refine ⟨1220688203175142845133757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3255168541800380920356685 1220688203175142845133757)
                  ·
                    refine ⟨457758076190678566925159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220688203175142845133757 457758076190678566925159)
                    ·
                      rfl

theorem cell22_1337221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_1337221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337221 prefixEnd_1337221 := by exact prefixLift 1337221
  have htrace : WordTrace (prefixWord ++ tailWord_1337221) baseStart_1337221 baseEnd_1337221 := by
    simpa [prefixWord, tailWord_1337221, baseEnd_1337221] using wordTrace_append hprefix tailTrace_1337221
  have hstable : (prefixWord ++ tailWord_1337221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337221).length < 2 ^ (prefixWord ++ tailWord_1337221).sum := by decide
  have hdescent : baseEnd_1337221 < baseStart_1337221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337255 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1337255 : Nat := 118140960795 + 1337255 * 2 ^ 59
def prefixEnd_1337255 : Nat := 4983230072969 + 3 ^ 40 * 1337255 * 2
def baseEnd_1337255 : Nat := 457769715085513811575055

theorem tailTrace_1337255 : CollatzResearch.WordTrace tailWord_1337255 prefixEnd_1337255 457769715085513811575055 := by
  unfold tailWord_1337255
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773696770360994816453219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32515797846907329877635479 48773696770360994816453219)
  ·
    refine ⟨73160545155541492224679829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48773696770360994816453219 73160545155541492224679829)
    ·
      refine ⟨3429400554166007448031867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73160545155541492224679829 3429400554166007448031867)
      ·
        refine ⟨5144100831249011172047801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429400554166007448031867 5144100831249011172047801)
        ·
          refine ⟨3858075623436758379035851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5144100831249011172047801 3858075623436758379035851)
          ·
            refine ⟨5787113435155137568553777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858075623436758379035851 5787113435155137568553777)
            ·
              refine ⟨4340335076366353176415333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787113435155137568553777 4340335076366353176415333)
              ·
                refine ⟨813812826818691220577875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4340335076366353176415333 813812826818691220577875)
                ·
                  refine ⟨1220719240228036830866813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813812826818691220577875 1220719240228036830866813)
                  ·
                    refine ⟨457769715085513811575055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220719240228036830866813 457769715085513811575055)
                    ·
                      rfl

theorem cell22_1337255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1337255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337255 prefixEnd_1337255 := by exact prefixLift 1337255
  have htrace : WordTrace (prefixWord ++ tailWord_1337255) baseStart_1337255 baseEnd_1337255 := by
    simpa [prefixWord, tailWord_1337255, baseEnd_1337255] using wordTrace_append hprefix tailTrace_1337255
  have hstable : (prefixWord ++ tailWord_1337255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337255).length < 2 ^ (prefixWord ++ tailWord_1337255).sum := by decide
  have hdescent : baseEnd_1337255 < baseStart_1337255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337279 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 6]
def baseStart_1337279 : Nat := 118140960795 + 1337279 * 2 ^ 59
def prefixEnd_1337279 : Nat := 4983230072969 + 3 ^ 40 * 1337279 * 2
def baseEnd_1337279 : Nat := 152592643591995249658327

theorem tailTrace_1337279 : CollatzResearch.WordTrace tailWord_1337279 prefixEnd_1337279 152592643591995249658327 := by
  unfold tailWord_1337279
  simp only [CollatzResearch.WordTrace]
  refine ⟨48774572122274046915326891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32516381414849364610217927 48774572122274046915326891)
  ·
    refine ⟨73161858183411070372990337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48774572122274046915326891 73161858183411070372990337)
    ·
      refine ⟨54871393637558302779742753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73161858183411070372990337 54871393637558302779742753)
      ·
        refine ⟨41153545228168727084807065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54871393637558302779742753 41153545228168727084807065)
        ·
          refine ⟨30865158921126545313605299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41153545228168727084807065 30865158921126545313605299)
          ·
            refine ⟨46297738381689817970407949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30865158921126545313605299 46297738381689817970407949)
            ·
              refine ⟨17361651893133681738902981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46297738381689817970407949 17361651893133681738902981)
              ·
                refine ⟨3255309729962565326044309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17361651893133681738902981 3255309729962565326044309)
                ·
                  refine ⟨152592643591995249658327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3255309729962565326044309 152592643591995249658327)
                  ·
                    rfl

theorem cell22_1337279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 6].length) (baseStart_1337279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337279 prefixEnd_1337279 := by exact prefixLift 1337279
  have htrace : WordTrace (prefixWord ++ tailWord_1337279) baseStart_1337279 baseEnd_1337279 := by
    simpa [prefixWord, tailWord_1337279, baseEnd_1337279] using wordTrace_append hprefix tailTrace_1337279
  have hstable : (prefixWord ++ tailWord_1337279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337279).length < 2 ^ (prefixWord ++ tailWord_1337279).sum := by decide
  have hdescent : baseEnd_1337279 < baseStart_1337279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337339 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_1337339 : Nat := 118140960795 + 1337339 * 2 ^ 59
def prefixEnd_1337339 : Nat := 4983230072969 + 3 ^ 40 * 1337339 * 2
def baseEnd_1337339 : Nat := 457798470002165592474797

theorem tailTrace_1337339 : CollatzResearch.WordTrace tailWord_1337339 prefixEnd_1337339 457798470002165592474797 := by
  unfold tailWord_1337339
  simp only [CollatzResearch.WordTrace]
  refine ⟨48776760502056677162511071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32517840334704451441674047 48776760502056677162511071)
  ·
    refine ⟨73165140753085015743766607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48776760502056677162511071 73165140753085015743766607)
    ·
      refine ⟨109747711129627523615649911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73165140753085015743766607 109747711129627523615649911)
      ·
        refine ⟨164621566694441285423474867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109747711129627523615649911 164621566694441285423474867)
        ·
          refine ⟨246932350041661928135212301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164621566694441285423474867 246932350041661928135212301)
          ·
            refine ⟨92599631265623223050704613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246932350041661928135212301 92599631265623223050704613)
            ·
              refine ⟨17362430862304354322007115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92599631265623223050704613 17362430862304354322007115)
              ·
                refine ⟨26043646293456531483010673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17362430862304354322007115 26043646293456531483010673)
                ·
                  refine ⟨19532734720092398612258005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26043646293456531483010673 19532734720092398612258005)
                  ·
                    refine ⟨457798470002165592474797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19532734720092398612258005 457798470002165592474797)
                    ·
                      rfl

theorem cell22_1337339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_1337339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337339 prefixEnd_1337339 := by exact prefixLift 1337339
  have htrace : WordTrace (prefixWord ++ tailWord_1337339) baseStart_1337339 baseEnd_1337339 := by
    simpa [prefixWord, tailWord_1337339, baseEnd_1337339] using wordTrace_append hprefix tailTrace_1337339
  have hstable : (prefixWord ++ tailWord_1337339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337339).length < 2 ^ (prefixWord ++ tailWord_1337339).sum := by decide
  have hdescent : baseEnd_1337339 < baseStart_1337339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337390 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1337390 : Nat := 118140960795 + 1337390 * 2 ^ 59
def prefixEnd_1337390 : Nat := 4983230072969 + 3 ^ 40 * 1337390 * 2
def baseEnd_1337390 : Nat := 457815928344418459449641

theorem tailTrace_1337390 : CollatzResearch.WordTrace tailWord_1337390 prefixEnd_1337390 457815928344418459449641 := by
  unfold tailWord_1337390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097327578108989109077203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32519080416581275248411749 6097327578108989109077203)
  ·
    refine ⟨9145991367163483663615805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6097327578108989109077203 9145991367163483663615805)
    ·
      refine ⟨3429746762686306373855927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9145991367163483663615805 3429746762686306373855927)
      ·
        refine ⟨5144620144029459560783891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429746762686306373855927 5144620144029459560783891)
        ·
          refine ⟨7716930216044189341175837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144620144029459560783891 7716930216044189341175837)
          ·
            refine ⟨2893848831016571002940939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7716930216044189341175837 2893848831016571002940939)
            ·
              refine ⟨4340773246524856504411409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893848831016571002940939 4340773246524856504411409)
              ·
                refine ⟨3255579934893642378308557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340773246524856504411409 3255579934893642378308557)
                ·
                  refine ⟨1220842475585115891865709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3255579934893642378308557 1220842475585115891865709)
                  ·
                    refine ⟨457815928344418459449641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220842475585115891865709 457815928344418459449641)
                    ·
                      rfl

theorem cell22_1337390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1337390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337390 prefixEnd_1337390 := by exact prefixLift 1337390
  have htrace : WordTrace (prefixWord ++ tailWord_1337390) baseStart_1337390 baseEnd_1337390 := by
    simpa [prefixWord, tailWord_1337390, baseEnd_1337390] using wordTrace_append hprefix tailTrace_1337390
  have hstable : (prefixWord ++ tailWord_1337390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337390).length < 2 ^ (prefixWord ++ tailWord_1337390).sum := by decide
  have hdescent : baseEnd_1337390 < baseStart_1337390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337416 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1337416 : Nat := 118140960795 + 1337416 * 2 ^ 59
def prefixEnd_1337416 : Nat := 4983230072969 + 3 ^ 40 * 1337416 * 2
def baseEnd_1337416 : Nat := 457824828675763058299561

theorem tailTrace_1337416 : CollatzResearch.WordTrace tailWord_1337416 prefixEnd_1337416 457824828675763058299561 := by
  unfold tailWord_1337416
  simp only [CollatzResearch.WordTrace]
  refine ⟨24389784461388859656532051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32519712615185146208709401 24389784461388859656532051)
  ·
    refine ⟨36584676692083289484798077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24389784461388859656532051 36584676692083289484798077)
    ·
      refine ⟨13719253759531233556799279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36584676692083289484798077 13719253759531233556799279)
      ·
        refine ⟨20578880639296850335198919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13719253759531233556799279 20578880639296850335198919)
        ·
          refine ⟨30868320958945275502798379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20578880639296850335198919 30868320958945275502798379)
          ·
            refine ⟨46302481438417913254197569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30868320958945275502798379 46302481438417913254197569)
            ·
              refine ⟨34726861078813434940648177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46302481438417913254197569 34726861078813434940648177)
              ·
                refine ⟨26045145809110076205486133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34726861078813434940648177 26045145809110076205486133)
                ·
                  refine ⟨2441732419604069644264325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26045145809110076205486133 2441732419604069644264325)
                  ·
                    refine ⟨457824828675763058299561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2441732419604069644264325 457824828675763058299561)
                    ·
                      rfl

theorem cell22_1337416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1337416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337416 prefixEnd_1337416 := by exact prefixLift 1337416
  have htrace : WordTrace (prefixWord ++ tailWord_1337416) baseStart_1337416 baseEnd_1337416 := by
    simpa [prefixWord, tailWord_1337416, baseEnd_1337416] using wordTrace_append hprefix tailTrace_1337416
  have hstable : (prefixWord ++ tailWord_1337416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337416).length < 2 ^ (prefixWord ++ tailWord_1337416).sum := by decide
  have hdescent : baseEnd_1337416 < baseStart_1337416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337431 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 6]
def baseStart_1337431 : Nat := 118140960795 + 1337431 * 2 ^ 59
def prefixEnd_1337431 : Nat := 4983230072969 + 3 ^ 40 * 1337431 * 2
def baseEnd_1337431 : Nat := 152609987827436006391505

theorem tailTrace_1337431 : CollatzResearch.WordTrace tailWord_1337431 prefixEnd_1337431 152609987827436006391505 := by
  unfold tailWord_1337431
  simp only [CollatzResearch.WordTrace]
  refine ⟨48780116017723376874860147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32520077345148917916573431 48780116017723376874860147)
  ·
    refine ⟨73170174026585065312290221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48780116017723376874860147 73170174026585065312290221)
    ·
      refine ⟨27438815259969399492108833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73170174026585065312290221 27438815259969399492108833)
      ·
        refine ⟨20579111444977049619081625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27438815259969399492108833 20579111444977049619081625)
        ·
          refine ⟨15434333583732787214311219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20579111444977049619081625 15434333583732787214311219)
          ·
            refine ⟨23151500375599180821466829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15434333583732787214311219 23151500375599180821466829)
            ·
              refine ⟨8681812640849692808050061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23151500375599180821466829 8681812640849692808050061)
              ·
                refine ⟨3255679740318634803018773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8681812640849692808050061 3255679740318634803018773)
                ·
                  refine ⟨152609987827436006391505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3255679740318634803018773 152609987827436006391505)
                  ·
                    rfl

theorem cell22_1337431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 6].length) (baseStart_1337431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337431 prefixEnd_1337431 := by exact prefixLift 1337431
  have htrace : WordTrace (prefixWord ++ tailWord_1337431) baseStart_1337431 baseEnd_1337431 := by
    simpa [prefixWord, tailWord_1337431, baseEnd_1337431] using wordTrace_append hprefix tailTrace_1337431
  have hstable : (prefixWord ++ tailWord_1337431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337431).length < 2 ^ (prefixWord ++ tailWord_1337431).sum := by decide
  have hdescent : baseEnd_1337431 < baseStart_1337431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337437 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 5]
def baseStart_1337437 : Nat := 118140960795 + 1337437 * 2 ^ 59
def prefixEnd_1337437 : Nat := 4983230072969 + 3 ^ 40 * 1337437 * 2
def baseEnd_1337437 : Nat := 152610672468308667841499

theorem tailTrace_1337437 : CollatzResearch.WordTrace tailWord_1337437 prefixEnd_1337437 152610672468308667841499 := by
  unfold tailWord_1337437
  simp only [CollatzResearch.WordTrace]
  refine ⟨48780334855701639899578565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32520223237134426599719043 48780334855701639899578565)
  ·
    refine ⟨9146312785444057481170981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48780334855701639899578565 9146312785444057481170981)
    ·
      refine ⟨1714933647270760777719559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9146312785444057481170981 1714933647270760777719559)
      ·
        refine ⟨2572400470906141166579339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714933647270760777719559 2572400470906141166579339)
        ·
          refine ⟨3858600706359211749869009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572400470906141166579339 3858600706359211749869009)
          ·
            refine ⟨2893950529769408812401757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3858600706359211749869009 2893950529769408812401757)
            ·
              refine ⟨1085231448663528304650659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2893950529769408812401757 1085231448663528304650659)
              ·
                refine ⟨1627847172995292456975989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085231448663528304650659 1627847172995292456975989)
                ·
                  refine ⟨152610672468308667841499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1627847172995292456975989 152610672468308667841499)
                  ·
                    rfl

theorem cell22_1337437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_1337437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337437 prefixEnd_1337437 := by exact prefixLift 1337437
  have htrace : WordTrace (prefixWord ++ tailWord_1337437) baseStart_1337437 baseEnd_1337437 := by
    simpa [prefixWord, tailWord_1337437, baseEnd_1337437] using wordTrace_append hprefix tailTrace_1337437
  have hstable : (prefixWord ++ tailWord_1337437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337437).length < 2 ^ (prefixWord ++ tailWord_1337437).sum := by decide
  have hdescent : baseEnd_1337437 < baseStart_1337437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337463 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 4, 3]
def baseStart_1337463 : Nat := 118140960795 + 1337463 * 2 ^ 59
def prefixEnd_1337463 : Nat := 4983230072969 + 3 ^ 40 * 1337463 * 2
def baseEnd_1337463 : Nat := 457840917736270602374417

theorem tailTrace_1337463 : CollatzResearch.WordTrace tailWord_1337463 prefixEnd_1337463 457840917736270602374417 := by
  unfold tailWord_1337463
  simp only [CollatzResearch.WordTrace]
  refine ⟨48781283153607446340025043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32520855435738297560016695 48781283153607446340025043)
  ·
    refine ⟨73171924730411169510037565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48781283153607446340025043 73171924730411169510037565)
    ·
      refine ⟨27439471773904188566264087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73171924730411169510037565 27439471773904188566264087)
      ·
        refine ⟨41159207660856282849396131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27439471773904188566264087 41159207660856282849396131)
        ·
          refine ⟨61738811491284424274094197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41159207660856282849396131 61738811491284424274094197)
          ·
            refine ⟨5788013577307914775696331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61738811491284424274094197 5788013577307914775696331)
            ·
              refine ⟨8682020365961872163544497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788013577307914775696331 8682020365961872163544497)
              ·
                refine ⟨6511515274471404122658373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8682020365961872163544497 6511515274471404122658373)
                ·
                  refine ⟨1220909113963388272998445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6511515274471404122658373 1220909113963388272998445)
                  ·
                    refine ⟨457840917736270602374417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220909113963388272998445 457840917736270602374417)
                    ·
                      rfl

theorem cell22_1337463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_1337463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337463 prefixEnd_1337463 := by exact prefixLift 1337463
  have htrace : WordTrace (prefixWord ++ tailWord_1337463) baseStart_1337463 baseEnd_1337463 := by
    simpa [prefixWord, tailWord_1337463, baseEnd_1337463] using wordTrace_append hprefix tailTrace_1337463
  have hstable : (prefixWord ++ tailWord_1337463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337463).length < 2 ^ (prefixWord ++ tailWord_1337463).sum := by decide
  have hdescent : baseEnd_1337463 < baseStart_1337463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337465 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 4]
def baseStart_1337465 : Nat := 118140960795 + 1337465 * 2 ^ 59
def prefixEnd_1337465 : Nat := 4983230072969 + 3 ^ 40 * 1337465 * 2
def baseEnd_1337465 : Nat := 152613867459047754608137

theorem tailTrace_1337465 : CollatzResearch.WordTrace tailWord_1337465 prefixEnd_1337465 152613867459047754608137 := by
  unfold tailWord_1337465
  simp only [CollatzResearch.WordTrace]
  refine ⟨48781356099600200681597849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32520904066400133787731899 48781356099600200681597849)
  ·
    refine ⟨36586017074700150511198387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48781356099600200681597849 36586017074700150511198387)
    ·
      refine ⟨54879025612050225766797581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36586017074700150511198387 54879025612050225766797581)
      ·
        refine ⟨20579634604518834662549093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54879025612050225766797581 20579634604518834662549093)
        ·
          refine ⟨3858681488347281499227955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20579634604518834662549093 3858681488347281499227955)
          ·
            refine ⟨5788022232520922248841933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858681488347281499227955 5788022232520922248841933)
            ·
              refine ⟨2170508337195345843315725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5788022232520922248841933 2170508337195345843315725)
              ·
                refine ⟨813940626448254691243397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170508337195345843315725 813940626448254691243397)
                ·
                  refine ⟨152613867459047754608137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813940626448254691243397 152613867459047754608137)
                  ·
                    rfl

theorem cell22_1337465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_1337465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337465 prefixEnd_1337465 := by exact prefixLift 1337465
  have htrace : WordTrace (prefixWord ++ tailWord_1337465) baseStart_1337465 baseEnd_1337465 := by
    simpa [prefixWord, tailWord_1337465, baseEnd_1337465] using wordTrace_append hprefix tailTrace_1337465
  have hstable : (prefixWord ++ tailWord_1337465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337465).length < 2 ^ (prefixWord ++ tailWord_1337465).sum := by decide
  have hdescent : baseEnd_1337465 < baseStart_1337465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337480 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1337480 : Nat := 118140960795 + 1337480 * 2 ^ 59
def prefixEnd_1337480 : Nat := 4983230072969 + 3 ^ 40 * 1337480 * 2
def baseEnd_1337480 : Nat := 457846737183688224699365

theorem tailTrace_1337480 : CollatzResearch.WordTrace tailWord_1337480 prefixEnd_1337480 457846737183688224699365 := by
  unfold tailWord_1337480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24390951597272929121696947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32521268796363905495595929 24390951597272929121696947)
  ·
    refine ⟨36586427395909393682545421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24390951597272929121696947 36586427395909393682545421)
    ·
      refine ⟨13719910273466022630954533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36586427395909393682545421 13719910273466022630954533)
      ·
        refine ⟨2572483176274879243303975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13719910273466022630954533 2572483176274879243303975)
        ·
          refine ⟨3858724764412318864955963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572483176274879243303975 3858724764412318864955963)
          ·
            refine ⟨5788087146618478297433945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858724764412318864955963 5788087146618478297433945)
            ·
              refine ⟨4341065359963858723075459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5788087146618478297433945 4341065359963858723075459)
              ·
                refine ⟨6511598039945788084613189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341065359963858723075459 6511598039945788084613189)
                ·
                  refine ⟨1220924632489835265864973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6511598039945788084613189 1220924632489835265864973)
                  ·
                    refine ⟨457846737183688224699365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220924632489835265864973 457846737183688224699365)
                    ·
                      rfl

theorem cell22_1337480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1337480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337480 prefixEnd_1337480 := by exact prefixLift 1337480
  have htrace : WordTrace (prefixWord ++ tailWord_1337480) baseStart_1337480 baseEnd_1337480 := by
    simpa [prefixWord, tailWord_1337480, baseEnd_1337480] using wordTrace_append hprefix tailTrace_1337480
  have hstable : (prefixWord ++ tailWord_1337480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337480).length < 2 ^ (prefixWord ++ tailWord_1337480).sum := by decide
  have hdescent : baseEnd_1337480 < baseStart_1337480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337482 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_1337482 : Nat := 118140960795 + 1337482 * 2 ^ 59
def prefixEnd_1337482 : Nat := 4983230072969 + 3 ^ 40 * 1337482 * 2
def baseEnd_1337482 : Nat := 152615807274853628716453

theorem tailTrace_1337482 : CollatzResearch.WordTrace tailWord_1337482 prefixEnd_1337482 152615807274853628716453 := by
  unfold tailWord_1337482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12195494035134653146241675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32521317427025741723311133 12195494035134653146241675)
  ·
    refine ⟨18293241052701979719362513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12195494035134653146241675 18293241052701979719362513)
    ·
      refine ⟨13719930789526484789521885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18293241052701979719362513 13719930789526484789521885)
      ·
        refine ⟨5144974046072431796070707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13719930789526484789521885 5144974046072431796070707)
        ·
          refine ⟨7717461069108647694106061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144974046072431796070707 7717461069108647694106061)
          ·
            refine ⟨2894047900915742885289773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7717461069108647694106061 2894047900915742885289773)
            ·
              refine ⟨1085267962843403581983665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2894047900915742885289773 1085267962843403581983665)
              ·
                refine ⟨813950972132552686487749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085267962843403581983665 813950972132552686487749)
                ·
                  refine ⟨152615807274853628716453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813950972132552686487749 152615807274853628716453)
                  ·
                    rfl

theorem cell22_1337482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_1337482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337482 prefixEnd_1337482 := by exact prefixLift 1337482
  have htrace : WordTrace (prefixWord ++ tailWord_1337482) baseStart_1337482 baseEnd_1337482 := by
    simpa [prefixWord, tailWord_1337482, baseEnd_1337482] using wordTrace_append hprefix tailTrace_1337482
  have hstable : (prefixWord ++ tailWord_1337482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337482).length < 2 ^ (prefixWord ++ tailWord_1337482).sum := by decide
  have hdescent : baseEnd_1337482 < baseStart_1337482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337568 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_1337568 : Nat := 118140960795 + 1337568 * 2 ^ 59
def prefixEnd_1337568 : Nat := 4983230072969 + 3 ^ 40 * 1337568 * 2
def baseEnd_1337568 : Nat := 457876861382085328499095

theorem tailTrace_1337568 : CollatzResearch.WordTrace tailWord_1337568 prefixEnd_1337568 457876861382085328499095 := by
  unfold tailWord_1337568
  simp only [CollatzResearch.WordTrace]
  refine ⟨24392556409113524636298679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32523408545484699515064905 24392556409113524636298679)
  ·
    refine ⟨36588834613670286954448019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24392556409113524636298679 36588834613670286954448019)
    ·
      refine ⟨54883251920505430431672029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36588834613670286954448019 54883251920505430431672029)
      ·
        refine ⟨20581219470189536411877011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54883251920505430431672029 20581219470189536411877011)
        ·
          refine ⟨30871829205284304617815517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20581219470189536411877011 30871829205284304617815517)
          ·
            refine ⟨11576935951981614231680819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30871829205284304617815517 11576935951981614231680819)
            ·
              refine ⟨17365403927972421347521229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11576935951981614231680819 17365403927972421347521229)
              ·
                refine ⟨6512026472989658005320461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17365403927972421347521229 6512026472989658005320461)
                ·
                  refine ⟨2442009927371121751995173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6512026472989658005320461 2442009927371121751995173)
                  ·
                    refine ⟨457876861382085328499095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2442009927371121751995173 457876861382085328499095)
                    ·
                      rfl

theorem cell22_1337568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_1337568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337568 prefixEnd_1337568 := by exact prefixLift 1337568
  have htrace : WordTrace (prefixWord ++ tailWord_1337568) baseStart_1337568 baseEnd_1337568 := by
    simpa [prefixWord, tailWord_1337568, baseEnd_1337568] using wordTrace_append hprefix tailTrace_1337568
  have hstable : (prefixWord ++ tailWord_1337568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337568).length < 2 ^ (prefixWord ++ tailWord_1337568).sum := by decide
  have hdescent : baseEnd_1337568 < baseStart_1337568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337600 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 4]
def baseStart_1337600 : Nat := 118140960795 + 1337600 * 2 ^ 59
def prefixEnd_1337600 : Nat := 4983230072969 + 3 ^ 40 * 1337600 * 2
def baseEnd_1337600 : Nat := 152629271878682637232999

theorem tailTrace_1337600 : CollatzResearch.WordTrace tailWord_1337600 prefixEnd_1337600 152629271878682637232999 := by
  unfold tailWord_1337600
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393139977055559368881127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32524186636074079158508169 24393139977055559368881127)
  ·
    refine ⟨36589709965583339053321691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24393139977055559368881127 36589709965583339053321691)
    ·
      refine ⟨54884564948375008579982537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36589709965583339053321691 54884564948375008579982537)
      ·
        refine ⟨41163423711281256434986903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54884564948375008579982537 41163423711281256434986903)
        ·
          refine ⟨61745135566921884652480355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41163423711281256434986903 61745135566921884652480355)
          ·
            refine ⟨92617703350382826978720533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61745135566921884652480355 92617703350382826978720533)
            ·
              refine ⟨4341454844549195014627525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92617703350382826978720533 4341454844549195014627525)
              ·
                refine ⟨814022783352974065242661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4341454844549195014627525 814022783352974065242661)
                ·
                  refine ⟨152629271878682637232999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814022783352974065242661 152629271878682637232999)
                  ·
                    rfl

theorem cell22_1337600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_1337600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337600 prefixEnd_1337600 := by exact prefixLift 1337600
  have htrace : WordTrace (prefixWord ++ tailWord_1337600) baseStart_1337600 baseEnd_1337600 := by
    simpa [prefixWord, tailWord_1337600, baseEnd_1337600] using wordTrace_append hprefix tailTrace_1337600
  have hstable : (prefixWord ++ tailWord_1337600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337600).length < 2 ^ (prefixWord ++ tailWord_1337600).sum := by decide
  have hdescent : baseEnd_1337600 < baseStart_1337600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337615 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 2, 3]
def baseStart_1337615 : Nat := 118140960795 + 1337615 * 2 ^ 59
def prefixEnd_1337615 : Nat := 4983230072969 + 3 ^ 40 * 1337615 * 2
def baseEnd_1337615 : Nat := 457892950442592872573951

theorem tailTrace_1337615 : CollatzResearch.WordTrace tailWord_1337615 prefixEnd_1337615 457892950442592872573951 := by
  unfold tailWord_1337615
  simp only [CollatzResearch.WordTrace]
  refine ⟨48786827049056776299558299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32524551366037850866372199 48786827049056776299558299)
  ·
    refine ⟨73180240573585164449337449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48786827049056776299558299 73180240573585164449337449)
    ·
      refine ⟨54885180430188873337003087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73180240573585164449337449 54885180430188873337003087)
      ·
        refine ⟨82327770645283310005504631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54885180430188873337003087 82327770645283310005504631)
        ·
          refine ⟨123491655967924965008256947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82327770645283310005504631 123491655967924965008256947)
          ·
            refine ⟨185237483951887447512385421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123491655967924965008256947 185237483951887447512385421)
            ·
              refine ⟨69464056481957792817144533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185237483951887447512385421 69464056481957792817144533)
              ·
                refine ⟨1628063823795885769151825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69464056481957792817144533 1628063823795885769151825)
                ·
                  refine ⟨1221047867846914326863869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628063823795885769151825 1221047867846914326863869)
                  ·
                    refine ⟨457892950442592872573951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221047867846914326863869 457892950442592872573951)
                    ·
                      rfl

theorem cell22_1337615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_1337615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337615 prefixEnd_1337615 := by exact prefixLift 1337615
  have htrace : WordTrace (prefixWord ++ tailWord_1337615) baseStart_1337615 baseEnd_1337615 := by
    simpa [prefixWord, tailWord_1337615, baseEnd_1337615] using wordTrace_append hprefix tailTrace_1337615
  have hstable : (prefixWord ++ tailWord_1337615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337615).length < 2 ^ (prefixWord ++ tailWord_1337615).sum := by decide
  have hdescent : baseEnd_1337615 < baseStart_1337615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337634 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1337634 : Nat := 118140960795 + 1337634 * 2 ^ 59
def prefixEnd_1337634 : Nat := 4983230072969 + 3 ^ 40 * 1337634 * 2
def baseEnd_1337634 : Nat := 152633151510294385449631

theorem tailTrace_1337634 : CollatzResearch.WordTrace tailWord_1337634 prefixEnd_1337634 152633151510294385449631 := by
  unfold tailWord_1337634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12196880008996985636124989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32525013357325295029666637 12196880008996985636124989)
  ·
    refine ⟨4573830003373869613546871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12196880008996985636124989 4573830003373869613546871)
    ·
      refine ⟨6860745005060804420320307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4573830003373869613546871 6860745005060804420320307)
      ·
        refine ⟨10291117507591206630480461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860745005060804420320307 10291117507591206630480461)
        ·
          refine ⟨3859169065346702486430173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10291117507591206630480461 3859169065346702486430173)
          ·
            refine ⟨1447188399505013432411315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3859169065346702486430173 1447188399505013432411315)
            ·
              refine ⟨2170782599257520148616973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447188399505013432411315 2170782599257520148616973)
              ·
                refine ⟨814043474721570055731365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170782599257520148616973 814043474721570055731365)
                ·
                  refine ⟨152633151510294385449631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814043474721570055731365 152633151510294385449631)
                  ·
                    rfl

theorem cell22_1337634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1337634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337634 prefixEnd_1337634 := by exact prefixLift 1337634
  have htrace : WordTrace (prefixWord ++ tailWord_1337634) baseStart_1337634 baseEnd_1337634 := by
    simpa [prefixWord, tailWord_1337634, baseEnd_1337634] using wordTrace_append hprefix tailTrace_1337634
  have hstable : (prefixWord ++ tailWord_1337634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337634).length < 2 ^ (prefixWord ++ tailWord_1337634).sum := by decide
  have hdescent : baseEnd_1337634 < baseStart_1337634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337688 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1337688 : Nat := 118140960795 + 1337688 * 2 ^ 59
def prefixEnd_1337688 : Nat := 4983230072969 + 3 ^ 40 * 1337688 * 2
def baseEnd_1337688 : Nat := 457917939834445015498727

theorem tailTrace_1337688 : CollatzResearch.WordTrace tailWord_1337688 prefixEnd_1337688 457917939834445015498727 := by
  unfold tailWord_1337688
  simp only [CollatzResearch.WordTrace]
  refine ⟨24394744788896154883482859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32526326385194873177977145 24394744788896154883482859)
  ·
    refine ⟨36592117183344232325224289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24394744788896154883482859 36592117183344232325224289)
    ·
      refine ⟨27444087887508174243918217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36592117183344232325224289 27444087887508174243918217)
      ·
        refine ⟨20583065915631130682938663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27444087887508174243918217 20583065915631130682938663)
        ·
          refine ⟨30874598873446696024407995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20583065915631130682938663 30874598873446696024407995)
          ·
            refine ⟨46311898310170044036611993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30874598873446696024407995 46311898310170044036611993)
            ·
              refine ⟨34733923732627533027458995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46311898310170044036611993 34733923732627533027458995)
              ·
                refine ⟨52100885598941299541188493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34733923732627533027458995 52100885598941299541188493)
                ·
                  refine ⟨19537832099602987327945685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52100885598941299541188493 19537832099602987327945685)
                  ·
                    refine ⟨457917939834445015498727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19537832099602987327945685 457917939834445015498727)
                    ·
                      rfl

theorem cell22_1337688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1337688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337688 prefixEnd_1337688 := by exact prefixLift 1337688
  have htrace : WordTrace (prefixWord ++ tailWord_1337688) baseStart_1337688 baseEnd_1337688 := by
    simpa [prefixWord, tailWord_1337688, baseEnd_1337688] using wordTrace_append hprefix tailTrace_1337688
  have hstable : (prefixWord ++ tailWord_1337688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337688).length < 2 ^ (prefixWord ++ tailWord_1337688).sum := by decide
  have hdescent : baseEnd_1337688 < baseStart_1337688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337735 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 6]
def baseStart_1337735 : Nat := 118140960795 + 1337735 * 2 ^ 59
def prefixEnd_1337735 : Nat := 4983230072969 + 3 ^ 40 * 1337735 * 2
def baseEnd_1337735 : Nat := 152644676298317519857861

theorem tailTrace_1337735 : CollatzResearch.WordTrace tailWord_1337735 prefixEnd_1337735 152644676298317519857861 := by
  unfold tailWord_1337735
  simp only [CollatzResearch.WordTrace]
  refine ⟨48791203808622036793926659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32527469205748024529284439 48791203808622036793926659)
  ·
    refine ⟨73186805712933055190889989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48791203808622036793926659 73186805712933055190889989)
    ·
      refine ⟨13722526071174947848291873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73186805712933055190889989 13722526071174947848291873)
      ·
        refine ⟨10291894553381210886218905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13722526071174947848291873 10291894553381210886218905)
        ·
          refine ⟨7718920915035908164664179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10291894553381210886218905 7718920915035908164664179)
          ·
            refine ⟨11578381372553862246996269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718920915035908164664179 11578381372553862246996269)
            ·
              refine ⟨4341893014707698342623601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11578381372553862246996269 4341893014707698342623601)
              ·
                refine ⟨3256419761030773756967701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4341893014707698342623601 3256419761030773756967701)
                ·
                  refine ⟨152644676298317519857861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3256419761030773756967701 152644676298317519857861)
                  ·
                    rfl

theorem cell22_1337735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 6].length) (baseStart_1337735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337735 prefixEnd_1337735 := by exact prefixLift 1337735
  have htrace : WordTrace (prefixWord ++ tailWord_1337735) baseStart_1337735 baseEnd_1337735 := by
    simpa [prefixWord, tailWord_1337735, baseEnd_1337735] using wordTrace_append hprefix tailTrace_1337735
  have hstable : (prefixWord ++ tailWord_1337735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337735).length < 2 ^ (prefixWord ++ tailWord_1337735).sum := by decide
  have hdescent : baseEnd_1337735 < baseStart_1337735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337754 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_1337754 : Nat := 118140960795 + 1337754 * 2 ^ 59
def prefixEnd_1337754 : Nat := 4983230072969 + 3 ^ 40 * 1337754 * 2
def baseEnd_1337754 : Nat := 457940532983242843348525

theorem tailTrace_1337754 : CollatzResearch.WordTrace tailWord_1337754 prefixEnd_1337754 457940532983242843348525 := by
  unfold tailWord_1337754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12197974198888300759717079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32527931197035468692578877 12197974198888300759717079)
  ·
    refine ⟨18296961298332451139575619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12197974198888300759717079 18296961298332451139575619)
    ·
      refine ⟨27445441947498676709363429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18296961298332451139575619 27445441947498676709363429)
      ·
        refine ⟨5146020365156001883005643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27445441947498676709363429 5146020365156001883005643)
        ·
          refine ⟨7719030547734002824508465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146020365156001883005643 7719030547734002824508465)
          ·
            refine ⟨5789272910800502118381349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7719030547734002824508465 5789272910800502118381349)
            ·
              refine ⟨1085488670775094147196503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5789272910800502118381349 1085488670775094147196503)
              ·
                refine ⟨1628233006162641220794755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085488670775094147196503 1628233006162641220794755)
                ·
                  refine ⟨2442349509243961831192133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628233006162641220794755 2442349509243961831192133)
                  ·
                    refine ⟨457940532983242843348525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2442349509243961831192133 457940532983242843348525)
                    ·
                      rfl

theorem cell22_1337754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_1337754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337754 prefixEnd_1337754 := by exact prefixLift 1337754
  have htrace : WordTrace (prefixWord ++ tailWord_1337754) baseStart_1337754 baseEnd_1337754 := by
    simpa [prefixWord, tailWord_1337754, baseEnd_1337754] using wordTrace_append hprefix tailTrace_1337754
  have hstable : (prefixWord ++ tailWord_1337754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337754).length < 2 ^ (prefixWord ++ tailWord_1337754).sum := by decide
  have hdescent : baseEnd_1337754 < baseStart_1337754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337765 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_1337765 : Nat := 118140960795 + 1337765 * 2 ^ 59
def prefixEnd_1337765 : Nat := 4983230072969 + 3 ^ 40 * 1337765 * 2
def baseEnd_1337765 : Nat := 457944298508042481323491

theorem tailTrace_1337765 : CollatzResearch.WordTrace tailWord_1337765 prefixEnd_1337765 457944298508042481323491 := by
  unfold tailWord_1337765
  simp only [CollatzResearch.WordTrace]
  refine ⟨48792297998513351917518749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32528198665675567945012499 48792297998513351917518749)
  ·
    refine ⟨18297111749442506969069531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48792297998513351917518749 18297111749442506969069531)
    ·
      refine ⟨27445667624163760453604297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18297111749442506969069531 27445667624163760453604297)
      ·
        refine ⟨20584250718122820340203223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27445667624163760453604297 20584250718122820340203223)
        ·
          refine ⟨30876376077184230510304835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20584250718122820340203223 30876376077184230510304835)
          ·
            refine ⟨46314564115776345765457253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30876376077184230510304835 46314564115776345765457253)
            ·
              refine ⟨8683980771708064831023235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46314564115776345765457253 8683980771708064831023235)
              ·
                refine ⟨13025971157562097246534853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8683980771708064831023235 13025971157562097246534853)
                ·
                  refine ⟨2442369592042893233725285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13025971157562097246534853 2442369592042893233725285)
                  ·
                    refine ⟨457944298508042481323491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2442369592042893233725285 457944298508042481323491)
                    ·
                      rfl

theorem cell22_1337765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_1337765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337765 prefixEnd_1337765 := by exact prefixLift 1337765
  have htrace : WordTrace (prefixWord ++ tailWord_1337765) baseStart_1337765 baseEnd_1337765 := by
    simpa [prefixWord, tailWord_1337765, baseEnd_1337765] using wordTrace_append hprefix tailTrace_1337765
  have hstable : (prefixWord ++ tailWord_1337765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337765).length < 2 ^ (prefixWord ++ tailWord_1337765).sum := by decide
  have hdescent : baseEnd_1337765 < baseStart_1337765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337825 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 7]
def baseStart_1337825 : Nat := 118140960795 + 1337825 * 2 ^ 59
def prefixEnd_1337825 : Nat := 4983230072969 + 3 ^ 40 * 1337825 * 2
def baseEnd_1337825 : Nat := 152654945911407441607769

theorem tailTrace_1337825 : CollatzResearch.WordTrace tailWord_1337825 prefixEnd_1337825 152654945911407441607769 := by
  unfold tailWord_1337825
  simp only [CollatzResearch.WordTrace]
  refine ⟨48794486378295982164702929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32529657585530654776468619 48794486378295982164702929)
  ·
    refine ⟨36595864783721986623527197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48794486378295982164702929 36595864783721986623527197)
    ·
      refine ⟨13723449293895744983822699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36595864783721986623527197 13723449293895744983822699)
      ·
        refine ⟨20585173940843617475734049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13723449293895744983822699 20585173940843617475734049)
        ·
          refine ⟨15438880455632713106800537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20585173940843617475734049 15438880455632713106800537)
          ·
            refine ⟨11579160341724534830100403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15438880455632713106800537 11579160341724534830100403)
            ·
              refine ⟨17368740512586802245150605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11579160341724534830100403 17368740512586802245150605)
              ·
                refine ⟨6513277692220050841931477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17368740512586802245150605 6513277692220050841931477)
                ·
                  refine ⟨152654945911407441607769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6513277692220050841931477 152654945911407441607769)
                  ·
                    rfl

theorem cell22_1337825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_1337825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337825 prefixEnd_1337825 := by exact prefixLift 1337825
  have htrace : WordTrace (prefixWord ++ tailWord_1337825) baseStart_1337825 baseEnd_1337825 := by
    simpa [prefixWord, tailWord_1337825, baseEnd_1337825] using wordTrace_append hprefix tailTrace_1337825
  have hstable : (prefixWord ++ tailWord_1337825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337825).length < 2 ^ (prefixWord ++ tailWord_1337825).sum := by decide
  have hdescent : baseEnd_1337825 < baseStart_1337825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337840 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_1337840 : Nat := 118140960795 + 1337840 * 2 ^ 59
def prefixEnd_1337840 : Nat := 4983230072969 + 3 ^ 40 * 1337840 * 2
def baseEnd_1337840 : Nat := 457969972540767285698261

theorem tailTrace_1337840 : CollatzResearch.WordTrace tailWord_1337840 prefixEnd_1337840 457969972540767285698261 := by
  unfold tailWord_1337840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24397516736620819863249487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32530022315494426484332649 24397516736620819863249487)
  ·
    refine ⟨36596275104931229794874231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24397516736620819863249487 36596275104931229794874231)
    ·
      refine ⟨54894412657396844692311347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36596275104931229794874231 54894412657396844692311347)
      ·
        refine ⟨82341618986095267038467021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54894412657396844692311347 82341618986095267038467021)
        ·
          refine ⟨30878107119785725139425133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82341618986095267038467021 30878107119785725139425133)
          ·
            refine ⟨11579290169919646927284425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30878107119785725139425133 11579290169919646927284425)
            ·
              refine ⟨8684467627439735195463319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11579290169919646927284425 8684467627439735195463319)
              ·
                refine ⟨13026701441159602793194979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8684467627439735195463319 13026701441159602793194979)
                ·
                  refine ⟨19540052161739404189792469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13026701441159602793194979 19540052161739404189792469)
                  ·
                    refine ⟨457969972540767285698261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19540052161739404189792469 457969972540767285698261)
                    ·
                      rfl

theorem cell22_1337840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_1337840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337840 prefixEnd_1337840 := by exact prefixLift 1337840
  have htrace : WordTrace (prefixWord ++ tailWord_1337840) baseStart_1337840 baseEnd_1337840 := by
    simpa [prefixWord, tailWord_1337840, baseEnd_1337840] using wordTrace_append hprefix tailTrace_1337840
  have hstable : (prefixWord ++ tailWord_1337840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337840).length < 2 ^ (prefixWord ++ tailWord_1337840).sum := by decide
  have hdescent : baseEnd_1337840 < baseStart_1337840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337876 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1337876 : Nat := 118140960795 + 1337876 * 2 ^ 59
def prefixEnd_1337876 : Nat := 4983230072969 + 3 ^ 40 * 1337876 * 2
def baseEnd_1337876 : Nat := 152660765358825063932717

theorem tailTrace_1337876 : CollatzResearch.WordTrace tailWord_1337876 prefixEnd_1337876 152660765358825063932717 := by
  unfold tailWord_1337876
  simp only [CollatzResearch.WordTrace]
  refine ⟨24398173250555608937404741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32530897667407478583206321 24398173250555608937404741)
  ·
    refine ⟨4574657484479176675763389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24398173250555608937404741 4574657484479176675763389)
    ·
      refine ⟨1715496556679691253411271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4574657484479176675763389 1715496556679691253411271)
      ·
        refine ⟨2573244835019536880116907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715496556679691253411271 2573244835019536880116907)
        ·
          refine ⟨3859867252529305320175361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573244835019536880116907 3859867252529305320175361)
          ·
            refine ⟨2894900439396978990131521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3859867252529305320175361 2894900439396978990131521)
            ·
              refine ⟨2171175329547734242598641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894900439396978990131521 2171175329547734242598641)
              ·
                refine ⟨1628381497160800681948981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171175329547734242598641 1628381497160800681948981)
                ·
                  refine ⟨152660765358825063932717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628381497160800681948981 152660765358825063932717)
                  ·
                    rfl

theorem cell22_1337876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1337876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337876 prefixEnd_1337876 := by exact prefixLift 1337876
  have htrace : WordTrace (prefixWord ++ tailWord_1337876) baseStart_1337876 baseEnd_1337876 := by
    simpa [prefixWord, tailWord_1337876, baseEnd_1337876] using wordTrace_append hprefix tailTrace_1337876
  have hstable : (prefixWord ++ tailWord_1337876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337876).length < 2 ^ (prefixWord ++ tailWord_1337876).sum := by decide
  have hdescent : baseEnd_1337876 < baseStart_1337876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337921 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 4]
def baseStart_1337921 : Nat := 118140960795 + 1337921 * 2 ^ 59
def prefixEnd_1337921 : Nat := 4983230072969 + 3 ^ 40 * 1337921 * 2
def baseEnd_1337921 : Nat := 152665900165370024807671

theorem tailTrace_1337921 : CollatzResearch.WordTrace tailWord_1337921 prefixEnd_1337921 152665900165370024807671 := by
  unfold tailWord_1337921
  simp only [CollatzResearch.WordTrace]
  refine ⟨48797987785948190560197617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32531991857298793706798411 48797987785948190560197617)
  ·
    refine ⟨36598490839461142920148213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48797987785948190560197617 36598490839461142920148213)
    ·
      refine ⟨3431108516199482148763895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36598490839461142920148213 3431108516199482148763895)
      ·
        refine ⟨5146662774299223223145843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431108516199482148763895 5146662774299223223145843)
        ·
          refine ⟨7719994161448834834718765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146662774299223223145843 7719994161448834834718765)
          ·
            refine ⟨2894997810543313063019537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7719994161448834834718765 2894997810543313063019537)
            ·
              refine ⟨2171248357907484797264653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894997810543313063019537 2171248357907484797264653)
              ·
                refine ⟨814218134215306798974245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2171248357907484797264653 814218134215306798974245)
                ·
                  refine ⟨152665900165370024807671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814218134215306798974245 152665900165370024807671)
                  ·
                    rfl

theorem cell22_1337921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_1337921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337921 prefixEnd_1337921 := by exact prefixLift 1337921
  have htrace : WordTrace (prefixWord ++ tailWord_1337921) baseStart_1337921 baseEnd_1337921 := by
    simpa [prefixWord, tailWord_1337921, baseEnd_1337921] using wordTrace_append hprefix tailTrace_1337921
  have hstable : (prefixWord ++ tailWord_1337921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337921).length < 2 ^ (prefixWord ++ tailWord_1337921).sum := by decide
  have hdescent : baseEnd_1337921 < baseStart_1337921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337964 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_1337964 : Nat := 118140960795 + 1337964 * 2 ^ 59
def prefixEnd_1337964 : Nat := 4983230072969 + 3 ^ 40 * 1337964 * 2
def baseEnd_1337964 : Nat := 458012420274872295597881

theorem tailTrace_1337964 : CollatzResearch.WordTrace tailWord_1337964 prefixEnd_1337964 458012420274872295597881 := by
  unfold tailWord_1337964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24399778062396204452006473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32533037416528272602675297 24399778062396204452006473)
  ·
    refine ⟨18299833546797153339004855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24399778062396204452006473 18299833546797153339004855)
    ·
      refine ⟨27449750320195730008507283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18299833546797153339004855 27449750320195730008507283)
      ·
        refine ⟨41174625480293595012760925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27449750320195730008507283 41174625480293595012760925)
        ·
          refine ⟨15440484555110098129785347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41174625480293595012760925 15440484555110098129785347)
          ·
            refine ⟨23160726832665147194678021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15440484555110098129785347 23160726832665147194678021)
            ·
              refine ⟨4342636281124715099002129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23160726832665147194678021 4342636281124715099002129)
              ·
                refine ⟨3256977210843536324251597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342636281124715099002129 3256977210843536324251597)
                ·
                  refine ⟨1221366454066326121594349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3256977210843536324251597 1221366454066326121594349)
                  ·
                    refine ⟨458012420274872295597881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221366454066326121594349 458012420274872295597881)
                    ·
                      rfl

theorem cell22_1337964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_1337964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337964 prefixEnd_1337964 := by exact prefixLift 1337964
  have htrace : WordTrace (prefixWord ++ tailWord_1337964) baseStart_1337964 baseEnd_1337964 := by
    simpa [prefixWord, tailWord_1337964, baseEnd_1337964] using wordTrace_append hprefix tailTrace_1337964
  have hstable : (prefixWord ++ tailWord_1337964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337964).length < 2 ^ (prefixWord ++ tailWord_1337964).sum := by decide
  have hdescent : baseEnd_1337964 < baseStart_1337964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337966 : List Nat := [4, 1, 2, 2, 2, 3, 2, 6]
def baseStart_1337966 : Nat := 118140960795 + 1337966 * 2 ^ 59
def prefixEnd_1337966 : Nat := 4983230072969 + 3 ^ 40 * 1337966 * 2
def baseEnd_1337966 : Nat := 50890344990638328560875

theorem tailTrace_1337966 : CollatzResearch.WordTrace tailWord_1337966 prefixEnd_1337966 50890344990638328560875 := by
  unfold tailWord_1337966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099953633848145405698219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32533086047190108830390501 6099953633848145405698219)
  ·
    refine ⟨9149930450772218108547329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6099953633848145405698219 9149930450772218108547329)
    ·
      refine ⟨6862447838079163581410497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9149930450772218108547329 6862447838079163581410497)
      ·
        refine ⟨5146835878559372686057873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862447838079163581410497 5146835878559372686057873)
        ·
          refine ⟨3860126908919529514543405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5146835878559372686057873 3860126908919529514543405)
          ·
            refine ⟨1447547590844823567953777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3860126908919529514543405 1447547590844823567953777)
            ·
              refine ⟨1085660693133617675965333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447547590844823567953777 1085660693133617675965333)
              ·
                refine ⟨50890344990638328560875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1085660693133617675965333 50890344990638328560875)
                ·
                  rfl

theorem cell22_1337966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_1337966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337966 prefixEnd_1337966 := by exact prefixLift 1337966
  have htrace : WordTrace (prefixWord ++ tailWord_1337966) baseStart_1337966 baseEnd_1337966 := by
    simpa [prefixWord, tailWord_1337966, baseEnd_1337966] using wordTrace_append hprefix tailTrace_1337966
  have hstable : (prefixWord ++ tailWord_1337966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337966).length < 2 ^ (prefixWord ++ tailWord_1337966).sum := by decide
  have hdescent : baseEnd_1337966 < baseStart_1337966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337977 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 7]
def baseStart_1337977 : Nat := 118140960795 + 1337977 * 2 ^ 59
def prefixEnd_1337977 : Nat := 4983230072969 + 3 ^ 40 * 1337977 * 2
def baseEnd_1337977 : Nat := 152672290146848198340947

theorem tailTrace_1337977 : CollatzResearch.WordTrace tailWord_1337977 prefixEnd_1337977 152672290146848198340947 := by
  unfold tailWord_1337977
  simp only [CollatzResearch.WordTrace]
  refine ⟨48800030273745312124236185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32533353515830208082824123 48800030273745312124236185)
  ·
    refine ⟨36600022705308984093177139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48800030273745312124236185 36600022705308984093177139)
    ·
      refine ⟨54900034057963476139765709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36600022705308984093177139 54900034057963476139765709)
      ·
        refine ⟨20587512771736303552412141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54900034057963476139765709 20587512771736303552412141)
        ·
          refine ⟨7720317289401113832154553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20587512771736303552412141 7720317289401113832154553)
          ·
            refine ⟨5790237967050835374115915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7720317289401113832154553 5790237967050835374115915)
            ·
              refine ⟨8685356950576253061173873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790237967050835374115915 8685356950576253061173873)
              ·
                refine ⟨6514017712932189795880405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8685356950576253061173873 6514017712932189795880405)
                ·
                  refine ⟨152672290146848198340947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6514017712932189795880405 152672290146848198340947)
                  ·
                    rfl

theorem cell22_1337977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_1337977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1337977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1337977 prefixEnd_1337977 := by exact prefixLift 1337977
  have htrace : WordTrace (prefixWord ++ tailWord_1337977) baseStart_1337977 baseEnd_1337977 := by
    simpa [prefixWord, tailWord_1337977, baseEnd_1337977] using wordTrace_append hprefix tailTrace_1337977
  have hstable : (prefixWord ++ tailWord_1337977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337977).length < 2 ^ (prefixWord ++ tailWord_1337977).sum := by decide
  have hdescent : baseEnd_1337977 < baseStart_1337977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338049 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1338049 : Nat := 118140960795 + 1338049 * 2 ^ 59
def prefixEnd_1338049 : Nat := 4983230072969 + 3 ^ 40 * 1338049 * 2
def baseEnd_1338049 : Nat := 458041517511960407222621

theorem tailTrace_1338049 : CollatzResearch.WordTrace tailWord_1338049 prefixEnd_1338049 458041517511960407222621 := by
  unfold tailWord_1338049
  simp only [CollatzResearch.WordTrace]
  refine ⟨48802656329484468420857201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32535104219656312280571467 48802656329484468420857201)
  ·
    refine ⟨36601992247113351315642901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48802656329484468420857201 36601992247113351315642901)
    ·
      refine ⟨1715718386583438342920761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36601992247113351315642901 1715718386583438342920761)
      ·
        refine ⟨1286788789937578757190571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715718386583438342920761 1286788789937578757190571)
        ·
          refine ⟨1930183184906368135785857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286788789937578757190571 1930183184906368135785857)
          ·
            refine ⟨1447637388679776101839393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930183184906368135785857 1447637388679776101839393)
            ·
              refine ⟨1085728041509832076379545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447637388679776101839393 1085728041509832076379545)
              ·
                refine ⟨814296031132374057284659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085728041509832076379545 814296031132374057284659)
                ·
                  refine ⟨1221444046698561085926989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814296031132374057284659 1221444046698561085926989)
                  ·
                    refine ⟨458041517511960407222621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221444046698561085926989 458041517511960407222621)
                    ·
                      rfl

theorem cell22_1338049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1338049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338049 prefixEnd_1338049 := by exact prefixLift 1338049
  have htrace : WordTrace (prefixWord ++ tailWord_1338049) baseStart_1338049 baseEnd_1338049 := by
    simpa [prefixWord, tailWord_1338049, baseEnd_1338049] using wordTrace_append hprefix tailTrace_1338049
  have hstable : (prefixWord ++ tailWord_1338049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338049).length < 2 ^ (prefixWord ++ tailWord_1338049).sum := by decide
  have hdescent : baseEnd_1338049 < baseStart_1338049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338056 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 4]
def baseStart_1338056 : Nat := 118140960795 + 1338056 * 2 ^ 59
def prefixEnd_1338056 : Nat := 4983230072969 + 3 ^ 40 * 1338056 * 2
def baseEnd_1338056 : Nat := 152681304585004907432533

theorem tailTrace_1338056 : CollatzResearch.WordTrace tailWord_1338056 prefixEnd_1338056 152681304585004907432533 := by
  unfold tailWord_1338056
  simp only [CollatzResearch.WordTrace]
  refine ⟨24401455820229554308181011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32535274426972739077574681 24401455820229554308181011)
  ·
    refine ⟨36602183730344331462271517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24401455820229554308181011 36602183730344331462271517)
    ·
      refine ⟨13725818898879124298351819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36602183730344331462271517 13725818898879124298351819)
      ·
        refine ⟨20588728348318686447527729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725818898879124298351819 20588728348318686447527729)
        ·
          refine ⟨15441546261239014835645797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20588728348318686447527729 15441546261239014835645797)
          ·
            refine ⟨2895289923982315281683587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15441546261239014835645797 2895289923982315281683587)
            ·
              refine ⟨4342934885973472922525381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895289923982315281683587 4342934885973472922525381)
              ·
                refine ⟨814300291120026172973509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4342934885973472922525381 814300291120026172973509)
                ·
                  refine ⟨152681304585004907432533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814300291120026172973509 152681304585004907432533)
                  ·
                    rfl

theorem cell22_1338056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_1338056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338056 prefixEnd_1338056 := by exact prefixLift 1338056
  have htrace : WordTrace (prefixWord ++ tailWord_1338056) baseStart_1338056 baseEnd_1338056 := by
    simpa [prefixWord, tailWord_1338056, baseEnd_1338056] using wordTrace_append hprefix tailTrace_1338056
  have hstable : (prefixWord ++ tailWord_1338056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338056).length < 2 ^ (prefixWord ++ tailWord_1338056).sum := by decide
  have hdescent : baseEnd_1338056 < baseStart_1338056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338071 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 2, 3]
def baseStart_1338071 : Nat := 118140960795 + 1338071 * 2 ^ 59
def prefixEnd_1338071 : Nat := 4983230072969 + 3 ^ 40 * 1338071 * 2
def baseEnd_1338071 : Nat := 458049048561559683172553

theorem tailTrace_1338071 : CollatzResearch.WordTrace tailWord_1338071 prefixEnd_1338071 458049048561559683172553 := by
  unfold tailWord_1338071
  simp only [CollatzResearch.WordTrace]
  refine ⟨48803458735404766178158067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32535639156936510785438711 48803458735404766178158067)
  ·
    refine ⟨73205188103107149267237101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48803458735404766178158067 73205188103107149267237101)
    ·
      refine ⟨27451945538665180975213913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73205188103107149267237101 27451945538665180975213913)
      ·
        refine ⟨20588959153998885731410435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27451945538665180975213913 20588959153998885731410435)
        ·
          refine ⟨30883438730998328597115653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20588959153998885731410435 30883438730998328597115653)
          ·
            refine ⟨5790644762062186611959185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30883438730998328597115653 5790644762062186611959185)
            ·
              refine ⟨4342983571546639958969389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5790644762062186611959185 4342983571546639958969389)
              ·
                refine ⟨1628618839329989984613521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4342983571546639958969389 1628618839329989984613521)
                ·
                  refine ⟨1221464129497492488460141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628618839329989984613521 1221464129497492488460141)
                  ·
                    refine ⟨458049048561559683172553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221464129497492488460141 458049048561559683172553)
                    ·
                      rfl

theorem cell22_1338071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_1338071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338071 prefixEnd_1338071 := by exact prefixLift 1338071
  have htrace : WordTrace (prefixWord ++ tailWord_1338071) baseStart_1338071 baseEnd_1338071 := by
    simpa [prefixWord, tailWord_1338071, baseEnd_1338071] using wordTrace_append hprefix tailTrace_1338071
  have hstable : (prefixWord ++ tailWord_1338071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338071).length < 2 ^ (prefixWord ++ tailWord_1338071).sum := by decide
  have hdescent : baseEnd_1338071 < baseStart_1338071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338099 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 7, 3]
def baseStart_1338099 : Nat := 118140960795 + 1338099 * 2 ^ 59
def prefixEnd_1338099 : Nat := 4983230072969 + 3 ^ 40 * 1338099 * 2
def baseEnd_1338099 : Nat := 458058633533776943472467

theorem tailTrace_1338099 : CollatzResearch.WordTrace tailWord_1338099 prefixEnd_1338099 458058633533776943472467 := by
  unfold tailWord_1338099
  simp only [CollatzResearch.WordTrace]
  refine ⟨48804479979303326960177351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32536319986202217973451567 48804479979303326960177351)
  ·
    refine ⟨73206719968954990440266027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48804479979303326960177351 73206719968954990440266027)
    ·
      refine ⟨109810079953432485660399041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73206719968954990440266027 109810079953432485660399041)
      ·
        refine ⟨82357559965074364245299281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109810079953432485660399041 82357559965074364245299281)
        ·
          refine ⟨61768169973805773183974461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82357559965074364245299281 61768169973805773183974461)
          ·
            refine ⟨23163063740177164943990423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61768169973805773183974461 23163063740177164943990423)
            ·
              refine ⟨34744595610265747415985635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23163063740177164943990423 34744595610265747415985635)
              ·
                refine ⟨52116893415398621123978453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34744595610265747415985635 52116893415398621123978453)
                ·
                  refine ⟨1221489689423405182593245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52116893415398621123978453 1221489689423405182593245)
                  ·
                    refine ⟨458058633533776943472467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221489689423405182593245 458058633533776943472467)
                    ·
                      rfl

theorem cell22_1338099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 3].length) (baseStart_1338099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338099 prefixEnd_1338099 := by exact prefixLift 1338099
  have htrace : WordTrace (prefixWord ++ tailWord_1338099) baseStart_1338099 baseEnd_1338099 := by
    simpa [prefixWord, tailWord_1338099, baseEnd_1338099] using wordTrace_append hprefix tailTrace_1338099
  have hstable : (prefixWord ++ tailWord_1338099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338099).length < 2 ^ (prefixWord ++ tailWord_1338099).sum := by decide
  have hdescent : baseEnd_1338099 < baseStart_1338099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338129 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 5]
def baseStart_1338129 : Nat := 118140960795 + 1338129 * 2 ^ 59
def prefixEnd_1338129 : Nat := 4983230072969 + 3 ^ 40 * 1338129 * 2
def baseEnd_1338129 : Nat := 152689634382288955074125

theorem tailTrace_1338129 : CollatzResearch.WordTrace tailWord_1338129 prefixEnd_1338129 152689634382288955074125 := by
  unfold tailWord_1338129
  simp only [CollatzResearch.WordTrace]
  refine ⟨48805574169194642083769441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32537049446129761389179627 48805574169194642083769441)
  ·
    refine ⟨36604180626895981562827081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48805574169194642083769441 36604180626895981562827081)
    ·
      refine ⟨27453135470171986172120311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36604180626895981562827081 27453135470171986172120311)
      ·
        refine ⟨41179703205257979258180467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27453135470171986172120311 41179703205257979258180467)
        ·
          refine ⟨61769554807886968887270701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41179703205257979258180467 61769554807886968887270701)
          ·
            refine ⟨23163583052957613332726513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61769554807886968887270701 23163583052957613332726513)
            ·
              refine ⟨17372687289718209999544885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23163583052957613332726513 17372687289718209999544885)
              ·
                refine ⟨1628689433411082187457333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17372687289718209999544885 1628689433411082187457333)
                ·
                  refine ⟨152689634382288955074125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628689433411082187457333 152689634382288955074125)
                  ·
                    rfl

theorem cell22_1338129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_1338129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338129 prefixEnd_1338129 := by exact prefixLift 1338129
  have htrace : WordTrace (prefixWord ++ tailWord_1338129) baseStart_1338129 baseEnd_1338129 := by
    simpa [prefixWord, tailWord_1338129, baseEnd_1338129] using wordTrace_append hprefix tailTrace_1338129
  have hstable : (prefixWord ++ tailWord_1338129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338129).length < 2 ^ (prefixWord ++ tailWord_1338129).sum := by decide
  have hdescent : baseEnd_1338129 < baseStart_1338129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338180 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1338180 : Nat := 118140960795 + 1338180 * 2 ^ 59
def prefixEnd_1338180 : Nat := 4983230072969 + 3 ^ 40 * 1338180 * 2
def baseEnd_1338180 : Nat := 152695453829706577399073

theorem tailTrace_1338180 : CollatzResearch.WordTrace tailWord_1338180 prefixEnd_1338180 152695453829706577399073 := by
  unfold tailWord_1338180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24403717146004938896937997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32538289528006585195917329 24403717146004938896937997)
  ·
    refine ⟨9151393929751852086351749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24403717146004938896937997 9151393929751852086351749)
    ·
      refine ⟨1715886361828472266190953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9151393929751852086351749 1715886361828472266190953)
      ·
        refine ⟨1286914771371354199643215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715886361828472266190953 1286914771371354199643215)
        ·
          refine ⟨1930372157057031299464823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286914771371354199643215 1930372157057031299464823)
          ·
            refine ⟨2895558235585546949197235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930372157057031299464823 2895558235585546949197235)
            ·
              refine ⟨4343337353378320423795853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895558235585546949197235 4343337353378320423795853)
              ·
                refine ⟨1628751507516870158923445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343337353378320423795853 1628751507516870158923445)
                ·
                  refine ⟨152695453829706577399073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628751507516870158923445 152695453829706577399073)
                  ·
                    rfl

theorem cell22_1338180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1338180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338180 prefixEnd_1338180 := by exact prefixLift 1338180
  have htrace : WordTrace (prefixWord ++ tailWord_1338180) baseStart_1338180 baseEnd_1338180 := by
    simpa [prefixWord, tailWord_1338180, baseEnd_1338180] using wordTrace_append hprefix tailTrace_1338180
  have hstable : (prefixWord ++ tailWord_1338180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338180).length < 2 ^ (prefixWord ++ tailWord_1338180).sum := by decide
  have hdescent : baseEnd_1338180 < baseStart_1338180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338225 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 4]
def baseStart_1338225 : Nat := 118140960795 + 1338225 * 2 ^ 59
def prefixEnd_1338225 : Nat := 4983230072969 + 3 ^ 40 * 1338225 * 2
def baseEnd_1338225 : Nat := 152700588636251538274027

theorem tailTrace_1338225 : CollatzResearch.WordTrace tailWord_1338225 prefixEnd_1338225 152700588636251538274027 := by
  unfold tailWord_1338225
  simp only [CollatzResearch.WordTrace]
  refine ⟨48809075576846850479264129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32539383717897900319509419 48809075576846850479264129)
  ·
    refine ⟨36606806682635137859448097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48809075576846850479264129 36606806682635137859448097)
    ·
      refine ⟨27455105011976353394586073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36606806682635137859448097 27455105011976353394586073)
      ·
        refine ⟨20591328758982265045939555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27455105011976353394586073 20591328758982265045939555)
        ·
          refine ⟨30886993138473397568909333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20591328758982265045939555 30886993138473397568909333)
          ·
            refine ⟨1447827803365940511042625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30886993138473397568909333 1447827803365940511042625)
            ·
              refine ⟨1085870852524455383281969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447827803365940511042625 1085870852524455383281969)
              ·
                refine ⟨814403139393341537461477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085870852524455383281969 814403139393341537461477)
                ·
                  refine ⟨152700588636251538274027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814403139393341537461477 152700588636251538274027)
                  ·
                    rfl

theorem cell22_1338225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_1338225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338225 prefixEnd_1338225 := by exact prefixLift 1338225
  have htrace : WordTrace (prefixWord ++ tailWord_1338225) baseStart_1338225 baseEnd_1338225 := by
    simpa [prefixWord, tailWord_1338225, baseEnd_1338225] using wordTrace_append hprefix tailTrace_1338225
  have hstable : (prefixWord ++ tailWord_1338225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338225).length < 2 ^ (prefixWord ++ tailWord_1338225).sum := by decide
  have hdescent : baseEnd_1338225 < baseStart_1338225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338234 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1338234 : Nat := 118140960795 + 1338234 * 2 ^ 59
def prefixEnd_1338234 : Nat := 4983230072969 + 3 ^ 40 * 1338234 * 2
def baseEnd_1338234 : Nat := 458104846792681591347053

theorem tailTrace_1338234 : CollatzResearch.WordTrace tailWord_1338234 prefixEnd_1338234 458104846792681591347053 := by
  unfold tailWord_1338234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202350958453561254085439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32539602555876163344227837 12202350958453561254085439)
  ·
    refine ⟨18303526437680341881128159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12202350958453561254085439 18303526437680341881128159)
    ·
      refine ⟨27455289656520512821692239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18303526437680341881128159 27455289656520512821692239)
      ·
        refine ⟨41182934484780769232538359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27455289656520512821692239 41182934484780769232538359)
        ·
          refine ⟨61774401727171153848807539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41182934484780769232538359 61774401727171153848807539)
          ·
            refine ⟨92661602590756730773211309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61774401727171153848807539 92661602590756730773211309)
            ·
              refine ⟨34748100971533774039954241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92661602590756730773211309 34748100971533774039954241)
              ·
                refine ⟨26061075728650330529965681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34748100971533774039954241 26061075728650330529965681)
                ·
                  refine ⟨19545806796487747897474261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26061075728650330529965681 19545806796487747897474261)
                  ·
                    refine ⟨458104846792681591347053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19545806796487747897474261 458104846792681591347053)
                    ·
                      rfl

theorem cell22_1338234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1338234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338234 prefixEnd_1338234 := by exact prefixLift 1338234
  have htrace : WordTrace (prefixWord ++ tailWord_1338234) baseStart_1338234 baseEnd_1338234 := by
    simpa [prefixWord, tailWord_1338234, baseEnd_1338234] using wordTrace_append hprefix tailTrace_1338234
  have hstable : (prefixWord ++ tailWord_1338234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338234).length < 2 ^ (prefixWord ++ tailWord_1338234).sum := by decide
  have hdescent : baseEnd_1338234 < baseStart_1338234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338251 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 5, 3]
def baseStart_1338251 : Nat := 118140960795 + 1338251 * 2 ^ 59
def prefixEnd_1338251 : Nat := 4983230072969 + 3 ^ 40 * 1338251 * 2
def baseEnd_1338251 : Nat := 458110666240099213672001

theorem tailTrace_1338251 : CollatzResearch.WordTrace tailWord_1338251 prefixEnd_1338251 458110666240099213672001 := by
  unfold tailWord_1338251
  simp only [CollatzResearch.WordTrace]
  refine ⟨48810023874752656919710607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32540015916501771279807071 48810023874752656919710607)
  ·
    refine ⟨73215035812128985379565911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48810023874752656919710607 73215035812128985379565911)
    ·
      refine ⟨109822553718193478069348867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73215035812128985379565911 109822553718193478069348867)
      ·
        refine ⟨164733830577290217104023301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109822553718193478069348867 164733830577290217104023301)
        ·
          refine ⟨30887593233241915707004369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164733830577290217104023301 30887593233241915707004369)
          ·
            refine ⟨23165694924931436780253277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30887593233241915707004369 23165694924931436780253277)
            ·
              refine ⟨8687135596849288792594979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23165694924931436780253277 8687135596849288792594979)
              ·
                refine ⟨13030703395273933188892469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8687135596849288792594979 13030703395273933188892469)
                ·
                  refine ⟨1221628443306931236458669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13030703395273933188892469 1221628443306931236458669)
                  ·
                    refine ⟨458110666240099213672001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221628443306931236458669 458110666240099213672001)
                    ·
                      rfl

theorem cell22_1338251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 3].length) (baseStart_1338251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338251 prefixEnd_1338251 := by exact prefixLift 1338251
  have htrace : WordTrace (prefixWord ++ tailWord_1338251) baseStart_1338251 baseEnd_1338251 := by
    simpa [prefixWord, tailWord_1338251, baseEnd_1338251] using wordTrace_append hprefix tailTrace_1338251
  have hstable : (prefixWord ++ tailWord_1338251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338251).length < 2 ^ (prefixWord ++ tailWord_1338251).sum := by decide
  have hdescent : baseEnd_1338251 < baseStart_1338251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338296 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1338296 : Nat := 118140960795 + 1338296 * 2 ^ 59
def prefixEnd_1338296 : Nat := 4983230072969 + 3 ^ 40 * 1338296 * 2
def baseEnd_1338296 : Nat := 458126070659734096296863

theorem tailTrace_1338296 : CollatzResearch.WordTrace tailWord_1338296 prefixEnd_1338296 458126070659734096296863 := by
  unfold tailWord_1338296
  simp only [CollatzResearch.WordTrace]
  refine ⟨24405832579794814802549371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32541110106393086403399161 24405832579794814802549371)
  ·
    refine ⟨36608748869692222203824057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24405832579794814802549371 36608748869692222203824057)
    ·
      refine ⟨27456561652269166652868043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36608748869692222203824057 27456561652269166652868043)
      ·
        refine ⟨41184842478403749979302065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27456561652269166652868043 41184842478403749979302065)
        ·
          refine ⟨30888631858802812484476549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41184842478403749979302065 30888631858802812484476549)
          ·
            refine ⟨5791618473525527340839353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30888631858802812484476549 5791618473525527340839353)
            ·
              refine ⟨4343713855144145505629515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5791618473525527340839353 4343713855144145505629515)
              ·
                refine ⟨6515570782716218258444273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343713855144145505629515 6515570782716218258444273)
                ·
                  refine ⟨4886678087037163693833205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6515570782716218258444273 4886678087037163693833205)
                  ·
                    refine ⟨458126070659734096296863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4886678087037163693833205 458126070659734096296863)
                    ·
                      rfl

theorem cell22_1338296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1338296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338296 prefixEnd_1338296 := by exact prefixLift 1338296
  have htrace : WordTrace (prefixWord ++ tailWord_1338296) baseStart_1338296 baseEnd_1338296 := by
    simpa [prefixWord, tailWord_1338296, baseEnd_1338296] using wordTrace_append hprefix tailTrace_1338296
  have hstable : (prefixWord ++ tailWord_1338296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338296).length < 2 ^ (prefixWord ++ tailWord_1338296).sum := by decide
  have hdescent : baseEnd_1338296 < baseStart_1338296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338298 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_1338298 : Nat := 118140960795 + 1338298 * 2 ^ 59
def prefixEnd_1338298 : Nat := 4983230072969 + 3 ^ 40 * 1338298 * 2
def baseEnd_1338298 : Nat := 152708918433535585915619

theorem tailTrace_1338298 : CollatzResearch.WordTrace tailWord_1338298 prefixEnd_1338298 152708918433535585915619 := by
  unfold tailWord_1338298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202934526395595986667887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32541158737054922631114365 12202934526395595986667887)
  ·
    refine ⟨18304401789593393980001831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12202934526395595986667887 18304401789593393980001831)
    ·
      refine ⟨27456602684390090970002747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18304401789593393980001831 27456602684390090970002747)
      ·
        refine ⟨41184904026585136455004121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27456602684390090970002747 41184904026585136455004121)
        ·
          refine ⟨30888678019938852341253091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41184904026585136455004121 30888678019938852341253091)
          ·
            refine ⟨46333017029908278511879637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30888678019938852341253091 46333017029908278511879637)
            ·
              refine ⟨1085930086638475277622179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46333017029908278511879637 1085930086638475277622179)
              ·
                refine ⟨1628895129957712916433269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085930086638475277622179 1628895129957712916433269)
                ·
                  refine ⟨152708918433535585915619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628895129957712916433269 152708918433535585915619)
                  ·
                    rfl

theorem cell22_1338298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_1338298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338298 prefixEnd_1338298 := by exact prefixLift 1338298
  have htrace : WordTrace (prefixWord ++ tailWord_1338298) baseStart_1338298 baseEnd_1338298 := by
    simpa [prefixWord, tailWord_1338298, baseEnd_1338298] using wordTrace_append hprefix tailTrace_1338298
  have hstable : (prefixWord ++ tailWord_1338298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338298).length < 2 ^ (prefixWord ++ tailWord_1338298).sum := by decide
  have hdescent : baseEnd_1338298 < baseStart_1338298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338311 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1338311 : Nat := 118140960795 + 1338311 * 2 ^ 59
def prefixEnd_1338311 : Nat := 4983230072969 + 3 ^ 40 * 1338311 * 2
def baseEnd_1338311 : Nat := 458131205466279057171817

theorem tailTrace_1338311 : CollatzResearch.WordTrace tailWord_1338311 prefixEnd_1338311 458131205466279057171817 := by
  unfold tailWord_1338311
  simp only [CollatzResearch.WordTrace]
  refine ⟨48812212254535287166894787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32541474836356858111263191 48812212254535287166894787)
  ·
    refine ⟨73218318381802930750342181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48812212254535287166894787 73218318381802930750342181)
    ·
      refine ⟨13728434696588049515689159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73218318381802930750342181 13728434696588049515689159)
      ·
        refine ⟨20592652044882074273533739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13728434696588049515689159 20592652044882074273533739)
        ·
          refine ⟨30888978067323111410300609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20592652044882074273533739 30888978067323111410300609)
          ·
            refine ⟨23166733550492333557725457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30888978067323111410300609 23166733550492333557725457)
            ·
              refine ⟨17375050162869250168294093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23166733550492333557725457 17375050162869250168294093)
              ·
                refine ⟨6515643811075968813110285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17375050162869250168294093 6515643811075968813110285)
                ·
                  refine ⟨2443366429153488304916357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6515643811075968813110285 2443366429153488304916357)
                  ·
                    refine ⟨458131205466279057171817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443366429153488304916357 458131205466279057171817)
                    ·
                      rfl

theorem cell22_1338311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1338311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338311 prefixEnd_1338311 := by exact prefixLift 1338311
  have htrace : WordTrace (prefixWord ++ tailWord_1338311) baseStart_1338311 baseEnd_1338311 := by
    simpa [prefixWord, tailWord_1338311, baseEnd_1338311] using wordTrace_append hprefix tailTrace_1338311
  have hstable : (prefixWord ++ tailWord_1338311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338311).length < 2 ^ (prefixWord ++ tailWord_1338311).sum := by decide
  have hdescent : baseEnd_1338311 < baseStart_1338311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338328 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_1338328 : Nat := 118140960795 + 1338328 * 2 ^ 59
def prefixEnd_1338328 : Nat := 4983230072969 + 3 ^ 40 * 1338328 * 2
def baseEnd_1338328 : Nat := 458137024913696679496765

theorem tailTrace_1338328 : CollatzResearch.WordTrace tailWord_1338328 prefixEnd_1338328 458137024913696679496765 := by
  unfold tailWord_1338328
  simp only [CollatzResearch.WordTrace]
  refine ⟨24406416147736849535131819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32541888196982466046842425 24406416147736849535131819)
  ·
    refine ⟨36609624221605274302697729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24406416147736849535131819 36609624221605274302697729)
    ·
      refine ⟨27457218166203955727023297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36609624221605274302697729 27457218166203955727023297)
      ·
        refine ⟨20592913624652966795267473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27457218166203955727023297 20592913624652966795267473)
        ·
          refine ⟨15444685218489725096450605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20592913624652966795267473 15444685218489725096450605)
          ·
            refine ⟨5791756956933646911168977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15444685218489725096450605 5791756956933646911168977)
            ·
              refine ⟨4343817717700235183376733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5791756956933646911168977 4343817717700235183376733)
              ·
                refine ⟨1628931644137588193766275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343817717700235183376733 1628931644137588193766275)
                ·
                  refine ⟨2443397466206382290649413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628931644137588193766275 2443397466206382290649413)
                  ·
                    refine ⟨458137024913696679496765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443397466206382290649413 458137024913696679496765)
                    ·
                      rfl

theorem cell22_1338328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_1338328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338328 prefixEnd_1338328 := by exact prefixLift 1338328
  have htrace : WordTrace (prefixWord ++ tailWord_1338328) baseStart_1338328 baseEnd_1338328 := by
    simpa [prefixWord, tailWord_1338328, baseEnd_1338328] using wordTrace_append hprefix tailTrace_1338328
  have hstable : (prefixWord ++ tailWord_1338328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338328).length < 2 ^ (prefixWord ++ tailWord_1338328).sum := by decide
  have hdescent : baseEnd_1338328 < baseStart_1338328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338343 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 6]
def baseStart_1338343 : Nat := 118140960795 + 1338343 * 2 ^ 59
def prefixEnd_1338343 : Nat := 4983230072969 + 3 ^ 40 * 1338343 * 2
def baseEnd_1338343 : Nat := 152714053240080546790573

theorem tailTrace_1338343 : CollatzResearch.WordTrace tailWord_1338343 prefixEnd_1338343 152714053240080546790573 := by
  unfold tailWord_1338343
  simp only [CollatzResearch.WordTrace]
  refine ⟨48813379390419356632059683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32542252926946237754706455 48813379390419356632059683)
  ·
    refine ⟨73220069085629034948089525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48813379390419356632059683 73220069085629034948089525)
    ·
      refine ⟨6864381476777722026383393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73220069085629034948089525 6864381476777722026383393)
      ·
        refine ⟨5148286107583291519787545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6864381476777722026383393 5148286107583291519787545)
        ·
          refine ⟨3861214580687468639840659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5148286107583291519787545 3861214580687468639840659)
          ·
            refine ⟨5791821871031202959760989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861214580687468639840659 5791821871031202959760989)
            ·
              refine ⟨2171933201636701109910371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5791821871031202959760989 2171933201636701109910371)
              ·
                refine ⟨3257899802455051664865557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171933201636701109910371 3257899802455051664865557)
                ·
                  refine ⟨152714053240080546790573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3257899802455051664865557 152714053240080546790573)
                  ·
                    rfl

theorem cell22_1338343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 6].length) (baseStart_1338343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338343 prefixEnd_1338343 := by exact prefixLift 1338343
  have htrace : WordTrace (prefixWord ++ tailWord_1338343) baseStart_1338343 baseEnd_1338343 := by
    simpa [prefixWord, tailWord_1338343, baseEnd_1338343] using wordTrace_append hprefix tailTrace_1338343
  have hstable : (prefixWord ++ tailWord_1338343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338343).length < 2 ^ (prefixWord ++ tailWord_1338343).sum := by decide
  have hdescent : baseEnd_1338343 < baseStart_1338343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338373 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1338373 : Nat := 118140960795 + 1338373 * 2 ^ 59
def prefixEnd_1338373 : Nat := 4983230072969 + 3 ^ 40 * 1338373 * 2
def baseEnd_1338373 : Nat := 458152429333331562121627

theorem tailTrace_1338373 : CollatzResearch.WordTrace tailWord_1338373 prefixEnd_1338373 458152429333331562121627 := by
  unfold tailWord_1338373
  simp only [CollatzResearch.WordTrace]
  refine ⟨48814473580310671755651773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32542982386873781170434515 48814473580310671755651773)
  ·
    refine ⟨18305427592616501908369415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48814473580310671755651773 18305427592616501908369415)
    ·
      refine ⟨27458141388924752862554123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18305427592616501908369415 27458141388924752862554123)
      ·
        refine ⟨41187212083387129293831185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27458141388924752862554123 41187212083387129293831185)
        ·
          refine ⟨30890409062540346970373389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41187212083387129293831185 30890409062540346970373389)
          ·
            refine ⟨11583903398452630113890021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30890409062540346970373389 11583903398452630113890021)
            ·
              refine ⟨2171981887209868146354379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11583903398452630113890021 2171981887209868146354379)
              ·
                refine ⟨3257972830814802219531569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171981887209868146354379 3257972830814802219531569)
                ·
                  refine ⟨2443479623111101664648677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257972830814802219531569 2443479623111101664648677)
                  ·
                    refine ⟨458152429333331562121627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443479623111101664648677 458152429333331562121627)
                    ·
                      rfl

theorem cell22_1338373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1338373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338373 prefixEnd_1338373 := by exact prefixLift 1338373
  have htrace : WordTrace (prefixWord ++ tailWord_1338373) baseStart_1338373 baseEnd_1338373 := by
    simpa [prefixWord, tailWord_1338373, baseEnd_1338373] using wordTrace_append hprefix tailTrace_1338373
  have hstable : (prefixWord ++ tailWord_1338373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338373).length < 2 ^ (prefixWord ++ tailWord_1338373).sum := by decide
  have hdescent : baseEnd_1338373 < baseStart_1338373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338431 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_1338431 : Nat := 118140960795 + 1338431 * 2 ^ 59
def prefixEnd_1338431 : Nat := 4983230072969 + 3 ^ 40 * 1338431 * 2
def baseEnd_1338431 : Nat := 458172283918638744171449

theorem tailTrace_1338431 : CollatzResearch.WordTrace tailWord_1338431 prefixEnd_1338431 458172283918638744171449 := by
  unfold tailWord_1338431
  simp only [CollatzResearch.WordTrace]
  refine ⟨48816589014100547661263147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32544392676067031774175431 48816589014100547661263147)
  ·
    refine ⟨73224883521150821491894721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48816589014100547661263147 73224883521150821491894721)
    ·
      refine ⟨54918662640863116118921041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73224883521150821491894721 54918662640863116118921041)
      ·
        refine ⟨41188996980647337089190781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54918662640863116118921041 41188996980647337089190781)
        ·
          refine ⟨15445873867742751408446543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41188996980647337089190781 15445873867742751408446543)
          ·
            refine ⟨23168810801614127112669815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15445873867742751408446543 23168810801614127112669815)
            ·
              refine ⟨34753216202421190669004723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23168810801614127112669815 34753216202421190669004723)
              ·
                refine ⟨52129824303631786003507085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34753216202421190669004723 52129824303631786003507085)
                ·
                  refine ⟨19548684113861919751315157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52129824303631786003507085 19548684113861919751315157)
                  ·
                    refine ⟨458172283918638744171449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19548684113861919751315157 458172283918638744171449)
                    ·
                      rfl

theorem cell22_1338431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_1338431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338431 prefixEnd_1338431 := by exact prefixLift 1338431
  have htrace : WordTrace (prefixWord ++ tailWord_1338431) baseStart_1338431 baseEnd_1338431 := by
    simpa [prefixWord, tailWord_1338431, baseEnd_1338431] using wordTrace_append hprefix tailTrace_1338431
  have hstable : (prefixWord ++ tailWord_1338431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338431).length < 2 ^ (prefixWord ++ tailWord_1338431).sum := by decide
  have hdescent : baseEnd_1338431 < baseStart_1338431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338450 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1338450 : Nat := 118140960795 + 1338450 * 2 ^ 59
def prefixEnd_1338450 : Nat := 4983230072969 + 3 ^ 40 * 1338450 * 2
def baseEnd_1338450 : Nat := 152726262668976342648797

theorem tailTrace_1338450 : CollatzResearch.WordTrace tailWord_1338450 prefixEnd_1338450 152726262668976342648797 := by
  unfold tailWord_1338450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204320500257928476551201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32544854667354475937469869 12204320500257928476551201)
  ·
    refine ⟨9153240375193446357413401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12204320500257928476551201 9153240375193446357413401)
    ·
      refine ⟨6864930281395084768060051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9153240375193446357413401 6864930281395084768060051)
      ·
        refine ⟨10297395422092627152090077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864930281395084768060051 10297395422092627152090077)
        ·
          refine ⟨3861523283284735182033779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10297395422092627152090077 3861523283284735182033779)
          ·
            refine ⟨5792284924927102773050669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861523283284735182033779 5792284924927102773050669)
            ·
              refine ⟨2172106846847663539894001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5792284924927102773050669 2172106846847663539894001)
              ·
                refine ⟨1629080135135747654920501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172106846847663539894001 1629080135135747654920501)
                ·
                  refine ⟨152726262668976342648797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1629080135135747654920501 152726262668976342648797)
                  ·
                    rfl

theorem cell22_1338450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1338450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338450 prefixEnd_1338450 := by exact prefixLift 1338450
  have htrace : WordTrace (prefixWord ++ tailWord_1338450) baseStart_1338450 baseEnd_1338450 := by
    simpa [prefixWord, tailWord_1338450, baseEnd_1338450] using wordTrace_append hprefix tailTrace_1338450
  have hstable : (prefixWord ++ tailWord_1338450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338450).length < 2 ^ (prefixWord ++ tailWord_1338450).sum := by decide
  have hdescent : baseEnd_1338450 < baseStart_1338450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338480 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_1338480 : Nat := 118140960795 + 1338480 * 2 ^ 59
def prefixEnd_1338480 : Nat := 4983230072969 + 3 ^ 40 * 1338480 * 2
def baseEnd_1338480 : Nat := 458189057620018949696299

theorem tailTrace_1338480 : CollatzResearch.WordTrace tailWord_1338480 prefixEnd_1338480 458189057620018949696299 := by
  unfold tailWord_1338480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409188095461514514898447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32545584127282019353197929 24409188095461514514898447)
  ·
    refine ⟨36613782143192271772347671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24409188095461514514898447 36613782143192271772347671)
    ·
      refine ⟨54920673214788407658521507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36613782143192271772347671 54920673214788407658521507)
      ·
        refine ⟨82381009822182611487782261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54920673214788407658521507 82381009822182611487782261)
        ·
          refine ⟨7723219670829619826979587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82381009822182611487782261 7723219670829619826979587)
          ·
            refine ⟨11584829506244429740469381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723219670829619826979587 11584829506244429740469381)
            ·
              refine ⟨2172155532420830576338009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11584829506244429740469381 2172155532420830576338009)
              ·
                refine ⟨1629116649315622932253507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172155532420830576338009 1629116649315622932253507)
                ·
                  refine ⟨2443674973973434398380261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629116649315622932253507 2443674973973434398380261)
                  ·
                    refine ⟨458189057620018949696299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443674973973434398380261 458189057620018949696299)
                    ·
                      rfl

theorem cell22_1338480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_1338480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338480 prefixEnd_1338480 := by exact prefixLift 1338480
  have htrace : WordTrace (prefixWord ++ tailWord_1338480) baseStart_1338480 baseEnd_1338480 := by
    simpa [prefixWord, tailWord_1338480, baseEnd_1338480] using wordTrace_append hprefix tailTrace_1338480
  have hstable : (prefixWord ++ tailWord_1338480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338480).length < 2 ^ (prefixWord ++ tailWord_1338480).sum := by decide
  have hdescent : baseEnd_1338480 < baseStart_1338480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338493 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1338493 : Nat := 118140960795 + 1338493 * 2 ^ 59
def prefixEnd_1338493 : Nat := 4983230072969 + 3 ^ 40 * 1338493 * 2
def baseEnd_1338493 : Nat := 458193507785691249121259

theorem tailTrace_1338493 : CollatzResearch.WordTrace tailWord_1338493 prefixEnd_1338493 458193507785691249121259 := by
  unfold tailWord_1338493
  simp only [CollatzResearch.WordTrace]
  refine ⟨48818850339875932250020133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32545900226583954833346755 48818850339875932250020133)
  ·
    refine ⟨9153534438726737296878775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48818850339875932250020133 9153534438726737296878775)
    ·
      refine ⟨13730301658090105945318163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9153534438726737296878775 13730301658090105945318163)
      ·
        refine ⟨20595452487135158917977245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13730301658090105945318163 20595452487135158917977245)
        ·
          refine ⟨7723294682675684594241467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20595452487135158917977245 7723294682675684594241467)
          ·
            refine ⟨11584942024013526891362201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723294682675684594241467 11584942024013526891362201)
            ·
              refine ⟨8688706518010145168521651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11584942024013526891362201 8688706518010145168521651)
              ·
                refine ⟨13033059777015217752782477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8688706518010145168521651 13033059777015217752782477)
                ·
                  refine ⟨4887397416380706657293429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13033059777015217752782477 4887397416380706657293429)
                  ·
                    refine ⟨458193507785691249121259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4887397416380706657293429 458193507785691249121259)
                    ·
                      rfl

theorem cell22_1338493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1338493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338493 prefixEnd_1338493 := by exact prefixLift 1338493
  have htrace : WordTrace (prefixWord ++ tailWord_1338493) baseStart_1338493 baseEnd_1338493 := by
    simpa [prefixWord, tailWord_1338493, baseEnd_1338493] using wordTrace_append hprefix tailTrace_1338493
  have hstable : (prefixWord ++ tailWord_1338493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338493).length < 2 ^ (prefixWord ++ tailWord_1338493).sum := by decide
  have hdescent : baseEnd_1338493 < baseStart_1338493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338568 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_1338568 : Nat := 118140960795 + 1338568 * 2 ^ 59
def prefixEnd_1338568 : Nat := 4983230072969 + 3 ^ 40 * 1338568 * 2
def baseEnd_1338568 : Nat := 152739727272805351165343

theorem tailTrace_1338568 : CollatzResearch.WordTrace tailWord_1338568 prefixEnd_1338568 152739727272805351165343 := by
  unfold tailWord_1338568
  simp only [CollatzResearch.WordTrace]
  refine ⟨24410792907302110029500179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32547723876402813372666905 24410792907302110029500179)
  ·
    refine ⟨36616189360953165044250269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24410792907302110029500179 36616189360953165044250269)
    ·
      refine ⟨13731071010357436891593851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36616189360953165044250269 13731071010357436891593851)
      ·
        refine ⟨20596606515536155337390777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731071010357436891593851 20596606515536155337390777)
        ·
          refine ⟨15447454886652116503043083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20596606515536155337390777 15447454886652116503043083)
          ·
            refine ⟨23171182329978174754564625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15447454886652116503043083 23171182329978174754564625)
            ·
              refine ⟨17378386747483631065923469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23171182329978174754564625 17378386747483631065923469)
              ·
                refine ⟨6516895030306361649721301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17378386747483631065923469 6516895030306361649721301)
                ·
                  refine ⟨152739727272805351165343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6516895030306361649721301 152739727272805351165343)
                  ·
                    rfl

theorem cell22_1338568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_1338568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338568 prefixEnd_1338568 := by exact prefixLift 1338568
  have htrace : WordTrace (prefixWord ++ tailWord_1338568) baseStart_1338568 baseEnd_1338568 := by
    simpa [prefixWord, tailWord_1338568, baseEnd_1338568] using wordTrace_append hprefix tailTrace_1338568
  have hstable : (prefixWord ++ tailWord_1338568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338568).length < 2 ^ (prefixWord ++ tailWord_1338568).sum := by decide
  have hdescent : baseEnd_1338568 < baseStart_1338568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338583 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1338583 : Nat := 118140960795 + 1338583 * 2 ^ 59
def prefixEnd_1338583 : Nat := 4983230072969 + 3 ^ 40 * 1338583 * 2
def baseEnd_1338583 : Nat := 458224316624961014370983

theorem tailTrace_1338583 : CollatzResearch.WordTrace tailWord_1338583 prefixEnd_1338583 458224316624961014370983 := by
  unfold tailWord_1338583
  simp only [CollatzResearch.WordTrace]
  refine ⟨48822132909549877620796403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32548088606366585080530935 48822132909549877620796403)
  ·
    refine ⟨73233199364324816431194605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48822132909549877620796403 73233199364324816431194605)
    ·
      refine ⟨27462449761621806161697977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73233199364324816431194605 27462449761621806161697977)
      ·
        refine ⟨20596837321216354621273483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27462449761621806161697977 20596837321216354621273483)
        ·
          refine ⟨30895255981824531931910225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20596837321216354621273483 30895255981824531931910225)
          ·
            refine ⟨23171441986368398948932669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30895255981824531931910225 23171441986368398948932669)
            ·
              refine ⟨8689290744888149605849751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23171441986368398948932669 8689290744888149605849751)
              ·
                refine ⟨13033936117332224408774627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689290744888149605849751 13033936117332224408774627)
                ·
                  refine ⟨19550904175998336613161941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033936117332224408774627 19550904175998336613161941)
                  ·
                    refine ⟨458224316624961014370983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19550904175998336613161941 458224316624961014370983)
                    ·
                      rfl

theorem cell22_1338583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1338583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338583 prefixEnd_1338583 := by exact prefixLift 1338583
  have htrace : WordTrace (prefixWord ++ tailWord_1338583) baseStart_1338583 baseEnd_1338583 := by
    simpa [prefixWord, tailWord_1338583, baseEnd_1338583] using wordTrace_append hprefix tailTrace_1338583
  have hstable : (prefixWord ++ tailWord_1338583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338583).length < 2 ^ (prefixWord ++ tailWord_1338583).sum := by decide
  have hdescent : baseEnd_1338583 < baseStart_1338583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338589 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1338589 : Nat := 118140960795 + 1338589 * 2 ^ 59
def prefixEnd_1338589 : Nat := 4983230072969 + 3 ^ 40 * 1338589 * 2
def baseEnd_1338589 : Nat := 458226370547578998720965

theorem tailTrace_1338589 : CollatzResearch.WordTrace tailWord_1338589 prefixEnd_1338589 458226370547578998720965 := by
  unfold tailWord_1338589
  simp only [CollatzResearch.WordTrace]
  refine ⟨48822351747528140645514821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32548234498352093763676547 48822351747528140645514821)
  ·
    refine ⟨9154190952661526371034029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48822351747528140645514821 9154190952661526371034029)
    ·
      refine ⟨3432821607248072389137761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9154190952661526371034029 3432821607248072389137761)
      ·
        refine ⟨2574616205436054291853321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3432821607248072389137761 2574616205436054291853321)
        ·
          refine ⟨1930962154077040718889991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574616205436054291853321 1930962154077040718889991)
          ·
            refine ⟨2896443231115561078334987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930962154077040718889991 2896443231115561078334987)
            ·
              refine ⟨4344664846673341617502481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896443231115561078334987 4344664846673341617502481)
              ·
                refine ⟨3258498635005006213126861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344664846673341617502481 3258498635005006213126861)
                ·
                  refine ⟨1221936988126877329922573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3258498635005006213126861 1221936988126877329922573)
                  ·
                    refine ⟨458226370547578998720965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221936988126877329922573 458226370547578998720965)
                    ·
                      rfl

theorem cell22_1338589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1338589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338589 prefixEnd_1338589 := by exact prefixLift 1338589
  have htrace : WordTrace (prefixWord ++ tailWord_1338589) baseStart_1338589 baseEnd_1338589 := by
    simpa [prefixWord, tailWord_1338589, baseEnd_1338589] using wordTrace_append hprefix tailTrace_1338589
  have hstable : (prefixWord ++ tailWord_1338589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338589).length < 2 ^ (prefixWord ++ tailWord_1338589).sum := by decide
  have hdescent : baseEnd_1338589 < baseStart_1338589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338615 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 1, 4]
def baseStart_1338615 : Nat := 118140960795 + 1338615 * 2 ^ 59
def prefixEnd_1338615 : Nat := 4983230072969 + 3 ^ 40 * 1338615 * 2
def baseEnd_1338615 : Nat := 458235270878923597570885

theorem tailTrace_1338615 : CollatzResearch.WordTrace tailWord_1338615 prefixEnd_1338615 458235270878923597570885 := by
  unfold tailWord_1338615
  simp only [CollatzResearch.WordTrace]
  refine ⟨48823300045433947085961299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32548866696955964723974199 48823300045433947085961299)
  ·
    refine ⟨73234950068150920628941949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48823300045433947085961299 73234950068150920628941949)
    ·
      refine ⟨27463106275556595235853231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73234950068150920628941949 27463106275556595235853231)
      ·
        refine ⟨41194659413334892853779847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27463106275556595235853231 41194659413334892853779847)
        ·
          refine ⟨61791989120002339280669771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41194659413334892853779847 61791989120002339280669771)
          ·
            refine ⟨92687983680003508921004657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61791989120002339280669771 92687983680003508921004657)
            ·
              refine ⟨69515987760002631690753493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92687983680003508921004657 69515987760002631690753493)
              ·
                refine ⟨1629280963125061680252035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69515987760002631690753493 1629280963125061680252035)
                ·
                  refine ⟨2443921444687592520378053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629280963125061680252035 2443921444687592520378053)
                  ·
                    refine ⟨458235270878923597570885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2443921444687592520378053 458235270878923597570885)
                    ·
                      rfl

theorem cell22_1338615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_1338615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338615 prefixEnd_1338615 := by exact prefixLift 1338615
  have htrace : WordTrace (prefixWord ++ tailWord_1338615) baseStart_1338615 baseEnd_1338615 := by
    simpa [prefixWord, tailWord_1338615, baseEnd_1338615] using wordTrace_append hprefix tailTrace_1338615
  have hstable : (prefixWord ++ tailWord_1338615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338615).length < 2 ^ (prefixWord ++ tailWord_1338615).sum := by decide
  have hdescent : baseEnd_1338615 < baseStart_1338615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338660 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1338660 : Nat := 118140960795 + 1338660 * 2 ^ 59
def prefixEnd_1338660 : Nat := 4983230072969 + 3 ^ 40 * 1338660 * 2
def baseEnd_1338660 : Nat := 458250675298558480195747

theorem tailTrace_1338660 : CollatzResearch.WordTrace tailWord_1338660 prefixEnd_1338660 458250675298558480195747 := by
  unfold tailWord_1338660
  simp only [CollatzResearch.WordTrace]
  refine ⟨24412470665135459885674717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32549960886847279847566289 24412470665135459885674717)
  ·
    refine ⟨9154676499425797457128019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24412470665135459885674717 9154676499425797457128019)
    ·
      refine ⟨13732014749138696185692029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9154676499425797457128019 13732014749138696185692029)
      ·
        refine ⟨5149505530927011069634511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13732014749138696185692029 5149505530927011069634511)
        ·
          refine ⟨7724258296390516604451767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149505530927011069634511 7724258296390516604451767)
          ·
            refine ⟨11586387444585774906677651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724258296390516604451767 11586387444585774906677651)
            ·
              refine ⟨17379581166878662360016477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11586387444585774906677651 17379581166878662360016477)
              ·
                refine ⟨6517342937579498385006179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17379581166878662360016477 6517342937579498385006179)
                ·
                  refine ⟨9776014406369247577509269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6517342937579498385006179 9776014406369247577509269)
                  ·
                    refine ⟨458250675298558480195747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9776014406369247577509269 458250675298558480195747)
                    ·
                      rfl

theorem cell22_1338660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1338660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338660 prefixEnd_1338660 := by exact prefixLift 1338660
  have htrace : WordTrace (prefixWord ++ tailWord_1338660) baseStart_1338660 baseEnd_1338660 := by
    simpa [prefixWord, tailWord_1338660, baseEnd_1338660] using wordTrace_append hprefix tailTrace_1338660
  have hstable : (prefixWord ++ tailWord_1338660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338660).length < 2 ^ (prefixWord ++ tailWord_1338660).sum := by decide
  have hdescent : baseEnd_1338660 < baseStart_1338660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338664 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 4]
def baseStart_1338664 : Nat := 118140960795 + 1338664 * 2 ^ 59
def prefixEnd_1338664 : Nat := 4983230072969 + 3 ^ 40 * 1338664 * 2
def baseEnd_1338664 : Nat := 152750681526767934365245

theorem tailTrace_1338664 : CollatzResearch.WordTrace tailWord_1338664 prefixEnd_1338664 152750681526767934365245 := by
  unfold tailWord_1338664
  simp only [CollatzResearch.WordTrace]
  refine ⟨24412543611128214227247523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32550058148170952302996697 24412543611128214227247523)
  ·
    refine ⟨36618815416692321340871285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24412543611128214227247523 36618815416692321340871285)
    ·
      refine ⟨3433013945314905125706683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36618815416692321340871285 3433013945314905125706683)
      ·
        refine ⟨5149520917972357688560025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433013945314905125706683 5149520917972357688560025)
        ·
          refine ⟨3862140688479268266420019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5149520917972357688560025 3862140688479268266420019)
          ·
            refine ⟨5793211032718902399630029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862140688479268266420019 5793211032718902399630029)
            ·
              refine ⟨2172454137269588399861261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5793211032718902399630029 2172454137269588399861261)
              ·
                refine ⟨814670301476095649947973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2172454137269588399861261 814670301476095649947973)
                ·
                  refine ⟨152750681526767934365245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814670301476095649947973 152750681526767934365245)
                  ·
                    rfl

theorem cell22_1338664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_1338664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338664 prefixEnd_1338664 := by exact prefixLift 1338664
  have htrace : WordTrace (prefixWord ++ tailWord_1338664) baseStart_1338664 baseEnd_1338664 := by
    simpa [prefixWord, tailWord_1338664, baseEnd_1338664] using wordTrace_append hprefix tailTrace_1338664
  have hstable : (prefixWord ++ tailWord_1338664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338664).length < 2 ^ (prefixWord ++ tailWord_1338664).sum := by decide
  have hdescent : baseEnd_1338664 < baseStart_1338664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338675 : List Nat := [1, 1, 1, 2, 5, 4, 8]
def baseStart_1338675 : Nat := 118140960795 + 1338675 * 2 ^ 59
def prefixEnd_1338675 : Nat := 4983230072969 + 3 ^ 40 * 1338675 * 2
def baseEnd_1338675 : Nat := 16972437411300127447063

theorem tailTrace_1338675 : CollatzResearch.WordTrace tailWord_1338675 prefixEnd_1338675 16972437411300127447063 := by
  unfold tailWord_1338675
  simp only [CollatzResearch.WordTrace]
  refine ⟨48825488425216577333145479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32550325616811051555430319 48825488425216577333145479)
  ·
    refine ⟨73238232637824865999718219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48825488425216577333145479 73238232637824865999718219)
    ·
      refine ⟨109857348956737298999577329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73238232637824865999718219 109857348956737298999577329)
      ·
        refine ⟨82393011717552974249682997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109857348956737298999577329 82393011717552974249682997)
        ·
          refine ⟨7724344848520591335907781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82393011717552974249682997 7724344848520591335907781)
          ·
            refine ⟨1448314659097610875482709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7724344848520591335907781 1448314659097610875482709)
            ·
              refine ⟨16972437411300127447063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1448314659097610875482709 16972437411300127447063)
              ·
                rfl

theorem cell22_1338675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 8].length) (baseStart_1338675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338675 prefixEnd_1338675 := by exact prefixLift 1338675
  have htrace : WordTrace (prefixWord ++ tailWord_1338675) baseStart_1338675 baseEnd_1338675 := by
    simpa [prefixWord, tailWord_1338675, baseEnd_1338675] using wordTrace_append hprefix tailTrace_1338675
  have hstable : (prefixWord ++ tailWord_1338675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338675).length < 2 ^ (prefixWord ++ tailWord_1338675).sum := by decide
  have hdescent : baseEnd_1338675 < baseStart_1338675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338677 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1338677 : Nat := 118140960795 + 1338677 * 2 ^ 59
def prefixEnd_1338677 : Nat := 4983230072969 + 3 ^ 40 * 1338677 * 2
def baseEnd_1338677 : Nat := 458256494745976102520695

theorem tailTrace_1338677 : CollatzResearch.WordTrace tailWord_1338677 prefixEnd_1338677 458256494745976102520695 := by
  unfold tailWord_1338677
  simp only [CollatzResearch.WordTrace]
  refine ⟨48825561371209331674718285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32550374247472887783145523 48825561371209331674718285)
  ·
    refine ⟨18309585514203499378019357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48825561371209331674718285 18309585514203499378019357)
    ·
      refine ⟨6866094567826312266757259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18309585514203499378019357 6866094567826312266757259)
      ·
        refine ⟨10299141851739468400135889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6866094567826312266757259 10299141851739468400135889)
        ·
          refine ⟨7724356388804601300101917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10299141851739468400135889 7724356388804601300101917)
          ·
            refine ⟨2896633645801725487538219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7724356388804601300101917 2896633645801725487538219)
            ·
              refine ⟨4344950468702588231307329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896633645801725487538219 4344950468702588231307329)
              ·
                refine ⟨3258712851526941173480497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344950468702588231307329 3258712851526941173480497)
                ·
                  refine ⟨2444034638645205880110373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258712851526941173480497 2444034638645205880110373)
                  ·
                    refine ⟨458256494745976102520695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444034638645205880110373 458256494745976102520695)
                    ·
                      rfl

theorem cell22_1338677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1338677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338677 prefixEnd_1338677 := by exact prefixLift 1338677
  have htrace : WordTrace (prefixWord ++ tailWord_1338677) baseStart_1338677 baseEnd_1338677 := by
    simpa [prefixWord, tailWord_1338677, baseEnd_1338677] using wordTrace_append hprefix tailTrace_1338677
  have hstable : (prefixWord ++ tailWord_1338677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338677).length < 2 ^ (prefixWord ++ tailWord_1338677).sum := by decide
  have hdescent : baseEnd_1338677 < baseStart_1338677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338681 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 4]
def baseStart_1338681 : Nat := 118140960795 + 1338681 * 2 ^ 59
def prefixEnd_1338681 : Nat := 4983230072969 + 3 ^ 40 * 1338681 * 2
def baseEnd_1338681 : Nat := 152752621342573808473561

theorem tailTrace_1338681 : CollatzResearch.WordTrace tailWord_1338681 prefixEnd_1338681 152752621342573808473561 := by
  unfold tailWord_1338681
  simp only [CollatzResearch.WordTrace]
  refine ⟨48825707263194840357863897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32550471508796560238575931 48825707263194840357863897)
  ·
    refine ⟨36619280447396130268397923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48825707263194840357863897 36619280447396130268397923)
    ·
      refine ⟨54928920671094195402596885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36619280447396130268397923 54928920671094195402596885)
      ·
        refine ⟨2574793156457540409496729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54928920671094195402596885 2574793156457540409496729)
        ·
          refine ⟨1931094867343155307122547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574793156457540409496729 1931094867343155307122547)
          ·
            refine ⟨2896642301014732960683821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931094867343155307122547 2896642301014732960683821)
            ·
              refine ⟨1086240862880524860256433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2896642301014732960683821 1086240862880524860256433)
              ·
                refine ⟨814680647160393645192325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086240862880524860256433 814680647160393645192325)
                ·
                  refine ⟨152752621342573808473561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814680647160393645192325 152752621342573808473561)
                  ·
                    rfl

theorem cell22_1338681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_1338681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338681 prefixEnd_1338681 := by exact prefixLift 1338681
  have htrace : WordTrace (prefixWord ++ tailWord_1338681) baseStart_1338681 baseEnd_1338681 := by
    simpa [prefixWord, tailWord_1338681, baseEnd_1338681] using wordTrace_append hprefix tailTrace_1338681
  have hstable : (prefixWord ++ tailWord_1338681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338681).length < 2 ^ (prefixWord ++ tailWord_1338681).sum := by decide
  have hdescent : baseEnd_1338681 < baseStart_1338681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338692 : List Nat := [2, 3, 4, 1, 1, 1, 1, 9]
def baseStart_1338692 : Nat := 118140960795 + 1338692 * 2 ^ 59
def prefixEnd_1338692 : Nat := 4983230072969 + 3 ^ 40 * 1338692 * 2
def baseEnd_1338692 : Nat := 50917958839169007043961

theorem tailTrace_1338692 : CollatzResearch.WordTrace tailWord_1338692 prefixEnd_1338692 50917958839169007043961 := by
  unfold tailWord_1338692
  simp only [CollatzResearch.WordTrace]
  refine ⟨24413054233077494618257165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32550738977436659491009553 24413054233077494618257165)
  ·
    refine ⟨9154895337404060481846437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24413054233077494618257165 9154895337404060481846437)
    ·
      refine ⟨1716542875763261340346207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9154895337404060481846437 1716542875763261340346207)
      ·
        refine ⟨2574814313644892010519311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716542875763261340346207 2574814313644892010519311)
        ·
          refine ⟨3862221470467338015778967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574814313644892010519311 3862221470467338015778967)
          ·
            refine ⟨5793332205701007023668451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862221470467338015778967 5793332205701007023668451)
            ·
              refine ⟨8689998308551510535502677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793332205701007023668451 8689998308551510535502677)
              ·
                refine ⟨50917958839169007043961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8689998308551510535502677 50917958839169007043961)
                ·
                  rfl

theorem cell22_1338692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_1338692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338692 prefixEnd_1338692 := by exact prefixLift 1338692
  have htrace : WordTrace (prefixWord ++ tailWord_1338692) baseStart_1338692 baseEnd_1338692 := by
    simpa [prefixWord, tailWord_1338692, baseEnd_1338692] using wordTrace_append hprefix tailTrace_1338692
  have hstable : (prefixWord ++ tailWord_1338692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338692).length < 2 ^ (prefixWord ++ tailWord_1338692).sum := by decide
  have hdescent : baseEnd_1338692 < baseStart_1338692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338735 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_1338735 : Nat := 118140960795 + 1338735 * 2 ^ 59
def prefixEnd_1338735 : Nat := 4983230072969 + 3 ^ 40 * 1338735 * 2
def baseEnd_1338735 : Nat := 458276349331283284570517

theorem tailTrace_1338735 : CollatzResearch.WordTrace tailWord_1338735 prefixEnd_1338735 458276349331283284570517 := by
  unfold tailWord_1338735
  simp only [CollatzResearch.WordTrace]
  refine ⟨48827676804999207580329659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32551784536666138386886439 48827676804999207580329659)
  ·
    refine ⟨73241515207498811370494489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48827676804999207580329659 73241515207498811370494489)
    ·
      refine ⟨54931136405624108527870867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73241515207498811370494489 54931136405624108527870867)
      ·
        refine ⟨82396704608436162791806301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54931136405624108527870867 82396704608436162791806301)
        ·
          refine ⟨30898764228163561046927363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82396704608436162791806301 30898764228163561046927363)
          ·
            refine ⟨46348146342245341570391045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30898764228163561046927363 46348146342245341570391045)
            ·
              refine ⟨8690277439171001544448321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46348146342245341570391045 8690277439171001544448321)
              ·
                refine ⟨6517708079378251158336241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8690277439171001544448321 6517708079378251158336241)
                ·
                  refine ⟨4888281059533688368752181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6517708079378251158336241 4888281059533688368752181)
                  ·
                    refine ⟨458276349331283284570517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4888281059533688368752181 458276349331283284570517)
                    ·
                      rfl

theorem cell22_1338735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_1338735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338735 prefixEnd_1338735 := by exact prefixLift 1338735
  have htrace : WordTrace (prefixWord ++ tailWord_1338735) baseStart_1338735 baseEnd_1338735 := by
    simpa [prefixWord, tailWord_1338735, baseEnd_1338735] using wordTrace_append hprefix tailTrace_1338735
  have hstable : (prefixWord ++ tailWord_1338735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338735).length < 2 ^ (prefixWord ++ tailWord_1338735).sum := by decide
  have hdescent : baseEnd_1338735 < baseStart_1338735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338825 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_1338825 : Nat := 118140960795 + 1338825 * 2 ^ 59
def prefixEnd_1338825 : Nat := 4983230072969 + 3 ^ 40 * 1338825 * 2
def baseEnd_1338825 : Nat := 458307158170553049820241

theorem tailTrace_1338825 : CollatzResearch.WordTrace tailWord_1338825 prefixEnd_1338825 458307158170553049820241 := by
  unfold tailWord_1338825
  simp only [CollatzResearch.WordTrace]
  refine ⟨48830959374673152951105929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32553972916448768634070619 48830959374673152951105929)
  ·
    refine ⟨36623219531004864713329447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48830959374673152951105929 36623219531004864713329447)
    ·
      refine ⟨54934829296507297069994171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36623219531004864713329447 54934829296507297069994171)
      ·
        refine ⟨82402243944760945604991257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54934829296507297069994171 82402243944760945604991257)
        ·
          refine ⟨61801682958570709203743443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82402243944760945604991257 61801682958570709203743443)
          ·
            refine ⟨92702524437856063805615165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61801682958570709203743443 92702524437856063805615165)
            ·
              refine ⟨34763446664196023927105687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92702524437856063805615165 34763446664196023927105687)
              ·
                refine ⟨52145169996294035890658531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34763446664196023927105687 52145169996294035890658531)
                ·
                  refine ⟨78217754994441053835987797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52145169996294035890658531 78217754994441053835987797)
                  ·
                    refine ⟨458307158170553049820241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 78217754994441053835987797 458307158170553049820241)
                    ·
                      rfl

theorem cell22_1338825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_1338825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338825 prefixEnd_1338825 := by exact prefixLift 1338825
  have htrace : WordTrace (prefixWord ++ tailWord_1338825) baseStart_1338825 baseEnd_1338825 := by
    simpa [prefixWord, tailWord_1338825, baseEnd_1338825] using wordTrace_append hprefix tailTrace_1338825
  have hstable : (prefixWord ++ tailWord_1338825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338825).length < 2 ^ (prefixWord ++ tailWord_1338825).sum := by decide
  have hdescent : baseEnd_1338825 < baseStart_1338825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338827 : List Nat := [1, 1, 1, 1, 3, 3, 6, 6]
def baseStart_1338827 : Nat := 118140960795 + 1338827 * 2 ^ 59
def prefixEnd_1338827 : Nat := 4983230072969 + 3 ^ 40 * 1338827 * 2
def baseEnd_1338827 : Nat := 50923093645713967918915

theorem tailTrace_1338827 : CollatzResearch.WordTrace tailWord_1338827 prefixEnd_1338827 50923093645713967918915 := by
  unfold tailWord_1338827
  simp only [CollatzResearch.WordTrace]
  refine ⟨48831032320665907292678735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32554021547110604861785823 48831032320665907292678735)
  ·
    refine ⟨73246548480998860939018103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48831032320665907292678735 73246548480998860939018103)
    ·
      refine ⟨109869822721498291408527155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73246548480998860939018103 109869822721498291408527155)
      ·
        refine ⟨164804734082247437112790733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109869822721498291408527155 164804734082247437112790733)
        ·
          refine ⟨61801775280842788917296525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164804734082247437112790733 61801775280842788917296525)
          ·
            refine ⟨23175665730316045843986197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61801775280842788917296525 23175665730316045843986197)
            ·
              refine ⟨1086359331108564648936853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23175665730316045843986197 1086359331108564648936853)
              ·
                refine ⟨50923093645713967918915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1086359331108564648936853 50923093645713967918915)
                ·
                  rfl

theorem cell22_1338827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 6].length) (baseStart_1338827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338827 prefixEnd_1338827 := by exact prefixLift 1338827
  have htrace : WordTrace (prefixWord ++ tailWord_1338827) baseStart_1338827 baseEnd_1338827 := by
    simpa [prefixWord, tailWord_1338827, baseEnd_1338827] using wordTrace_append hprefix tailTrace_1338827
  have hstable : (prefixWord ++ tailWord_1338827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338827).length < 2 ^ (prefixWord ++ tailWord_1338827).sum := by decide
  have hdescent : baseEnd_1338827 < baseStart_1338827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338917 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 6]
def baseStart_1338917 : Nat := 118140960795 + 1338917 * 2 ^ 59
def prefixEnd_1338917 : Nat := 4983230072969 + 3 ^ 40 * 1338917 * 2
def baseEnd_1338917 : Nat := 152779550550231825506653

theorem tailTrace_1338917 : CollatzResearch.WordTrace tailWord_1338917 prefixEnd_1338917 152779550550231825506653 := by
  unfold tailWord_1338917
  simp only [CollatzResearch.WordTrace]
  refine ⟨48834314890339852663455005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32556209926893235108970003 48834314890339852663455005)
  ·
    refine ⟨18312868083877444748795627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48834314890339852663455005 18312868083877444748795627)
    ·
      refine ⟨27469302125816167123193441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18312868083877444748795627 27469302125816167123193441)
      ·
        refine ⟨20601976594362125342395081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27469302125816167123193441 20601976594362125342395081)
        ·
          refine ⟨15451482445771594006796311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20601976594362125342395081 15451482445771594006796311)
          ·
            refine ⟨23177223668657391010194467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15451482445771594006796311 23177223668657391010194467)
            ·
              refine ⟨34765835502986086515291701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23177223668657391010194467 34765835502986086515291701)
              ·
                refine ⟨3259297078404945610808597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34765835502986086515291701 3259297078404945610808597)
                ·
                  refine ⟨152779550550231825506653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3259297078404945610808597 152779550550231825506653)
                  ·
                    rfl

theorem cell22_1338917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_1338917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338917 prefixEnd_1338917 := by exact prefixLift 1338917
  have htrace : WordTrace (prefixWord ++ tailWord_1338917) baseStart_1338917 baseEnd_1338917 := by
    simpa [prefixWord, tailWord_1338917, baseEnd_1338917] using wordTrace_append hprefix tailTrace_1338917
  have hstable : (prefixWord ++ tailWord_1338917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338917).length < 2 ^ (prefixWord ++ tailWord_1338917).sum := by decide
  have hdescent : baseEnd_1338917 < baseStart_1338917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338949 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_1338949 : Nat := 118140960795 + 1338949 * 2 ^ 59
def prefixEnd_1338949 : Nat := 4983230072969 + 3 ^ 40 * 1338949 * 2
def baseEnd_1338949 : Nat := 458349605904658059719861

theorem tailTrace_1338949 : CollatzResearch.WordTrace tailWord_1338949 prefixEnd_1338949 458349605904658059719861 := by
  unfold tailWord_1338949
  simp only [CollatzResearch.WordTrace]
  refine ⟨48835482026223922128619901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32556988017482614752413267 48835482026223922128619901)
  ·
    refine ⟨18313305759833970798232463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48835482026223922128619901 18313305759833970798232463)
    ·
      refine ⟨27469958639750956197348695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18313305759833970798232463 27469958639750956197348695)
      ·
        refine ⟨41204937959626434296023043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27469958639750956197348695 41204937959626434296023043)
        ·
          refine ⟨61807406939439651444034565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41204937959626434296023043 61807406939439651444034565)
          ·
            refine ⟨11588888801144934645756481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61807406939439651444034565 11588888801144934645756481)
            ·
              refine ⟨8691666600858700984317361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11588888801144934645756481 8691666600858700984317361)
              ·
                refine ⟨6518749950644025738238021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8691666600858700984317361 6518749950644025738238021)
                ·
                  refine ⟨1222265615745754825919629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6518749950644025738238021 1222265615745754825919629)
                  ·
                    refine ⟨458349605904658059719861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222265615745754825919629 458349605904658059719861)
                    ·
                      rfl

theorem cell22_1338949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_1338949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338949 prefixEnd_1338949 := by exact prefixLift 1338949
  have htrace : WordTrace (prefixWord ++ tailWord_1338949) baseStart_1338949 baseEnd_1338949 := by
    simpa [prefixWord, tailWord_1338949, baseEnd_1338949] using wordTrace_append hprefix tailTrace_1338949
  have hstable : (prefixWord ++ tailWord_1338949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338949).length < 2 ^ (prefixWord ++ tailWord_1338949).sum := by decide
  have hdescent : baseEnd_1338949 < baseStart_1338949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338964 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1338964 : Nat := 118140960795 + 1338964 * 2 ^ 59
def prefixEnd_1338964 : Nat := 4983230072969 + 3 ^ 40 * 1338964 * 2
def baseEnd_1338964 : Nat := 458354740711203020594815

theorem tailTrace_1338964 : CollatzResearch.WordTrace tailWord_1338964 prefixEnd_1338964 458354740711203020594815 := by
  unfold tailWord_1338964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24418014560584789845207973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32557352747446386460277297 24418014560584789845207973)
  ·
    refine ⟨4578377730109648095976495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24418014560584789845207973 4578377730109648095976495)
    ·
      refine ⟨6867566595164472143964743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4578377730109648095976495 6867566595164472143964743)
      ·
        refine ⟨10301349892746708215947115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6867566595164472143964743 10301349892746708215947115)
        ·
          refine ⟨15452024839120062323920673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10301349892746708215947115 15452024839120062323920673)
          ·
            refine ⟨11589018629340046742940505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15452024839120062323920673 11589018629340046742940505)
            ·
              refine ⟨8691763972005035057205379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11589018629340046742940505 8691763972005035057205379)
              ·
                refine ⟨13037645958007552585808069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691763972005035057205379 13037645958007552585808069)
                ·
                  refine ⟨2444558617126416109839013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13037645958007552585808069 2444558617126416109839013)
                  ·
                    refine ⟨458354740711203020594815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444558617126416109839013 458354740711203020594815)
                    ·
                      rfl

theorem cell22_1338964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1338964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1338964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1338964 prefixEnd_1338964 := by exact prefixLift 1338964
  have htrace : WordTrace (prefixWord ++ tailWord_1338964) baseStart_1338964 baseEnd_1338964 := by
    simpa [prefixWord, tailWord_1338964, baseEnd_1338964] using wordTrace_append hprefix tailTrace_1338964
  have hstable : (prefixWord ++ tailWord_1338964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338964).length < 2 ^ (prefixWord ++ tailWord_1338964).sum := by decide
  have hdescent : baseEnd_1338964 < baseStart_1338964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339041 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 5]
def baseStart_1339041 : Nat := 118140960795 + 1339041 * 2 ^ 59
def prefixEnd_1339041 : Nat := 4983230072969 + 3 ^ 40 * 1339041 * 2
def baseEnd_1339041 : Nat := 152793699794933495473193

theorem tailTrace_1339041 : CollatzResearch.WordTrace tailWord_1339041 prefixEnd_1339041 152793699794933495473193 := by
  unfold tailWord_1339041
  simp only [CollatzResearch.WordTrace]
  refine ⟨48838837541890621840968977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32559225027927081227312651 48838837541890621840968977)
  ·
    refine ⟨36629128156417966380726733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48838837541890621840968977 36629128156417966380726733)
    ·
      refine ⟨13735923058656737392772525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36629128156417966380726733 13735923058656737392772525)
      ·
        refine ⟨5150971146996276522289697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13735923058656737392772525 5150971146996276522289697)
        ·
          refine ⟨3863228360247207391717273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5150971146996276522289697 3863228360247207391717273)
          ·
            refine ⟨2897421270185405543787955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3863228360247207391717273 2897421270185405543787955)
            ·
              refine ⟨4346131905278108315681933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897421270185405543787955 4346131905278108315681933)
              ·
                refine ⟨1629799464479290618380725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4346131905278108315681933 1629799464479290618380725)
                ·
                  refine ⟨152793699794933495473193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1629799464479290618380725 152793699794933495473193)
                  ·
                    rfl

theorem cell22_1339041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_1339041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339041 prefixEnd_1339041 := by exact prefixLift 1339041
  have htrace : WordTrace (prefixWord ++ tailWord_1339041) baseStart_1339041 baseEnd_1339041 := by
    simpa [prefixWord, tailWord_1339041, baseEnd_1339041] using wordTrace_append hprefix tailTrace_1339041
  have hstable : (prefixWord ++ tailWord_1339041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339041).length < 2 ^ (prefixWord ++ tailWord_1339041).sum := by decide
  have hdescent : baseEnd_1339041 < baseStart_1339041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339114 : List Nat := [3, 1, 3, 1, 1, 1, 2, 10]
def baseStart_1339114 : Nat := 118140960795 + 1339114 * 2 ^ 59
def prefixEnd_1339114 : Nat := 4983230072969 + 3 ^ 40 * 1339114 * 2
def baseEnd_1339114 : Nat := 50934009864072514371595

theorem tailTrace_1339114 : CollatzResearch.WordTrace tailWord_1339114 prefixEnd_1339114 50934009864072514371595 := by
  unfold tailWord_1339114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12210375017656538827094099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32561000047084103538917597 12210375017656538827094099)
  ·
    refine ⟨18315562526484808240641149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12210375017656538827094099 18315562526484808240641149)
    ·
      refine ⟨6868335947431803090240431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18315562526484808240641149 6868335947431803090240431)
      ·
        refine ⟨10302503921147704635360647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6868335947431803090240431 10302503921147704635360647)
        ·
          refine ⟨15453755881721556953040971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10302503921147704635360647 15453755881721556953040971)
          ·
            refine ⟨23180633822582335429561457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15453755881721556953040971 23180633822582335429561457)
            ·
              refine ⟨17385475366936751572171093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23180633822582335429561457 17385475366936751572171093)
              ·
                refine ⟨50934009864072514371595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17385475366936751572171093 50934009864072514371595)
                ·
                  rfl

theorem cell22_1339114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_1339114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339114 prefixEnd_1339114 := by exact prefixLift 1339114
  have htrace : WordTrace (prefixWord ++ tailWord_1339114) baseStart_1339114 baseEnd_1339114 := by
    simpa [prefixWord, tailWord_1339114, baseEnd_1339114] using wordTrace_append hprefix tailTrace_1339114
  have hstable : (prefixWord ++ tailWord_1339114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339114).length < 2 ^ (prefixWord ++ tailWord_1339114).sum := by decide
  have hdescent : baseEnd_1339114 < baseStart_1339114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339116 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1339116 : Nat := 118140960795 + 1339116 * 2 ^ 59
def prefixEnd_1339116 : Nat := 4983230072969 + 3 ^ 40 * 1339116 * 2
def baseEnd_1339116 : Nat := 458406773417525290794349

theorem tailTrace_1339116 : CollatzResearch.WordTrace tailWord_1339116 prefixEnd_1339116 458406773417525290794349 := by
  unfold tailWord_1339116
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420786508309454824974601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32561048677745939766632801 24420786508309454824974601)
  ·
    refine ⟨18315589881232091118730951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24420786508309454824974601 18315589881232091118730951)
    ·
      refine ⟨27473384821848136678096427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18315589881232091118730951 27473384821848136678096427)
      ·
        refine ⟨41210077232772205017144641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27473384821848136678096427 41210077232772205017144641)
        ·
          refine ⟨30907557924579153762858481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41210077232772205017144641 30907557924579153762858481)
          ·
            refine ⟨23180668443434365322143861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30907557924579153762858481 23180668443434365322143861)
            ·
              refine ⟨2173187666571971748950987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23180668443434365322143861 2173187666571971748950987)
              ·
                refine ⟨3259781499857957623426481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173187666571971748950987 3259781499857957623426481)
                ·
                  refine ⟨2444836124893468217569861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3259781499857957623426481 2444836124893468217569861)
                  ·
                    refine ⟨458406773417525290794349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444836124893468217569861 458406773417525290794349)
                    ·
                      rfl

theorem cell22_1339116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1339116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339116 prefixEnd_1339116 := by exact prefixLift 1339116
  have htrace : WordTrace (prefixWord ++ tailWord_1339116) baseStart_1339116 baseEnd_1339116 := by
    simpa [prefixWord, tailWord_1339116, baseEnd_1339116] using wordTrace_append hprefix tailTrace_1339116
  have hstable : (prefixWord ++ tailWord_1339116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339116).length < 2 ^ (prefixWord ++ tailWord_1339116).sum := by decide
  have hdescent : baseEnd_1339116 < baseStart_1339116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339176 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_1339176 : Nat := 118140960795 + 1339176 * 2 ^ 59
def prefixEnd_1339176 : Nat := 4983230072969 + 3 ^ 40 * 1339176 * 2
def baseEnd_1339176 : Nat := 152809104214568378098055

theorem tailTrace_1339176 : CollatzResearch.WordTrace tailWord_1339176 prefixEnd_1339176 152809104214568378098055 := by
  unfold tailWord_1339176
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421880698200769948566691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32562507597601026598088921 24421880698200769948566691)
  ·
    refine ⟨36632821047301154922850037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24421880698200769948566691 36632821047301154922850037)
    ·
      refine ⟨3434326973184483274017191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36632821047301154922850037 3434326973184483274017191)
      ·
        refine ⟨5151490459776724911025787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3434326973184483274017191 5151490459776724911025787)
        ·
          refine ⟨7727235689665087366538681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151490459776724911025787 7727235689665087366538681)
          ·
            refine ⟨5795426767248815524904011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7727235689665087366538681 5795426767248815524904011)
            ·
              refine ⟨8693140150873223287356017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795426767248815524904011 8693140150873223287356017)
              ·
                refine ⟨6519855113154917465517013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8693140150873223287356017 6519855113154917465517013)
                ·
                  refine ⟨152809104214568378098055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6519855113154917465517013 152809104214568378098055)
                  ·
                    rfl

theorem cell22_1339176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_1339176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339176 prefixEnd_1339176 := by exact prefixLift 1339176
  have htrace : WordTrace (prefixWord ++ tailWord_1339176) baseStart_1339176 baseEnd_1339176 := by
    simpa [prefixWord, tailWord_1339176, baseEnd_1339176] using wordTrace_append hprefix tailTrace_1339176
  have hstable : (prefixWord ++ tailWord_1339176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339176).length < 2 ^ (prefixWord ++ tailWord_1339176).sum := by decide
  have hdescent : baseEnd_1339176 < baseStart_1339176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339180 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_1339180 : Nat := 118140960795 + 1339180 * 2 ^ 59
def prefixEnd_1339180 : Nat := 4983230072969 + 3 ^ 40 * 1339180 * 2
def baseEnd_1339180 : Nat := 458428681925450457194153

theorem tailTrace_1339180 : CollatzResearch.WordTrace tailWord_1339180 prefixEnd_1339180 458428681925450457194153 := by
  unfold tailWord_1339180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421953644193524290139497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32562604858924699053519329 24421953644193524290139497)
  ·
    refine ⟨18316465233145143217604623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24421953644193524290139497 18316465233145143217604623)
    ·
      refine ⟨27474697849717714826406935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18316465233145143217604623 27474697849717714826406935)
      ·
        refine ⟨41212046774576572239610403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27474697849717714826406935 41212046774576572239610403)
        ·
          refine ⟨61818070161864858359415605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41212046774576572239610403 61818070161864858359415605)
          ·
            refine ⟨5795444077674830471195213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61818070161864858359415605 5795444077674830471195213)
            ·
              refine ⟨2173291529128061426698205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5795444077674830471195213 2173291529128061426698205)
              ·
                refine ⟨814984323423023035011827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2173291529128061426698205 814984323423023035011827)
                ·
                  refine ⟨1222476485134534552517741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814984323423023035011827 1222476485134534552517741)
                  ·
                    refine ⟨458428681925450457194153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222476485134534552517741 458428681925450457194153)
                    ·
                      rfl

theorem cell22_1339180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_1339180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339180 prefixEnd_1339180 := by exact prefixLift 1339180
  have htrace : WordTrace (prefixWord ++ tailWord_1339180) baseStart_1339180 baseEnd_1339180 := by
    simpa [prefixWord, tailWord_1339180, baseEnd_1339180] using wordTrace_append hprefix tailTrace_1339180
  have hstable : (prefixWord ++ tailWord_1339180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339180).length < 2 ^ (prefixWord ++ tailWord_1339180).sum := by decide
  have hdescent : baseEnd_1339180 < baseStart_1339180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339223 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 3, 4]
def baseStart_1339223 : Nat := 118140960795 + 1339223 * 2 ^ 59
def prefixEnd_1339223 : Nat := 4983230072969 + 3 ^ 40 * 1339223 * 2
def baseEnd_1339223 : Nat := 458443401704212678369021

theorem tailTrace_1339223 : CollatzResearch.WordTrace tailWord_1339223 prefixEnd_1339223 458443401704212678369021 := by
  unfold tailWord_1339223
  simp only [CollatzResearch.WordTrace]
  refine ⟨48845475627231266924094323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32563650418154177949396215 48845475627231266924094323)
  ·
    refine ⟨73268213440846900386141485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48845475627231266924094323 73268213440846900386141485)
    ·
      refine ⟨27475580040317587644803057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73268213440846900386141485 27475580040317587644803057)
      ·
        refine ⟨20606685030238190733602293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27475580040317587644803057 20606685030238190733602293)
        ·
          refine ⟨1931876721584830381275215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20606685030238190733602293 1931876721584830381275215)
          ·
            refine ⟨2897815082377245571912823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931876721584830381275215 2897815082377245571912823)
            ·
              refine ⟨4346722623565868357869235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897815082377245571912823 4346722623565868357869235)
              ·
                refine ⟨6520083935348802536803853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346722623565868357869235 6520083935348802536803853)
                ·
                  refine ⟨2445031475755800951301445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6520083935348802536803853 2445031475755800951301445)
                  ·
                    refine ⟨458443401704212678369021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445031475755800951301445 458443401704212678369021)
                    ·
                      rfl

theorem cell22_1339223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_1339223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339223 prefixEnd_1339223 := by exact prefixLift 1339223
  have htrace : WordTrace (prefixWord ++ tailWord_1339223) baseStart_1339223 baseEnd_1339223 := by
    simpa [prefixWord, tailWord_1339223, baseEnd_1339223] using wordTrace_append hprefix tailTrace_1339223
  have hstable : (prefixWord ++ tailWord_1339223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339223).length < 2 ^ (prefixWord ++ tailWord_1339223).sum := by decide
  have hdescent : baseEnd_1339223 < baseStart_1339223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339240 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1339240 : Nat := 118140960795 + 1339240 * 2 ^ 59
def prefixEnd_1339240 : Nat := 4983230072969 + 3 ^ 40 * 1339240 * 2
def baseEnd_1339240 : Nat := 458449221151630300693969

theorem tailTrace_1339240 : CollatzResearch.WordTrace tailWord_1339240 prefixEnd_1339240 458449221151630300693969 := by
  unfold tailWord_1339240
  simp only [CollatzResearch.WordTrace]
  refine ⟨24423047834084839413731587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32564063778779785884975449 24423047834084839413731587)
  ·
    refine ⟨36634571751127259120597381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24423047834084839413731587 36634571751127259120597381)
    ·
      refine ⟨6868982203336361085112009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36634571751127259120597381 6868982203336361085112009)
      ·
        refine ⟨5151736652502270813834007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6868982203336361085112009 5151736652502270813834007)
        ·
          refine ⟨7727604978753406220751011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151736652502270813834007 7727604978753406220751011)
          ·
            refine ⟨11591407468130109331126517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727604978753406220751011 11591407468130109331126517)
            ·
              refine ⟨1086694450137197749793111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11591407468130109331126517 1086694450137197749793111)
              ·
                refine ⟨1630041675205796624689667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086694450137197749793111 1630041675205796624689667)
                ·
                  refine ⟨2445062512808694937034501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630041675205796624689667 2445062512808694937034501)
                  ·
                    refine ⟨458449221151630300693969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445062512808694937034501 458449221151630300693969)
                    ·
                      rfl

theorem cell22_1339240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1339240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339240 prefixEnd_1339240 := by exact prefixLift 1339240
  have htrace : WordTrace (prefixWord ++ tailWord_1339240) baseStart_1339240 baseEnd_1339240 := by
    simpa [prefixWord, tailWord_1339240, baseEnd_1339240] using wordTrace_append hprefix tailTrace_1339240
  have hstable : (prefixWord ++ tailWord_1339240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339240).length < 2 ^ (prefixWord ++ tailWord_1339240).sum := by decide
  have hdescent : baseEnd_1339240 < baseStart_1339240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339311 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 7]
def baseStart_1339311 : Nat := 118140960795 + 1339311 * 2 ^ 59
def prefixEnd_1339311 : Nat := 4983230072969 + 3 ^ 40 * 1339311 * 2
def baseEnd_1339311 : Nat := 152824508634203260722917

theorem tailTrace_1339311 : CollatzResearch.WordTrace tailWord_1339311 prefixEnd_1339311 152824508634203260722917 := by
  unfold tailWord_1339311
  simp only [CollatzResearch.WordTrace]
  refine ⟨48848685250912457953297787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32565790167274971968865191 48848685250912457953297787)
  ·
    refine ⟨73273027876368686929946681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48848685250912457953297787 73273027876368686929946681)
    ·
      refine ⟨54954770907276515197460011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73273027876368686929946681 54954770907276515197460011)
      ·
        refine ⟨82432156360914772796190017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54954770907276515197460011 82432156360914772796190017)
        ·
          refine ⟨61824117270686079597142513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82432156360914772796190017 61824117270686079597142513)
          ·
            refine ⟨46368087953014559697856885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61824117270686079597142513 46368087953014559697856885)
            ·
              refine ⟨4347008245595114971674083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46368087953014559697856885 4347008245595114971674083)
              ·
                refine ⟨6520512368392672457511125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347008245595114971674083 6520512368392672457511125)
                ·
                  refine ⟨152824508634203260722917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6520512368392672457511125 152824508634203260722917)
                  ·
                    rfl

theorem cell22_1339311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 7].length) (baseStart_1339311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339311 prefixEnd_1339311 := by exact prefixLift 1339311
  have htrace : WordTrace (prefixWord ++ tailWord_1339311) baseStart_1339311 baseEnd_1339311 := by
    simpa [prefixWord, tailWord_1339311, baseEnd_1339311] using wordTrace_append hprefix tailTrace_1339311
  have hstable : (prefixWord ++ tailWord_1339311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339311).length < 2 ^ (prefixWord ++ tailWord_1339311).sum := by decide
  have hdescent : baseEnd_1339311 < baseStart_1339311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339315 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 1, 3]
def baseStart_1339315 : Nat := 118140960795 + 1339315 * 2 ^ 59
def prefixEnd_1339315 : Nat := 4983230072969 + 3 ^ 40 * 1339315 * 2
def baseEnd_1339315 : Nat := 458474895184355105068739

theorem tailTrace_1339315 : CollatzResearch.WordTrace tailWord_1339315 prefixEnd_1339315 458474895184355105068739 := by
  unfold tailWord_1339315
  simp only [CollatzResearch.WordTrace]
  refine ⟨48848831142897966636443399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32565887428598644424295599 48848831142897966636443399)
  ·
    refine ⟨73273246714346949954665099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48848831142897966636443399 73273246714346949954665099)
    ·
      refine ⟨109909870071520424931997649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73273246714346949954665099 109909870071520424931997649)
      ·
        refine ⟨82432402553640318698998237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109909870071520424931997649 82432402553640318698998237)
        ·
          refine ⟨30912150957615119512124339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82432402553640318698998237 30912150957615119512124339)
          ·
            refine ⟨46368226436422679268186509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30912150957615119512124339 46368226436422679268186509)
            ·
              refine ⟨17388084913658504725569941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46368226436422679268186509 17388084913658504725569941)
              ·
                refine ⟨815066480327742409011091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17388084913658504725569941 815066480327742409011091)
                ·
                  refine ⟨1222599720491613613516637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815066480327742409011091 1222599720491613613516637)
                  ·
                    refine ⟨458474895184355105068739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222599720491613613516637 458474895184355105068739)
                    ·
                      rfl

theorem cell22_1339315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 3].length) (baseStart_1339315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339315 prefixEnd_1339315 := by exact prefixLift 1339315
  have htrace : WordTrace (prefixWord ++ tailWord_1339315) baseStart_1339315 baseEnd_1339315 := by
    simpa [prefixWord, tailWord_1339315, baseEnd_1339315] using wordTrace_append hprefix tailTrace_1339315
  have hstable : (prefixWord ++ tailWord_1339315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339315).length < 2 ^ (prefixWord ++ tailWord_1339315).sum := by decide
  have hdescent : baseEnd_1339315 < baseStart_1339315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339349 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_1339349 : Nat := 118140960795 + 1339349 * 2 ^ 59
def prefixEnd_1339349 : Nat := 4983230072969 + 3 ^ 40 * 1339349 * 2
def baseEnd_1339349 : Nat := 458486534079190349718635

theorem tailTrace_1339349 : CollatzResearch.WordTrace tailWord_1339349 prefixEnd_1339349 458486534079190349718635 := by
  unfold tailWord_1339349
  simp only [CollatzResearch.WordTrace]
  refine ⟨48850071224774790443181101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32566714149849860295454067 48850071224774790443181101)
  ·
    refine ⟨18318776709290546416192913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48850071224774790443181101 18318776709290546416192913)
    ·
      refine ⟨13739082531967909812144685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18318776709290546416192913 13739082531967909812144685)
      ·
        refine ⟨5152155949487966179554257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13739082531967909812144685 5152155949487966179554257)
        ·
          refine ⟨3864116962115974634665693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5152155949487966179554257 3864116962115974634665693)
          ·
            refine ⟨1449043860793490487999635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3864116962115974634665693 1449043860793490487999635)
            ·
              refine ⟨2173565791190235731999453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449043860793490487999635 2173565791190235731999453)
              ·
                refine ⟨815087171696338399499795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2173565791190235731999453 815087171696338399499795)
                ·
                  refine ⟨1222630757544507599249693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815087171696338399499795 1222630757544507599249693)
                  ·
                    refine ⟨458486534079190349718635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222630757544507599249693 458486534079190349718635)
                    ·
                      rfl

theorem cell22_1339349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_1339349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339349 prefixEnd_1339349 := by exact prefixLift 1339349
  have htrace : WordTrace (prefixWord ++ tailWord_1339349) baseStart_1339349 baseEnd_1339349 := by
    simpa [prefixWord, tailWord_1339349, baseEnd_1339349] using wordTrace_append hprefix tailTrace_1339349
  have hstable : (prefixWord ++ tailWord_1339349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339349).length < 2 ^ (prefixWord ++ tailWord_1339349).sum := by decide
  have hdescent : baseEnd_1339349 < baseStart_1339349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339388 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1339388 : Nat := 118140960795 + 1339388 * 2 ^ 59
def prefixEnd_1339388 : Nat := 4983230072969 + 3 ^ 40 * 1339388 * 2
def baseEnd_1339388 : Nat := 458499884576207247993515

theorem tailTrace_1339388 : CollatzResearch.WordTrace tailWord_1339388 prefixEnd_1339388 458499884576207247993515 := by
  unfold tailWord_1339388
  simp only [CollatzResearch.WordTrace]
  refine ⟨24425746835816750051925409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32567662447755666735900545 24425746835816750051925409)
  ·
    refine ⟨18319310126862562538944057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24425746835816750051925409 18319310126862562538944057)
    ·
      refine ⟨13739482595146921904208043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18319310126862562538944057 13739482595146921904208043)
      ·
        refine ⟨20609223892720382856312065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13739482595146921904208043 20609223892720382856312065)
        ·
          refine ⟨15456917919540287142234049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20609223892720382856312065 15456917919540287142234049)
          ·
            refine ⟨11592688439655215356675537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15456917919540287142234049 11592688439655215356675537)
            ·
              refine ⟨8694516329741411517506653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11592688439655215356675537 8694516329741411517506653)
              ·
                refine ⟨3260443623653029319064995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8694516329741411517506653 3260443623653029319064995)
                ·
                  refine ⟨4890665435479543978597493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260443623653029319064995 4890665435479543978597493)
                  ·
                    refine ⟨458499884576207247993515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4890665435479543978597493 458499884576207247993515)
                    ·
                      rfl

theorem cell22_1339388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1339388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339388 prefixEnd_1339388 := by exact prefixLift 1339388
  have htrace : WordTrace (prefixWord ++ tailWord_1339388) baseStart_1339388 baseEnd_1339388 := by
    simpa [prefixWord, tailWord_1339388, baseEnd_1339388] using wordTrace_append hprefix tailTrace_1339388
  have hstable : (prefixWord ++ tailWord_1339388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339388).length < 2 ^ (prefixWord ++ tailWord_1339388).sum := by decide
  have hdescent : baseEnd_1339388 < baseStart_1339388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339420 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1339420 : Nat := 118140960795 + 1339420 * 2 ^ 59
def prefixEnd_1339420 : Nat := 4983230072969 + 3 ^ 40 * 1339420 * 2
def baseEnd_1339420 : Nat := 458510838830169831193417

theorem tailTrace_1339420 : CollatzResearch.WordTrace tailWord_1339420 prefixEnd_1339420 458510838830169831193417 := by
  unfold tailWord_1339420
  simp only [CollatzResearch.WordTrace]
  refine ⟨24426330403758784784507857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32568440538345046379343809 24426330403758784784507857)
  ·
    refine ⟨18319747802819088588380893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24426330403758784784507857 18319747802819088588380893)
    ·
      refine ⟨6869905426057158220642835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18319747802819088588380893 6869905426057158220642835)
      ·
        refine ⟨10304858139085737330964253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869905426057158220642835 10304858139085737330964253)
        ·
          refine ⟨3864321802157151499111595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10304858139085737330964253 3864321802157151499111595)
          ·
            refine ⟨5796482703235727248667393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864321802157151499111595 5796482703235727248667393)
            ·
              refine ⟨4347362027426795436500545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5796482703235727248667393 4347362027426795436500545)
              ·
                refine ⟨3260521520570096577375409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347362027426795436500545 3260521520570096577375409)
                ·
                  refine ⟨2445391140427572433031557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260521520570096577375409 2445391140427572433031557)
                  ·
                    refine ⟨458510838830169831193417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445391140427572433031557 458510838830169831193417)
                    ·
                      rfl

theorem cell22_1339420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1339420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339420 prefixEnd_1339420 := by exact prefixLift 1339420
  have htrace : WordTrace (prefixWord ++ tailWord_1339420) baseStart_1339420 baseEnd_1339420 := by
    simpa [prefixWord, tailWord_1339420, baseEnd_1339420] using wordTrace_append hprefix tailTrace_1339420
  have hstable : (prefixWord ++ tailWord_1339420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339420).length < 2 ^ (prefixWord ++ tailWord_1339420).sum := by decide
  have hdescent : baseEnd_1339420 < baseStart_1339420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339454 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1339454 : Nat := 118140960795 + 1339454 * 2 ^ 59
def prefixEnd_1339454 : Nat := 4983230072969 + 3 ^ 40 * 1339454 * 2
def baseEnd_1339454 : Nat := 458522477725005075843313

theorem tailTrace_1339454 : CollatzResearch.WordTrace tailWord_1339454 prefixEnd_1339454 458522477725005075843313 := by
  unfold tailWord_1339454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6106737611174299171969177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32569267259596262250502277 6106737611174299171969177)
  ·
    refine ⟨4580053208380724378976883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6106737611174299171969177 4580053208380724378976883)
    ·
      refine ⟨6870079812571086568465325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580053208380724378976883 6870079812571086568465325)
      ·
        refine ⟨2576279929714157463174497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6870079812571086568465325 2576279929714157463174497)
        ·
          refine ⟨1932209947285618097380873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2576279929714157463174497 1932209947285618097380873)
          ·
            refine ⟨1449157460464213573035655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1932209947285618097380873 1449157460464213573035655)
            ·
              refine ⟨2173736190696320359553483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449157460464213573035655 2173736190696320359553483)
              ·
                refine ⟨3260604286044480539330225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173736190696320359553483 3260604286044480539330225)
                ·
                  refine ⟨2445453214533360404497669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260604286044480539330225 2445453214533360404497669)
                  ·
                    refine ⟨458522477725005075843313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445453214533360404497669 458522477725005075843313)
                    ·
                      rfl

theorem cell22_1339454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1339454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339454 prefixEnd_1339454 := by exact prefixLift 1339454
  have htrace : WordTrace (prefixWord ++ tailWord_1339454) baseStart_1339454 baseEnd_1339454 := by
    simpa [prefixWord, tailWord_1339454, baseEnd_1339454] using wordTrace_append hprefix tailTrace_1339454
  have hstable : (prefixWord ++ tailWord_1339454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339454).length < 2 ^ (prefixWord ++ tailWord_1339454).sum := by decide
  have hdescent : baseEnd_1339454 < baseStart_1339454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339463 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 7]
def baseStart_1339463 : Nat := 118140960795 + 1339463 * 2 ^ 59
def prefixEnd_1339463 : Nat := 4983230072969 + 3 ^ 40 * 1339463 * 2
def baseEnd_1339463 : Nat := 152841852869644017456095

theorem tailTrace_1339463 : CollatzResearch.WordTrace tailWord_1339463 prefixEnd_1339463 152841852869644017456095 := by
  unfold tailWord_1339463
  simp only [CollatzResearch.WordTrace]
  refine ⟨48854229146361787912831043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32569486097574525275220695 48854229146361787912831043)
  ·
    refine ⟨73281343719542681869246565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48854229146361787912831043 73281343719542681869246565)
    ·
      refine ⟨13740251947414252850483731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73281343719542681869246565 13740251947414252850483731)
      ·
        refine ⟨20610377921121379275725597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13740251947414252850483731 20610377921121379275725597)
        ·
          refine ⟨7728891720420517228397099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20610377921121379275725597 7728891720420517228397099)
          ·
            refine ⟨11593337580630775842595649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7728891720420517228397099 11593337580630775842595649)
            ·
              refine ⟨8695003185473081881946737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11593337580630775842595649 8695003185473081881946737)
              ·
                refine ⟨6521252389104811411460053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8695003185473081881946737 6521252389104811411460053)
                ·
                  refine ⟨152841852869644017456095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6521252389104811411460053 152841852869644017456095)
                  ·
                    rfl

theorem cell22_1339463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_1339463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339463 prefixEnd_1339463 := by exact prefixLift 1339463
  have htrace : WordTrace (prefixWord ++ tailWord_1339463) baseStart_1339463 baseEnd_1339463 := by
    simpa [prefixWord, tailWord_1339463, baseEnd_1339463] using wordTrace_append hprefix tailTrace_1339463
  have hstable : (prefixWord ++ tailWord_1339463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339463).length < 2 ^ (prefixWord ++ tailWord_1339463).sum := by decide
  have hdescent : baseEnd_1339463 < baseStart_1339463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339480 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_1339480 : Nat := 118140960795 + 1339480 * 2 ^ 59
def prefixEnd_1339480 : Nat := 4983230072969 + 3 ^ 40 * 1339480 * 2
def baseEnd_1339480 : Nat := 152843792685449891564411

theorem tailTrace_1339480 : CollatzResearch.WordTrace tailWord_1339480 prefixEnd_1339480 152843792685449891564411 := by
  unfold tailWord_1339480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24427424593650099908099947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32569899458200133210799929 24427424593650099908099947)
  ·
    refine ⟨36641136890475149862149921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24427424593650099908099947 36641136890475149862149921)
    ·
      refine ⟨27480852667856362396612441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36641136890475149862149921 27480852667856362396612441)
      ·
        refine ⟨20610639500892271797459331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27480852667856362396612441 20610639500892271797459331)
        ·
          refine ⟨30915959251338407696188997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20610639500892271797459331 30915959251338407696188997)
          ·
            refine ⟨5796742359625951443035437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30915959251338407696188997 5796742359625951443035437)
            ·
              refine ⟨2173778384859731791138289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5796742359625951443035437 2173778384859731791138289)
              ·
                refine ⟨1630333788644798843353717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173778384859731791138289 1630333788644798843353717)
                ·
                  refine ⟨152843792685449891564411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1630333788644798843353717 152843792685449891564411)
                  ·
                    rfl

theorem cell22_1339480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_1339480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339480 prefixEnd_1339480 := by exact prefixLift 1339480
  have htrace : WordTrace (prefixWord ++ tailWord_1339480) baseStart_1339480 baseEnd_1339480 := by
    simpa [prefixWord, tailWord_1339480, baseEnd_1339480] using wordTrace_append hprefix tailTrace_1339480
  have hstable : (prefixWord ++ tailWord_1339480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339480).length < 2 ^ (prefixWord ++ tailWord_1339480).sum := by decide
  have hdescent : baseEnd_1339480 < baseStart_1339480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339484 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1339484 : Nat := 118140960795 + 1339484 * 2 ^ 59
def prefixEnd_1339484 : Nat := 4983230072969 + 3 ^ 40 * 1339484 * 2
def baseEnd_1339484 : Nat := 458532747338094997593221

theorem tailTrace_1339484 : CollatzResearch.WordTrace tailWord_1339484 prefixEnd_1339484 458532747338094997593221 := by
  unfold tailWord_1339484
  simp only [CollatzResearch.WordTrace]
  refine ⟨24427497539642854249672753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32569996719523805666230337 24427497539642854249672753)
  ·
    refine ⟨18320623154732140687254565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24427497539642854249672753 18320623154732140687254565)
    ·
      refine ⟨3435116841512276378860231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18320623154732140687254565 3435116841512276378860231)
      ·
        refine ⟨5152675262268414568290347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435116841512276378860231 5152675262268414568290347)
        ·
          refine ⟨7729012893402621852435521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152675262268414568290347 7729012893402621852435521)
          ·
            refine ⟨5796759670051966389326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7729012893402621852435521 5796759670051966389326641)
            ·
              refine ⟨4347569752538974791994981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5796759670051966389326641 4347569752538974791994981)
              ·
                refine ⟨815169328601057773499059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4347569752538974791994981 815169328601057773499059)
                ·
                  refine ⟨1222753992901586660248589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815169328601057773499059 1222753992901586660248589)
                  ·
                    refine ⟨458532747338094997593221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222753992901586660248589 458532747338094997593221)
                    ·
                      rfl

theorem cell22_1339484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1339484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339484 prefixEnd_1339484 := by exact prefixLift 1339484
  have htrace : WordTrace (prefixWord ++ tailWord_1339484) baseStart_1339484 baseEnd_1339484 := by
    simpa [prefixWord, tailWord_1339484, baseEnd_1339484] using wordTrace_append hprefix tailTrace_1339484
  have hstable : (prefixWord ++ tailWord_1339484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339484).length < 2 ^ (prefixWord ++ tailWord_1339484).sum := by decide
  have hdescent : baseEnd_1339484 < baseStart_1339484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339557 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_1339557 : Nat := 118140960795 + 1339557 * 2 ^ 59
def prefixEnd_1339557 : Nat := 4983230072969 + 3 ^ 40 * 1339557 * 2
def baseEnd_1339557 : Nat := 458557736729947140517997

theorem tailTrace_1339557 : CollatzResearch.WordTrace tailWord_1339557 prefixEnd_1339557 458557736729947140517997 := by
  unfold tailWord_1339557
  simp only [CollatzResearch.WordTrace]
  refine ⟨48857657608021241966752925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32571771738680827977835283 48857657608021241966752925)
  ·
    refine ⟨18321621603007965737532347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48857657608021241966752925 18321621603007965737532347)
    ·
      refine ⟨27482432404511948606298521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18321621603007965737532347 27482432404511948606298521)
      ·
        refine ⟨20611824303383961454723891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27482432404511948606298521 20611824303383961454723891)
        ·
          refine ⟨30917736455075942182085837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20611824303383961454723891 30917736455075942182085837)
          ·
            refine ⟨11594151170653478318282189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30917736455075942182085837 11594151170653478318282189)
            ·
              refine ⟨4347806688995054369355821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11594151170653478318282189 4347806688995054369355821)
              ·
                refine ⟨1630427508373145388508433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4347806688995054369355821 1630427508373145388508433)
                ·
                  refine ⟨1222820631279859041381325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1630427508373145388508433 1222820631279859041381325)
                  ·
                    refine ⟨458557736729947140517997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222820631279859041381325 458557736729947140517997)
                    ·
                      rfl

theorem cell22_1339557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_1339557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339557 prefixEnd_1339557 := by exact prefixLift 1339557
  have htrace : WordTrace (prefixWord ++ tailWord_1339557) baseStart_1339557 baseEnd_1339557 := by
    simpa [prefixWord, tailWord_1339557, baseEnd_1339557] using wordTrace_append hprefix tailTrace_1339557
  have hstable : (prefixWord ++ tailWord_1339557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339557).length < 2 ^ (prefixWord ++ tailWord_1339557).sum := by decide
  have hdescent : baseEnd_1339557 < baseStart_1339557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339630 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1339630 : Nat := 118140960795 + 1339630 * 2 ^ 59
def prefixEnd_1339630 : Nat := 4983230072969 + 3 ^ 40 * 1339630 * 2
def baseEnd_1339630 : Nat := 458582726121799283442773

theorem tailTrace_1339630 : CollatzResearch.WordTrace tailWord_1339630 prefixEnd_1339630 458582726121799283442773 := by
  unfold tailWord_1339630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6107540017094596929270043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32573546757837850289440229 6107540017094596929270043)
  ·
    refine ⟨9161310025641895393905065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6107540017094596929270043 9161310025641895393905065)
    ·
      refine ⟨6870982519231421545428799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9161310025641895393905065 6870982519231421545428799)
      ·
        refine ⟨10306473778847132318143199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6870982519231421545428799 10306473778847132318143199)
        ·
          refine ⟨15459710668270698477214799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306473778847132318143199 15459710668270698477214799)
          ·
            refine ⟨23189566002406047715822199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15459710668270698477214799 23189566002406047715822199)
            ·
              refine ⟨34784349003609071573733299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23189566002406047715822199 34784349003609071573733299)
              ·
                refine ⟨52176523505413607360599949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34784349003609071573733299 52176523505413607360599949)
                ·
                  refine ⟨19566196314530102760224981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52176523505413607360599949 19566196314530102760224981)
                  ·
                    refine ⟨458582726121799283442773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19566196314530102760224981 458582726121799283442773)
                    ·
                      rfl

theorem cell22_1339630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1339630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339630 prefixEnd_1339630 := by exact prefixLift 1339630
  have htrace : WordTrace (prefixWord ++ tailWord_1339630) baseStart_1339630 baseEnd_1339630 := by
    simpa [prefixWord, tailWord_1339630, baseEnd_1339630] using wordTrace_append hprefix tailTrace_1339630
  have hstable : (prefixWord ++ tailWord_1339630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339630).length < 2 ^ (prefixWord ++ tailWord_1339630).sum := by decide
  have hdescent : baseEnd_1339630 < baseStart_1339630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339679 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 1, 4]
def baseStart_1339679 : Nat := 118140960795 + 1339679 * 2 ^ 59
def prefixEnd_1339679 : Nat := 4983230072969 + 3 ^ 40 * 1339679 * 2
def baseEnd_1339679 : Nat := 458599499823179488967623

theorem tailTrace_1339679 : CollatzResearch.WordTrace tailWord_1339679 prefixEnd_1339679 458599499823179488967623 := by
  unfold tailWord_1339679
  simp only [CollatzResearch.WordTrace]
  refine ⟨48862107313579256802694091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32574738209052837868462727 48862107313579256802694091)
  ·
    refine ⟨73293160970368885204041137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48862107313579256802694091 73293160970368885204041137)
    ·
      refine ⟨54969870727776663903030853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73293160970368885204041137 54969870727776663903030853)
      ·
        refine ⟨10306850761458124481818285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54969870727776663903030853 10306850761458124481818285)
        ·
          refine ⟨3865069035546796680681857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10306850761458124481818285 3865069035546796680681857)
          ·
            refine ⟨2898801776660097510511393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865069035546796680681857 2898801776660097510511393)
            ·
              refine ⟨2174101332495073132883545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2898801776660097510511393 2174101332495073132883545)
              ·
                refine ⟨1630575999371304849662659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174101332495073132883545 1630575999371304849662659)
                ·
                  refine ⟨2445863999056957274493989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630575999371304849662659 2445863999056957274493989)
                  ·
                    refine ⟨458599499823179488967623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445863999056957274493989 458599499823179488967623)
                    ·
                      rfl

theorem cell22_1339679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_1339679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339679 prefixEnd_1339679 := by exact prefixLift 1339679
  have htrace : WordTrace (prefixWord ++ tailWord_1339679) baseStart_1339679 baseEnd_1339679 := by
    simpa [prefixWord, tailWord_1339679, baseEnd_1339679] using wordTrace_append hprefix tailTrace_1339679
  have hstable : (prefixWord ++ tailWord_1339679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339679).length < 2 ^ (prefixWord ++ tailWord_1339679).sum := by decide
  have hdescent : baseEnd_1339679 < baseStart_1339679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339687 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1339687 : Nat := 118140960795 + 1339687 * 2 ^ 59
def prefixEnd_1339687 : Nat := 4983230072969 + 3 ^ 40 * 1339687 * 2
def baseEnd_1339687 : Nat := 458602238386670134767599

theorem tailTrace_1339687 : CollatzResearch.WordTrace tailWord_1339687 prefixEnd_1339687 458602238386670134767599 := by
  unfold tailWord_1339687
  simp only [CollatzResearch.WordTrace]
  refine ⟨48862399097550274168985315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32574932731700182779323543 48862399097550274168985315)
  ·
    refine ⟨73293598646325411253477973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48862399097550274168985315 73293598646325411253477973)
    ·
      refine ⟨858909359136625913126695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 73293598646325411253477973 858909359136625913126695)
      ·
        refine ⟨1288364038704938869690043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858909359136625913126695 1288364038704938869690043)
        ·
          refine ⟨1932546058057408304535065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288364038704938869690043 1932546058057408304535065)
          ·
            refine ⟨1449409543543056228401299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1932546058057408304535065 1449409543543056228401299)
            ·
              refine ⟨2174114315314584342601949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449409543543056228401299 2174114315314584342601949)
              ·
                refine ⟨815292868242969128475731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174114315314584342601949 815292868242969128475731)
                ·
                  refine ⟨1222939302364453692713597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815292868242969128475731 1222939302364453692713597)
                  ·
                    refine ⟨458602238386670134767599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222939302364453692713597 458602238386670134767599)
                    ·
                      rfl

theorem cell22_1339687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1339687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339687 prefixEnd_1339687 := by exact prefixLift 1339687
  have htrace : WordTrace (prefixWord ++ tailWord_1339687) baseStart_1339687 baseEnd_1339687 := by
    simpa [prefixWord, tailWord_1339687, baseEnd_1339687] using wordTrace_append hprefix tailTrace_1339687
  have hstable : (prefixWord ++ tailWord_1339687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339687).length < 2 ^ (prefixWord ++ tailWord_1339687).sum := by decide
  have hdescent : baseEnd_1339687 < baseStart_1339687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339692 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_1339692 : Nat := 118140960795 + 1339692 * 2 ^ 59
def prefixEnd_1339692 : Nat := 4983230072969 + 3 ^ 40 * 1339692 * 2
def baseEnd_1339692 : Nat := 458603949988851788392583

theorem tailTrace_1339692 : CollatzResearch.WordTrace tailWord_1339692 prefixEnd_1339692 458603949988851788392583 := by
  unfold tailWord_1339692
  simp only [CollatzResearch.WordTrace]
  refine ⟨24431290731266080011458665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32575054308354773348611553 24431290731266080011458665)
  ·
    refine ⟨18323468048449560008593999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24431290731266080011458665 18323468048449560008593999)
    ·
      refine ⟨27485202072674340012890999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18323468048449560008593999 27485202072674340012890999)
      ·
        refine ⟨41227803109011510019336499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27485202072674340012890999 41227803109011510019336499)
        ·
          refine ⟨61841704663517265029004749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41227803109011510019336499 61841704663517265029004749)
          ·
            refine ⟨23190639248818974385876781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61841704663517265029004749 23190639248818974385876781)
            ·
              refine ⟨8696489718307115394703793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23190639248818974385876781 8696489718307115394703793)
              ·
                refine ⟨6522367288730336546027845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8696489718307115394703793 6522367288730336546027845)
                ·
                  refine ⟨1222943866636938102380221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6522367288730336546027845 1222943866636938102380221)
                  ·
                    refine ⟨458603949988851788392583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222943866636938102380221 458603949988851788392583)
                    ·
                      rfl

theorem cell22_1339692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_1339692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339692 prefixEnd_1339692 := by exact prefixLift 1339692
  have htrace : WordTrace (prefixWord ++ tailWord_1339692) baseStart_1339692 baseEnd_1339692 := by
    simpa [prefixWord, tailWord_1339692, baseEnd_1339692] using wordTrace_append hprefix tailTrace_1339692
  have hstable : (prefixWord ++ tailWord_1339692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339692).length < 2 ^ (prefixWord ++ tailWord_1339692).sum := by decide
  have hdescent : baseEnd_1339692 < baseStart_1339692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339737 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_1339737 : Nat := 118140960795 + 1339737 * 2 ^ 59
def prefixEnd_1339737 : Nat := 4983230072969 + 3 ^ 40 * 1339737 * 2
def baseEnd_1339737 : Nat := 458619354408486671017445

theorem tailTrace_1339737 : CollatzResearch.WordTrace tailWord_1339737 prefixEnd_1339737 458619354408486671017445 := by
  unfold tailWord_1339737
  simp only [CollatzResearch.WordTrace]
  refine ⟨48864222747369132708305465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32576148498246088472203643 48864222747369132708305465)
  ·
    refine ⟨36648167060526849531229099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48864222747369132708305465 36648167060526849531229099)
    ·
      refine ⟨54972250590790274296843649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36648167060526849531229099 54972250590790274296843649)
      ·
        refine ⟨41229187943092705722632737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54972250590790274296843649 41229187943092705722632737)
        ·
          refine ⟨30921890957319529291974553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41229187943092705722632737 30921890957319529291974553)
          ·
            refine ⟨23191418217989646968980915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30921890957319529291974553 23191418217989646968980915)
            ·
              refine ⟨34787127326984470453471373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23191418217989646968980915 34787127326984470453471373)
              ·
                refine ⟨13045172747619176420051765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34787127326984470453471373 13045172747619176420051765)
                ·
                  refine ⟨1222984945089297789379853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13045172747619176420051765 1222984945089297789379853)
                  ·
                    refine ⟨458619354408486671017445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222984945089297789379853 458619354408486671017445)
                    ·
                      rfl

theorem cell22_1339737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_1339737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339737 prefixEnd_1339737 := by exact prefixLift 1339737
  have htrace : WordTrace (prefixWord ++ tailWord_1339737) baseStart_1339737 baseEnd_1339737 := by
    simpa [prefixWord, tailWord_1339737, baseEnd_1339737] using wordTrace_append hprefix tailTrace_1339737
  have hstable : (prefixWord ++ tailWord_1339737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339737).length < 2 ^ (prefixWord ++ tailWord_1339737).sum := by decide
  have hdescent : baseEnd_1339737 < baseStart_1339737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339771 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 1, 3]
def baseStart_1339771 : Nat := 118140960795 + 1339771 * 2 ^ 59
def prefixEnd_1339771 : Nat := 4983230072969 + 3 ^ 40 * 1339771 * 2
def baseEnd_1339771 : Nat := 458630993303321915667341

theorem tailTrace_1339771 : CollatzResearch.WordTrace tailWord_1339771 prefixEnd_1339771 458630993303321915667341 := by
  unfold tailWord_1339771
  simp only [CollatzResearch.WordTrace]
  refine ⟨48865462829245956515043167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32576975219497304343362111 48865462829245956515043167)
  ·
    refine ⟨73298194243868934772564751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48865462829245956515043167 73298194243868934772564751)
    ·
      refine ⟨109947291365803402158847127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73298194243868934772564751 109947291365803402158847127)
      ·
        refine ⟨164920937048705103238270691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109947291365803402158847127 164920937048705103238270691)
        ·
          refine ⟨247381405573057654857406037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164920937048705103238270691 247381405573057654857406037)
          ·
            refine ⟨2899000846559269392860227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 247381405573057654857406037 2899000846559269392860227)
            ·
              refine ⟨4348501269838904089290341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899000846559269392860227 4348501269838904089290341)
              ·
                refine ⟨815343988094794516741939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4348501269838904089290341 815343988094794516741939)
                ·
                  refine ⟨1223015982142191775112909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815343988094794516741939 1223015982142191775112909)
                  ·
                    refine ⟨458630993303321915667341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223015982142191775112909 458630993303321915667341)
                    ·
                      rfl

theorem cell22_1339771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 3].length) (baseStart_1339771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339771 prefixEnd_1339771 := by exact prefixLift 1339771
  have htrace : WordTrace (prefixWord ++ tailWord_1339771) baseStart_1339771 baseEnd_1339771 := by
    simpa [prefixWord, tailWord_1339771, baseEnd_1339771] using wordTrace_append hprefix tailTrace_1339771
  have hstable : (prefixWord ++ tailWord_1339771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339771).length < 2 ^ (prefixWord ++ tailWord_1339771).sum := by decide
  have hdescent : baseEnd_1339771 < baseStart_1339771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339818 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_1339818 : Nat := 118140960795 + 1339818 * 2 ^ 59
def prefixEnd_1339818 : Nat := 4983230072969 + 3 ^ 40 * 1339818 * 2
def baseEnd_1339818 : Nat := 152882360787943153247399

theorem tailTrace_1339818 : CollatzResearch.WordTrace tailWord_1339818 prefixEnd_1339818 152882360787943153247399 := by
  unfold tailWord_1339818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12216794265018920885501027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32578118040050455694669405 12216794265018920885501027)
  ·
    refine ⟨18325191397528381328251541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12216794265018920885501027 18325191397528381328251541)
    ·
      refine ⟨858993346759142874761791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18325191397528381328251541 858993346759142874761791)
      ·
        refine ⟨1288490020138714312142687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858993346759142874761791 1288490020138714312142687)
        ·
          refine ⟨1932735030208071468214031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288490020138714312142687 1932735030208071468214031)
          ·
            refine ⟨2899102545312107202321047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932735030208071468214031 2899102545312107202321047)
            ·
              refine ⟨4348653817968160803481571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899102545312107202321047 4348653817968160803481571)
              ·
                refine ⟨6522980726952241205222357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348653817968160803481571 6522980726952241205222357)
                ·
                  refine ⟨152882360787943153247399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6522980726952241205222357 152882360787943153247399)
                  ·
                    rfl

theorem cell22_1339818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_1339818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339818 prefixEnd_1339818 := by exact prefixLift 1339818
  have htrace : WordTrace (prefixWord ++ tailWord_1339818) baseStart_1339818 baseEnd_1339818 := by
    simpa [prefixWord, tailWord_1339818, baseEnd_1339818] using wordTrace_append hprefix tailTrace_1339818
  have hstable : (prefixWord ++ tailWord_1339818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339818).length < 2 ^ (prefixWord ++ tailWord_1339818).sum := by decide
  have hdescent : baseEnd_1339818 < baseStart_1339818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339887 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_1339887 : Nat := 118140960795 + 1339887 * 2 ^ 59
def prefixEnd_1339887 : Nat := 4983230072969 + 3 ^ 40 * 1339887 * 2
def baseEnd_1339887 : Nat := 458670702473936279766985

theorem tailTrace_1339887 : CollatzResearch.WordTrace tailWord_1339887 prefixEnd_1339887 458670702473936279766985 := by
  unfold tailWord_1339887
  simp only [CollatzResearch.WordTrace]
  refine ⟨48869693696825708326265915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32579795797883805550843943 48869693696825708326265915)
  ·
    refine ⟨73304540545238562489398873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48869693696825708326265915 73304540545238562489398873)
    ·
      refine ⟨54978405408928921867049155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73304540545238562489398873 54978405408928921867049155)
      ·
        refine ⟨82467608113393382800573733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54978405408928921867049155 82467608113393382800573733)
        ·
          refine ⟨15462676521261259275107575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82467608113393382800573733 15462676521261259275107575)
          ·
            refine ⟨23194014781891888912661363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15462676521261259275107575 23194014781891888912661363)
            ·
              refine ⟨34791022172837833368992045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23194014781891888912661363 34791022172837833368992045)
              ·
                refine ⟨13046633314814187513372017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34791022172837833368992045 13046633314814187513372017)
                ·
                  refine ⟨9784974986110640635029013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13046633314814187513372017 9784974986110640635029013)
                  ·
                    refine ⟨458670702473936279766985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9784974986110640635029013 458670702473936279766985)
                    ·
                      rfl

theorem cell22_1339887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_1339887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339887 prefixEnd_1339887 := by exact prefixLift 1339887
  have htrace : WordTrace (prefixWord ++ tailWord_1339887) baseStart_1339887 baseEnd_1339887 := by
    simpa [prefixWord, tailWord_1339887, baseEnd_1339887] using wordTrace_append hprefix tailTrace_1339887
  have hstable : (prefixWord ++ tailWord_1339887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339887).length < 2 ^ (prefixWord ++ tailWord_1339887).sum := by decide
  have hdescent : baseEnd_1339887 < baseStart_1339887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339910 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1339910 : Nat := 118140960795 + 1339910 * 2 ^ 59
def prefixEnd_1339910 : Nat := 4983230072969 + 3 ^ 40 * 1339910 * 2
def baseEnd_1339910 : Nat := 458678575843971886441915

theorem tailTrace_1339910 : CollatzResearch.WordTrace tailWord_1339910 prefixEnd_1339910 458678575843971886441915 := by
  unfold tailWord_1339910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527204142991949476698537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32580355050494922169568789 1527204142991949476698537)
  ·
    refine ⟨1145403107243962107523903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1527204142991949476698537 1145403107243962107523903)
    ·
      refine ⟨1718104660865943161285855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145403107243962107523903 1718104660865943161285855)
      ·
        refine ⟨2577156991298914741928783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718104660865943161285855 2577156991298914741928783)
        ·
          refine ⟨3865735486948372112893175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577156991298914741928783 3865735486948372112893175)
          ·
            refine ⟨5798603230422558169339763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3865735486948372112893175 5798603230422558169339763)
            ·
              refine ⟨8697904845633837254009645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5798603230422558169339763 8697904845633837254009645)
              ·
                refine ⟨3261714317112688970253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8697904845633837254009645 3261714317112688970253617)
                ·
                  refine ⟨2446285737834516727690213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261714317112688970253617 2446285737834516727690213)
                  ·
                    refine ⟨458678575843971886441915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2446285737834516727690213 458678575843971886441915)
                    ·
                      rfl

theorem cell22_1339910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1339910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339910 prefixEnd_1339910 := by exact prefixLift 1339910
  have htrace : WordTrace (prefixWord ++ tailWord_1339910) baseStart_1339910 baseEnd_1339910 := by
    simpa [prefixWord, tailWord_1339910, baseEnd_1339910] using wordTrace_append hprefix tailTrace_1339910
  have hstable : (prefixWord ++ tailWord_1339910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339910).length < 2 ^ (prefixWord ++ tailWord_1339910).sum := by decide
  have hdescent : baseEnd_1339910 < baseStart_1339910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339947 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 10]
def baseStart_1339947 : Nat := 118140960795 + 1339947 * 2 ^ 59
def prefixEnd_1339947 : Nat := 4983230072969 + 3 ^ 40 * 1339947 * 2
def baseEnd_1339947 : Nat := 152897080566705374422267

theorem tailTrace_1339947 : CollatzResearch.WordTrace tailWord_1339947 prefixEnd_1339947 152897080566705374422267 := by
  unfold tailWord_1339947
  simp only [CollatzResearch.WordTrace]
  refine ⟨48871882076608338573450095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32581254717738892382300063 48871882076608338573450095)
  ·
    refine ⟨73307823114912507860175143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48871882076608338573450095 73307823114912507860175143)
    ·
      refine ⟨109961734672368761790262715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73307823114912507860175143 109961734672368761790262715)
      ·
        refine ⟨164942602008553142685394073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109961734672368761790262715 164942602008553142685394073)
        ·
          refine ⟨123706951506414857014045555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164942602008553142685394073 123706951506414857014045555)
          ·
            refine ⟨185560427259622285521068333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123706951506414857014045555 185560427259622285521068333)
            ·
              refine ⟨69585160222358357070400625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185560427259622285521068333 69585160222358357070400625)
              ·
                refine ⟨52188870166768767802800469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69585160222358357070400625 52188870166768767802800469)
                ·
                  refine ⟨152897080566705374422267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 52188870166768767802800469 152897080566705374422267)
                  ·
                    rfl

theorem cell22_1339947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_1339947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339947 prefixEnd_1339947 := by exact prefixLift 1339947
  have htrace : WordTrace (prefixWord ++ tailWord_1339947) baseStart_1339947 baseEnd_1339947 := by
    simpa [prefixWord, tailWord_1339947, baseEnd_1339947] using wordTrace_append hprefix tailTrace_1339947
  have hstable : (prefixWord ++ tailWord_1339947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339947).length < 2 ^ (prefixWord ++ tailWord_1339947).sum := by decide
  have hdescent : baseEnd_1339947 < baseStart_1339947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339964 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_1339964 : Nat := 118140960795 + 1339964 * 2 ^ 59
def prefixEnd_1339964 : Nat := 4983230072969 + 3 ^ 40 * 1339964 * 2
def baseEnd_1339964 : Nat := 152899020382511248530583

theorem tailTrace_1339964 : CollatzResearch.WordTrace tailWord_1339964 prefixEnd_1339964 152899020382511248530583 := by
  unfold tailWord_1339964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24436251058773375238409473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32581668078364500317879297 24436251058773375238409473)
  ·
    refine ⟨18327188294080031428807105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24436251058773375238409473 18327188294080031428807105)
    ·
      refine ⟨13745391220560023571605329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18327188294080031428807105 13745391220560023571605329)
      ·
        refine ⟨10309043415420017678703997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13745391220560023571605329 10309043415420017678703997)
        ·
          refine ⟨3865891280782506629513999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10309043415420017678703997 3865891280782506629513999)
          ·
            refine ⟨5798836921173759944270999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3865891280782506629513999 5798836921173759944270999)
            ·
              refine ⟨8698255381760639916406499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5798836921173759944270999 8698255381760639916406499)
              ·
                refine ⟨13047383072640959874609749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8698255381760639916406499 13047383072640959874609749)
                ·
                  refine ⟨152899020382511248530583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13047383072640959874609749 152899020382511248530583)
                  ·
                    rfl

theorem cell22_1339964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_1339964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339964 prefixEnd_1339964 := by exact prefixLift 1339964
  have htrace : WordTrace (prefixWord ++ tailWord_1339964) baseStart_1339964 baseEnd_1339964 := by
    simpa [prefixWord, tailWord_1339964, baseEnd_1339964] using wordTrace_append hprefix tailTrace_1339964
  have hstable : (prefixWord ++ tailWord_1339964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339964).length < 2 ^ (prefixWord ++ tailWord_1339964).sum := by decide
  have hdescent : baseEnd_1339964 < baseStart_1339964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339979 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 1, 5]
def baseStart_1339979 : Nat := 118140960795 + 1339979 * 2 ^ 59
def prefixEnd_1339979 : Nat := 4983230072969 + 3 ^ 40 * 1339979 * 2
def baseEnd_1339979 : Nat := 458702195954078706466703

theorem tailTrace_1339979 : CollatzResearch.WordTrace tailWord_1339979 prefixEnd_1339979 458702195954078706466703 := by
  unfold tailWord_1339979
  simp only [CollatzResearch.WordTrace]
  refine ⟨48873049212492408038614991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32582032808328272025743327 48873049212492408038614991)
  ·
    refine ⟨73309573818738612057922487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48873049212492408038614991 73309573818738612057922487)
    ·
      refine ⟨109964360728107918086883731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73309573818738612057922487 109964360728107918086883731)
      ·
        refine ⟨164946541092161877130325597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109964360728107918086883731 164946541092161877130325597)
        ·
          refine ⟨61854952909560703923872099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164946541092161877130325597 61854952909560703923872099)
          ·
            refine ⟨92782429364341055885808149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61854952909560703923872099 92782429364341055885808149)
            ·
              refine ⟨4349176376453486994647257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92782429364341055885808149 4349176376453486994647257)
              ·
                refine ⟨3261882282340115245985443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4349176376453486994647257 3261882282340115245985443)
                ·
                  refine ⟨4892823423510172868978165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261882282340115245985443 4892823423510172868978165)
                  ·
                    refine ⟨458702195954078706466703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4892823423510172868978165 458702195954078706466703)
                    ·
                      rfl

theorem cell22_1339979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_1339979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1339979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1339979 prefixEnd_1339979 := by exact prefixLift 1339979
  have htrace : WordTrace (prefixWord ++ tailWord_1339979) baseStart_1339979 baseEnd_1339979 := by
    simpa [prefixWord, tailWord_1339979, baseEnd_1339979] using wordTrace_append hprefix tailTrace_1339979
  have hstable : (prefixWord ++ tailWord_1339979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339979).length < 2 ^ (prefixWord ++ tailWord_1339979).sum := by decide
  have hdescent : baseEnd_1339979 < baseStart_1339979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340013 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1340013 : Nat := 118140960795 + 1340013 * 2 ^ 59
def prefixEnd_1340013 : Nat := 4983230072969 + 3 ^ 40 * 1340013 * 2
def baseEnd_1340013 : Nat := 458713834848913951116599

theorem tailTrace_1340013 : CollatzResearch.WordTrace tailWord_1340013 prefixEnd_1340013 458713834848913951116599 := by
  unfold tailWord_1340013
  simp only [CollatzResearch.WordTrace]
  refine ⟨48874289294369231845352693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32582859529579487896901795 48874289294369231845352693)
  ·
    refine ⟨4581964621347115485501815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48874289294369231845352693 4581964621347115485501815)
    ·
      refine ⟨6872946932020673228252723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4581964621347115485501815 6872946932020673228252723)
      ·
        refine ⟨10309420398031009842379085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6872946932020673228252723 10309420398031009842379085)
        ·
          refine ⟨3866032649261628690892157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10309420398031009842379085 3866032649261628690892157)
          ·
            refine ⟨1449762243473110759084559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3866032649261628690892157 1449762243473110759084559)
            ·
              refine ⟨2174643365209666138626839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449762243473110759084559 2174643365209666138626839)
              ·
                refine ⟨3261965047814499207940259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174643365209666138626839 3261965047814499207940259)
                ·
                  refine ⟨4892947571721748811910389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261965047814499207940259 4892947571721748811910389)
                  ·
                    refine ⟨458713834848913951116599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4892947571721748811910389 458713834848913951116599)
                    ·
                      rfl

theorem cell22_1340013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1340013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340013 prefixEnd_1340013 := by exact prefixLift 1340013
  have htrace : WordTrace (prefixWord ++ tailWord_1340013) baseStart_1340013 baseEnd_1340013 := by
    simpa [prefixWord, tailWord_1340013, baseEnd_1340013] using wordTrace_append hprefix tailTrace_1340013
  have hstable : (prefixWord ++ tailWord_1340013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340013).length < 2 ^ (prefixWord ++ tailWord_1340013).sum := by decide
  have hdescent : baseEnd_1340013 < baseStart_1340013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
