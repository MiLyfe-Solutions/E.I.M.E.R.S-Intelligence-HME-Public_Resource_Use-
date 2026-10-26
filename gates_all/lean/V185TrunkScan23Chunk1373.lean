import V185TrunkScan23Chunk1372

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8132080 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 4, 2, 2]
def baseStart_8132080 : Nat := 118140960795 + 8132080 * 2 ^ 59
def prefixEnd_8132080 : Nat := 4983230072969 + 3 ^ 40 * 8132080 * 2
def baseEnd_8132080 : Nat := 4175665760814648433301251

theorem tailTrace_8132080 : CollatzResearch.WordTrace tailWord_8132080 prefixEnd_8132080 4175665760814648433301251 := by
  unfold tailWord_8132080
  simp only [CollatzResearch.WordTrace]
  refine ⟨148300662189435241768608847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197734216252580322358145129 148300662189435241768608847)
  ·
    refine ⟨222450993284152862652913271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148300662189435241768608847 222450993284152862652913271)
    ·
      refine ⟨333676489926229293979369907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222450993284152862652913271 333676489926229293979369907)
      ·
        refine ⟨500514734889343940969054861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333676489926229293979369907 500514734889343940969054861)
        ·
          refine ⟨187693025583503977863395573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500514734889343940969054861 187693025583503977863395573)
          ·
            refine ⟨17596221148453497924693335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187693025583503977863395573 17596221148453497924693335)
            ·
              refine ⟨26394331722680246887040003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17596221148453497924693335 26394331722680246887040003)
              ·
                refine ⟨39591497584020370330560005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26394331722680246887040003 39591497584020370330560005)
                ·
                  refine ⟨7423405797003819436980001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39591497584020370330560005 7423405797003819436980001)
                  ·
                    refine ⟨5567554347752864577735001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7423405797003819436980001 5567554347752864577735001)
                    ·
                      refine ⟨4175665760814648433301251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567554347752864577735001 4175665760814648433301251)
                      ·
                        rfl

theorem cell23_8132080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 2, 2].length) (baseStart_8132080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132080 prefixEnd_8132080 := by exact prefixLift 8132080
  have htrace : WordTrace (prefixWord ++ tailWord_8132080) baseStart_8132080 baseEnd_8132080 := by
    simpa [prefixWord, tailWord_8132080, baseEnd_8132080] using wordTrace_append hprefix tailTrace_8132080
  have hstable : (prefixWord ++ tailWord_8132080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132080).length < 2 ^ (prefixWord ++ tailWord_8132080).sum := by decide
  have hdescent : baseEnd_8132080 < baseStart_8132080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132097 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_8132097 : Nat := 118140960795 + 8132097 * 2 ^ 59
def prefixEnd_8132097 : Nat := 4983230072969 + 3 ^ 40 * 8132097 * 2
def baseEnd_8132097 : Nat := 4175674489985774866788673

theorem tailTrace_8132097 : CollatzResearch.WordTrace tailWord_8132097 prefixEnd_8132097 4175674489985774866788673 := by
  unfold tailWord_8132097
  simp only [CollatzResearch.WordTrace]
  refine ⟨296601944419808895440586545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197734629613205930293724363 296601944419808895440586545)
  ·
    refine ⟨222451458314856671580439909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296601944419808895440586545 222451458314856671580439909)
    ·
      refine ⟨41709648434035625921332483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222451458314856671580439909 41709648434035625921332483)
      ·
        refine ⟨62564472651053438881998725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41709648434035625921332483 62564472651053438881998725)
        ·
          refine ⟨11730838622072519790374761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62564472651053438881998725 11730838622072519790374761)
          ·
            refine ⟨8798128966554389842781071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11730838622072519790374761 8798128966554389842781071)
            ·
              refine ⟨13197193449831584764171607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798128966554389842781071 13197193449831584764171607)
              ·
                refine ⟨19795790174747377146257411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197193449831584764171607 19795790174747377146257411)
                ·
                  refine ⟨29693685262121065719386117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19795790174747377146257411 29693685262121065719386117)
                  ·
                    refine ⟨5567565986647699822384897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29693685262121065719386117 5567565986647699822384897)
                    ·
                      refine ⟨4175674489985774866788673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567565986647699822384897 4175674489985774866788673)
                      ·
                        rfl

theorem cell23_8132097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_8132097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132097 prefixEnd_8132097 := by exact prefixLift 8132097
  have htrace : WordTrace (prefixWord ++ tailWord_8132097) baseStart_8132097 baseEnd_8132097 := by
    simpa [prefixWord, tailWord_8132097, baseEnd_8132097] using wordTrace_append hprefix tailTrace_8132097
  have hstable : (prefixWord ++ tailWord_8132097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132097).length < 2 ^ (prefixWord ++ tailWord_8132097).sum := by decide
  have hdescent : baseEnd_8132097 < baseStart_8132097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132193 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 6]
def baseStart_8132193 : Nat := 118140960795 + 8132193 * 2 ^ 59
def prefixEnd_8132193 : Nat := 4983230072969 + 3 ^ 40 * 8132193 * 2
def baseEnd_8132193 : Nat := 463969309347622943465359

theorem tailTrace_8132193 : CollatzResearch.WordTrace tailWord_8132193 prefixEnd_8132193 463969309347622943465359 := by
  unfold tailWord_8132193
  simp only [CollatzResearch.WordTrace]
  refine ⟨296605445827461103836081233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197736963884974069224054155 296605445827461103836081233)
  ·
    refine ⟨222454084370595827877060925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296605445827461103836081233 222454084370595827877060925)
    ·
      refine ⟨83420281638973435453897847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222454084370595827877060925 83420281638973435453897847)
      ·
        refine ⟨125130422458460153180846771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83420281638973435453897847 125130422458460153180846771)
        ·
          refine ⟨187695633687690229771270157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125130422458460153180846771 187695633687690229771270157)
          ·
            refine ⟨70385862632883836164226309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187695633687690229771270157 70385862632883836164226309)
            ·
              refine ⟨13197349243665719280792433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70385862632883836164226309 13197349243665719280792433)
              ·
                refine ⟨9898011932749289460594325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13197349243665719280792433 9898011932749289460594325)
                ·
                  refine ⟨463969309347622943465359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9898011932749289460594325 463969309347622943465359)
                  ·
                    rfl

theorem cell23_8132193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 6].length) (baseStart_8132193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132193 prefixEnd_8132193 := by exact prefixLift 8132193
  have htrace : WordTrace (prefixWord ++ tailWord_8132193) baseStart_8132193 baseEnd_8132193 := by
    simpa [prefixWord, tailWord_8132193, baseEnd_8132193] using wordTrace_append hprefix tailTrace_8132193
  have hstable : (prefixWord ++ tailWord_8132193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132193).length < 2 ^ (prefixWord ++ tailWord_8132193).sum := by decide
  have hdescent : baseEnd_8132193 < baseStart_8132193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132197 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_8132197 : Nat := 118140960795 + 8132197 * 2 ^ 59
def prefixEnd_8132197 : Nat := 4983230072969 + 3 ^ 40 * 8132197 * 2
def baseEnd_8132197 : Nat := 1391908612683741491846071

theorem tailTrace_8132197 : CollatzResearch.WordTrace tailWord_8132197 prefixEnd_8132197 1391908612683741491846071 := by
  unfold tailWord_8132197
  simp only [CollatzResearch.WordTrace]
  refine ⟨296605591719446612519226845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197737061146297741679484563 296605591719446612519226845)
  ·
    refine ⟨111227096894792479694710067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296605591719446612519226845 111227096894792479694710067)
    ·
      refine ⟨166840645342188719542065101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111227096894792479694710067 166840645342188719542065101)
      ·
        refine ⟨62565242003320769828274413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166840645342188719542065101 62565242003320769828274413)
        ·
          refine ⟨23461965751245288685602905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62565242003320769828274413 23461965751245288685602905)
          ·
            refine ⟨17596474313433966514202179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23461965751245288685602905 17596474313433966514202179)
            ·
              refine ⟨26394711470150949771303269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17596474313433966514202179 26394711470150949771303269)
              ·
                refine ⟨4949008400653303082119363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26394711470150949771303269 4949008400653303082119363)
                ·
                  refine ⟨7423512600979954623179045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949008400653303082119363 7423512600979954623179045)
                  ·
                    refine ⟨1391908612683741491846071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423512600979954623179045 1391908612683741491846071)
                    ·
                      rfl

theorem cell23_8132197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_8132197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132197 prefixEnd_8132197 := by exact prefixLift 8132197
  have htrace : WordTrace (prefixWord ++ tailWord_8132197) baseStart_8132197 baseEnd_8132197 := by
    simpa [prefixWord, tailWord_8132197, baseEnd_8132197] using wordTrace_append hprefix tailTrace_8132197
  have hstable : (prefixWord ++ tailWord_8132197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132197).length < 2 ^ (prefixWord ++ tailWord_8132197).sum := by decide
  have hdescent : baseEnd_8132197 < baseStart_8132197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132244 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 6]
def baseStart_8132244 : Nat := 118140960795 + 8132244 * 2 ^ 59
def prefixEnd_8132244 : Nat := 4983230072969 + 3 ^ 40 * 8132244 * 2
def baseEnd_8132244 : Nat := 463972219071331754627833

theorem tailTrace_8132244 : CollatzResearch.WordTrace tailWord_8132244 prefixEnd_8132244 463972219071331754627833 := by
  unfold tailWord_8132244
  simp only [CollatzResearch.WordTrace]
  refine ⟨148303652975138169773093893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197738203966850893030791857 148303652975138169773093893)
  ·
    refine ⟨27806934932838406832455105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148303652975138169773093893 27806934932838406832455105)
    ·
      refine ⟨20855201199628805124341329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27806934932838406832455105 20855201199628805124341329)
      ·
        refine ⟨15641400899721603843255997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20855201199628805124341329 15641400899721603843255997)
        ·
          refine ⟨5865525337395601441220999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15641400899721603843255997 5865525337395601441220999)
          ·
            refine ⟨8798288006093402161831499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865525337395601441220999 8798288006093402161831499)
            ·
              refine ⟨13197432009140103242747249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798288006093402161831499 13197432009140103242747249)
              ·
                refine ⟨9898074006855077432060437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13197432009140103242747249 9898074006855077432060437)
                ·
                  refine ⟨463972219071331754627833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9898074006855077432060437 463972219071331754627833)
                  ·
                    rfl

theorem cell23_8132244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_8132244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132244 prefixEnd_8132244 := by exact prefixLift 8132244
  have htrace : WordTrace (prefixWord ++ tailWord_8132244) baseStart_8132244 baseEnd_8132244 := by
    simpa [prefixWord, tailWord_8132244, baseEnd_8132244] using wordTrace_append hprefix tailTrace_8132244
  have hstable : (prefixWord ++ tailWord_8132244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132244).length < 2 ^ (prefixWord ++ tailWord_8132244).sum := by decide
  have hdescent : baseEnd_8132244 < baseStart_8132244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132254 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_8132254 : Nat := 118140960795 + 8132254 * 2 ^ 59
def prefixEnd_8132254 : Nat := 4983230072969 + 3 ^ 40 * 8132254 * 2
def baseEnd_8132254 : Nat := 4175755106448530752525451

theorem tailTrace_8132254 : CollatzResearch.WordTrace tailWord_8132254 prefixEnd_8132254 4175755106448530752525451 := by
  unfold tailWord_8132254
  simp only [CollatzResearch.WordTrace]
  refine ⟨37075958835030013906756477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197738447120160074169367877 37075958835030013906756477)
  ·
    refine ⟨13903484563136255215033679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37075958835030013906756477 13903484563136255215033679)
    ·
      refine ⟨20855226844704382822550519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13903484563136255215033679 20855226844704382822550519)
      ·
        refine ⟨31282840267056574233825779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20855226844704382822550519 31282840267056574233825779)
        ·
          refine ⟨46924260400584861350738669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31282840267056574233825779 46924260400584861350738669)
          ·
            refine ⟨17596597650219323006527001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46924260400584861350738669 17596597650219323006527001)
            ·
              refine ⟨13197448237664492254895251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17596597650219323006527001 13197448237664492254895251)
              ·
                refine ⟨19796172356496738382342877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197448237664492254895251 19796172356496738382342877)
                ·
                  refine ⟨7423564633686276893378579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19796172356496738382342877 7423564633686276893378579)
                  ·
                    refine ⟨11135346950529415340067869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7423564633686276893378579 11135346950529415340067869)
                    ·
                      refine ⟨4175755106448530752525451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11135346950529415340067869 4175755106448530752525451)
                      ·
                        rfl

theorem cell23_8132254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_8132254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132254 prefixEnd_8132254 := by exact prefixLift 8132254
  have htrace : WordTrace (prefixWord ++ tailWord_8132254) baseStart_8132254 baseEnd_8132254 := by
    simpa [prefixWord, tailWord_8132254, baseEnd_8132254] using wordTrace_append hprefix tailTrace_8132254
  have hstable : (prefixWord ++ tailWord_8132254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132254).length < 2 ^ (prefixWord ++ tailWord_8132254).sum := by decide
  have hdescent : baseEnd_8132254 < baseStart_8132254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132300 : List Nat := [2, 2, 1, 5, 2, 2, 9]
def baseStart_8132300 : Nat := 118140960795 + 8132300 * 2 ^ 59
def prefixEnd_8132300 : Nat := 4983230072969 + 3 ^ 40 * 8132300 * 2
def baseEnd_8132300 : Nat := 51552823784674537932719

theorem tailTrace_8132300 : CollatzResearch.WordTrace tailWord_8132300 prefixEnd_8132300 51552823784674537932719 := by
  unfold tailWord_8132300
  simp only [CollatzResearch.WordTrace]
  refine ⟨148304674219036730555113177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197739565625382307406817569 148304674219036730555113177)
  ·
    refine ⟨111228505664277547916334883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148304674219036730555113177 111228505664277547916334883)
    ·
      refine ⟨166842758496416321874502325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111228505664277547916334883 166842758496416321874502325)
      ·
        refine ⟨15641508609039030175734593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166842758496416321874502325 15641508609039030175734593)
        ·
          refine ⟨11731131456779272631800945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15641508609039030175734593 11731131456779272631800945)
          ·
            refine ⟨8798348592584454473850709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11731131456779272631800945 8798348592584454473850709)
            ·
              refine ⟨51552823784674537932719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8798348592584454473850709 51552823784674537932719)
              ·
                rfl

theorem cell23_8132300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 9].length) (baseStart_8132300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132300 prefixEnd_8132300 := by exact prefixLift 8132300
  have htrace : WordTrace (prefixWord ++ tailWord_8132300) baseStart_8132300 baseEnd_8132300 := by
    simpa [prefixWord, tailWord_8132300, baseEnd_8132300] using wordTrace_append hprefix tailTrace_8132300
  have hstable : (prefixWord ++ tailWord_8132300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132300).length < 2 ^ (prefixWord ++ tailWord_8132300).sum := by decide
  have hdescent : baseEnd_8132300 < baseStart_8132300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132311 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 1, 2, 2]
def baseStart_8132311 : Nat := 118140960795 + 8132311 * 2 ^ 59
def prefixEnd_8132311 : Nat := 4983230072969 + 3 ^ 40 * 8132311 * 2
def baseEnd_8132311 : Nat := 4175784374845837029512689

theorem tailTrace_8132311 : CollatzResearch.WordTrace tailWord_8132311 prefixEnd_8132311 4175784374845837029512689 := by
  unfold tailWord_8132311
  simp only [CollatzResearch.WordTrace]
  refine ⟨296609749641033609988876787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197739833094022406659251191 296609749641033609988876787)
  ·
    refine ⟨444914624461550414983315181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296609749641033609988876787 444914624461550414983315181)
    ·
      refine ⟨166842984173081405618743193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444914624461550414983315181 166842984173081405618743193)
      ·
        refine ⟨125132238129811054214057395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166842984173081405618743193 125132238129811054214057395)
        ·
          refine ⟨187698357194716581321086093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125132238129811054214057395 187698357194716581321086093)
          ·
            refine ⟨70386883948018717995407285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187698357194716581321086093 70386883948018717995407285)
            ·
              refine ⟨6598770370126754812069433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70386883948018717995407285 6598770370126754812069433)
              ·
                refine ⟨4949077777595066109052075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6598770370126754812069433 4949077777595066109052075)
                ·
                  refine ⟨7423616666392599163578113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949077777595066109052075 7423616666392599163578113)
                  ·
                    refine ⟨5567712499794449372683585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7423616666392599163578113 5567712499794449372683585)
                    ·
                      refine ⟨4175784374845837029512689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567712499794449372683585 4175784374845837029512689)
                      ·
                        rfl

theorem cell23_8132311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_8132311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132311 prefixEnd_8132311 := by exact prefixLift 8132311
  have htrace : WordTrace (prefixWord ++ tailWord_8132311) baseStart_8132311 baseEnd_8132311 := by
    simpa [prefixWord, tailWord_8132311, baseEnd_8132311] using wordTrace_append hprefix tailTrace_8132311
  have hstable : (prefixWord ++ tailWord_8132311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132311).length < 2 ^ (prefixWord ++ tailWord_8132311).sum := by decide
  have hdescent : baseEnd_8132311 < baseStart_8132311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132317 : List Nat := [1, 4, 3, 3, 1, 1, 2, 8]
def baseStart_8132317 : Nat := 118140960795 + 8132317 * 2 ^ 59
def prefixEnd_8132317 : Nat := 4983230072969 + 3 ^ 40 * 8132317 * 2
def baseEnd_8132317 : Nat := 154658794656657926149543

theorem tailTrace_8132317 : CollatzResearch.WordTrace tailWord_8132317 prefixEnd_8132317 154658794656657926149543 := by
  unfold tailWord_8132317
  simp only [CollatzResearch.WordTrace]
  refine ⟨296609968479011873013595205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197739978986007915342396803 296609968479011873013595205)
  ·
    refine ⟨55614369089814726190049101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296609968479011873013595205 55614369089814726190049101)
    ·
      refine ⟨20855388408680522321268413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55614369089814726190049101 20855388408680522321268413)
      ·
        refine ⟨7820770653255195870475655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20855388408680522321268413 7820770653255195870475655)
        ·
          refine ⟨11731155979882793805713483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820770653255195870475655 11731155979882793805713483)
          ·
            refine ⟨17596733969824190708570225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11731155979882793805713483 17596733969824190708570225)
            ·
              refine ⟨13197550477368143031427669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17596733969824190708570225 13197550477368143031427669)
              ·
                refine ⟨154658794656657926149543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13197550477368143031427669 154658794656657926149543)
                ·
                  rfl

theorem cell23_8132317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 8].length) (baseStart_8132317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132317 prefixEnd_8132317 := by exact prefixLift 8132317
  have htrace : WordTrace (prefixWord ++ tailWord_8132317) baseStart_8132317 baseEnd_8132317 := by
    simpa [prefixWord, tailWord_8132317, baseEnd_8132317] using wordTrace_append hprefix tailTrace_8132317
  have hstable : (prefixWord ++ tailWord_8132317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132317).length < 2 ^ (prefixWord ++ tailWord_8132317).sum := by decide
  have hdescent : baseEnd_8132317 < baseStart_8132317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132321 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 2, 4]
def baseStart_8132321 : Nat := 118140960795 + 8132321 * 2 ^ 59
def prefixEnd_8132321 : Nat := 4983230072969 + 3 ^ 40 * 8132321 * 2
def baseEnd_8132321 : Nat := 1391929836550793996795881

theorem tailTrace_8132321 : CollatzResearch.WordTrace tailWord_8132321 prefixEnd_8132321 1391929836550793996795881 := by
  unfold tailWord_8132321
  simp only [CollatzResearch.WordTrace]
  refine ⟨296610114370997381696740817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197740076247331587797827211 296610114370997381696740817)
  ·
    refine ⟨222457585778248036272555613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296610114370997381696740817 222457585778248036272555613)
    ·
      refine ⟨83421594666843013602208355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222457585778248036272555613 83421594666843013602208355)
      ·
        refine ⟨125132392000264520403312533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83421594666843013602208355 125132392000264520403312533)
        ·
          refine ⟨5865580875012399393905275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125132392000264520403312533 5865580875012399393905275)
          ·
            refine ⟨8798371312518599090857913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865580875012399393905275 8798371312518599090857913)
            ·
              refine ⟨6598778484388949318143435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8798371312518599090857913 6598778484388949318143435)
              ·
                refine ⟨9898167726583423977215153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598778484388949318143435 9898167726583423977215153)
                ·
                  refine ⟨7423625794937567982911365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9898167726583423977215153 7423625794937567982911365)
                  ·
                    refine ⟨1391929836550793996795881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423625794937567982911365 1391929836550793996795881)
                    ·
                      rfl

theorem cell23_8132321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_8132321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132321 prefixEnd_8132321 := by exact prefixLift 8132321
  have htrace : WordTrace (prefixWord ++ tailWord_8132321) baseStart_8132321 baseEnd_8132321 := by
    simpa [prefixWord, tailWord_8132321, baseEnd_8132321] using wordTrace_append hprefix tailTrace_8132321
  have hstable : (prefixWord ++ tailWord_8132321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132321).length < 2 ^ (prefixWord ++ tailWord_8132321).sum := by decide
  have hdescent : baseEnd_8132321 < baseStart_8132321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132337 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 3, 3, 2]
def baseStart_8132337 : Nat := 118140960795 + 8132337 * 2 ^ 59
def prefixEnd_8132337 : Nat := 4983230072969 + 3 ^ 40 * 8132337 * 2
def baseEnd_8132337 : Nat := 4175797725342853927787569

theorem tailTrace_8132337 : CollatzResearch.WordTrace tailWord_8132337 prefixEnd_8132337 4175797725342853927787569 := by
  unfold tailWord_8132337
  simp only [CollatzResearch.WordTrace]
  refine ⟨296610697938939416429323265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197740465292626277619548843 296610697938939416429323265)
  ·
    refine ⟨222458023454204562321992449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296610697938939416429323265 222458023454204562321992449)
    ·
      refine ⟨166843517590653421741494337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222458023454204562321992449 166843517590653421741494337)
      ·
        refine ⟨125132638192990066306120753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166843517590653421741494337 125132638192990066306120753)
        ·
          refine ⟨93849478644742549729590565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125132638192990066306120753 93849478644742549729590565)
          ·
            refine ⟨17596777245889228074298231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93849478644742549729590565 17596777245889228074298231)
            ·
              refine ⟨26395165868833842111447347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17596777245889228074298231 26395165868833842111447347)
              ·
                refine ⟨39592748803250763167171021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26395165868833842111447347 39592748803250763167171021)
                ·
                  refine ⟨14847280801219036187689133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39592748803250763167171021 14847280801219036187689133)
                  ·
                    refine ⟨5567730300457138570383425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14847280801219036187689133 5567730300457138570383425)
                    ·
                      refine ⟨4175797725342853927787569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567730300457138570383425 4175797725342853927787569)
                      ·
                        rfl

theorem cell23_8132337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_8132337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132337 prefixEnd_8132337 := by exact prefixLift 8132337
  have htrace : WordTrace (prefixWord ++ tailWord_8132337) baseStart_8132337 baseEnd_8132337 := by
    simpa [prefixWord, tailWord_8132337, baseEnd_8132337] using wordTrace_append hprefix tailTrace_8132337
  have hstable : (prefixWord ++ tailWord_8132337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132337).length < 2 ^ (prefixWord ++ tailWord_8132337).sum := by decide
  have hdescent : baseEnd_8132337 < baseStart_8132337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132380 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_8132380 : Nat := 118140960795 + 8132380 * 2 ^ 59
def prefixEnd_8132380 : Nat := 4983230072969 + 3 ^ 40 * 8132380 * 2
def baseEnd_8132380 : Nat := 4175819805010997259549871

theorem tailTrace_8132380 : CollatzResearch.WordTrace tailWord_8132380 prefixEnd_8132380 4175819805010997259549871 := by
  unfold tailWord_8132380
  simp only [CollatzResearch.WordTrace]
  refine ⟨148306133138891817386569297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197741510851855756515425729 148306133138891817386569297)
  ·
    refine ⟨111229599854168863039926973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148306133138891817386569297 111229599854168863039926973)
    ·
      refine ⟨41711099945313323639972615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111229599854168863039926973 41711099945313323639972615)
      ·
        refine ⟨62566649917969985459958923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41711099945313323639972615 62566649917969985459958923)
        ·
          refine ⟨93849974876954978189938385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62566649917969985459958923 93849974876954978189938385)
          ·
            refine ⟨70387481157716233642453789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93849974876954978189938385 70387481157716233642453789)
            ·
              refine ⟨26395305434143587615920171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70387481157716233642453789 26395305434143587615920171)
              ·
                refine ⟨39592958151215381423880257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26395305434143587615920171 39592958151215381423880257)
                ·
                  refine ⟨29694718613411536067910193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39592958151215381423880257 29694718613411536067910193)
                  ·
                    refine ⟨22271038960058652050932645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29694718613411536067910193 22271038960058652050932645)
                    ·
                      refine ⟨4175819805010997259549871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22271038960058652050932645 4175819805010997259549871)
                      ·
                        rfl

theorem cell23_8132380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_8132380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132380 prefixEnd_8132380 := by exact prefixLift 8132380
  have htrace : WordTrace (prefixWord ++ tailWord_8132380) baseStart_8132380 baseEnd_8132380 := by
    simpa [prefixWord, tailWord_8132380, baseEnd_8132380] using wordTrace_append hprefix tailTrace_8132380
  have hstable : (prefixWord ++ tailWord_8132380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132380).length < 2 ^ (prefixWord ++ tailWord_8132380).sum := by decide
  have hdescent : baseEnd_8132380 < baseStart_8132380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132384 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 2, 2, 2]
def baseStart_8132384 : Nat := 118140960795 + 8132384 * 2 ^ 59
def prefixEnd_8132384 : Nat := 4983230072969 + 3 ^ 40 * 8132384 * 2
def baseEnd_8132384 : Nat := 4175821858933615243899853

theorem tailTrace_8132384 : CollatzResearch.WordTrace tailWord_8132384 prefixEnd_8132384 4175821858933615243899853 := by
  unfold tailWord_8132384
  simp only [CollatzResearch.WordTrace]
  refine ⟨148306206084884571728142103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197741608113179428970856137 148306206084884571728142103)
  ·
    refine ⟨222459309127326857592213155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148306206084884571728142103 222459309127326857592213155)
    ·
      refine ⟨333688963690990286388319733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222459309127326857592213155 333688963690990286388319733)
      ·
        refine ⟨31283340346030339348904975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333688963690990286388319733 31283340346030339348904975)
        ·
          refine ⟨46925010519045509023357463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31283340346030339348904975 46925010519045509023357463)
          ·
            refine ⟨70387515778568263535036195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46925010519045509023357463 70387515778568263535036195)
            ·
              refine ⟨105581273667852395302554293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70387515778568263535036195 105581273667852395302554293)
              ·
                refine ⟨9898244406361162059614465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105581273667852395302554293 9898244406361162059614465)
                ·
                  refine ⟨7423683304770871544710849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9898244406361162059614465 7423683304770871544710849)
                  ·
                    refine ⟨5567762478578153658533137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7423683304770871544710849 5567762478578153658533137)
                    ·
                      refine ⟨4175821858933615243899853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567762478578153658533137 4175821858933615243899853)
                      ·
                        rfl

theorem cell23_8132384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_8132384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132384 prefixEnd_8132384 := by exact prefixLift 8132384
  have htrace : WordTrace (prefixWord ++ tailWord_8132384) baseStart_8132384 baseEnd_8132384 := by
    simpa [prefixWord, tailWord_8132384, baseEnd_8132384] using wordTrace_append hprefix tailTrace_8132384
  have hstable : (prefixWord ++ tailWord_8132384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132384).length < 2 ^ (prefixWord ++ tailWord_8132384).sum := by decide
  have hdescent : baseEnd_8132384 < baseStart_8132384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132458 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_8132458 : Nat := 118140960795 + 8132458 * 2 ^ 59
def prefixEnd_8132458 : Nat := 4983230072969 + 3 ^ 40 * 8132458 * 2
def baseEnd_8132458 : Nat := 463984428500227550486057

theorem tailTrace_8132458 : CollatzResearch.WordTrace tailWord_8132458 prefixEnd_8132458 463984428500227550486057 := by
  unfold tailWord_8132458
  simp only [CollatzResearch.WordTrace]
  refine ⟨74153777792875263523619507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197743407447667369396318685 74153777792875263523619507)
  ·
    refine ⟨111230666689312895285429261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74153777792875263523619507 111230666689312895285429261)
    ·
      refine ⟨41711500008492335732035973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111230666689312895285429261 41711500008492335732035973)
      ·
        refine ⟨7820906251592312949756745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41711500008492335732035973 7820906251592312949756745)
        ·
          refine ⟨5865679688694234712317559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7820906251592312949756745 5865679688694234712317559)
          ·
            refine ⟨8798519533041352068476339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865679688694234712317559 8798519533041352068476339)
            ·
              refine ⟨13197779299562028102714509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798519533041352068476339 13197779299562028102714509)
              ·
                refine ⟨4949167237335760538517941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13197779299562028102714509 4949167237335760538517941)
                ·
                  refine ⟨463984428500227550486057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4949167237335760538517941 463984428500227550486057)
                  ·
                    rfl

theorem cell23_8132458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_8132458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132458 prefixEnd_8132458 := by exact prefixLift 8132458
  have htrace : WordTrace (prefixWord ++ tailWord_8132458) baseStart_8132458 baseEnd_8132458 := by
    simpa [prefixWord, tailWord_8132458, baseEnd_8132458] using wordTrace_append hprefix tailTrace_8132458
  have hstable : (prefixWord ++ tailWord_8132458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132458).length < 2 ^ (prefixWord ++ tailWord_8132458).sum := by decide
  have hdescent : baseEnd_8132458 < baseStart_8132458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132480 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 6]
def baseStart_8132480 : Nat := 118140960795 + 8132480 * 2 ^ 59
def prefixEnd_8132480 : Nat := 4983230072969 + 3 ^ 40 * 8132480 * 2
def baseEnd_8132480 : Nat := 463985683675160763144379

theorem tailTrace_8132480 : CollatzResearch.WordTrace tailWord_8132480 prefixEnd_8132480 463985683675160763144379 := by
  unfold tailWord_8132480
  simp only [CollatzResearch.WordTrace]
  refine ⟨148307956788710675925889447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197743942384947567901185929 148307956788710675925889447)
  ·
    refine ⟨222461935183066013888834171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148307956788710675925889447 222461935183066013888834171)
    ·
      refine ⟨333692902774599020833251257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222461935183066013888834171 333692902774599020833251257)
      ·
        refine ⟨250269677080949265624938443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333692902774599020833251257 250269677080949265624938443)
        ·
          refine ⟨375404515621423898437407665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250269677080949265624938443 375404515621423898437407665)
          ·
            refine ⟨281553386716067923828055749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375404515621423898437407665 281553386716067923828055749)
            ·
              refine ⟨52791260009262735717760453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281553386716067923828055749 52791260009262735717760453)
              ·
                refine ⟨9898361251736762947080085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52791260009262735717760453 9898361251736762947080085)
                ·
                  refine ⟨463985683675160763144379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9898361251736762947080085 463985683675160763144379)
                  ·
                    rfl

theorem cell23_8132480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_8132480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132480 prefixEnd_8132480 := by exact prefixLift 8132480
  have htrace : WordTrace (prefixWord ++ tailWord_8132480) baseStart_8132480 baseEnd_8132480 := by
    simpa [prefixWord, tailWord_8132480, baseEnd_8132480] using wordTrace_append hprefix tailTrace_8132480
  have hstable : (prefixWord ++ tailWord_8132480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132480).length < 2 ^ (prefixWord ++ tailWord_8132480).sum := by decide
  have hdescent : baseEnd_8132480 < baseStart_8132480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132484 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_8132484 : Nat := 118140960795 + 8132484 * 2 ^ 59
def prefixEnd_8132484 : Nat := 4983230072969 + 3 ^ 40 * 8132484 * 2
def baseEnd_8132484 : Nat := 1391957735666354950883131

theorem tailTrace_8132484 : CollatzResearch.WordTrace tailWord_8132484 prefixEnd_8132484 1391957735666354950883131 := by
  unfold tailWord_8132484
  simp only [CollatzResearch.WordTrace]
  refine ⟨148308029734703430267462253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197744039646271240356616337 148308029734703430267462253)
  ·
    refine ⟨55615511150513786350298345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148308029734703430267462253 55615511150513786350298345)
    ·
      refine ⟨41711633362885339762723759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55615511150513786350298345 41711633362885339762723759)
      ·
        refine ⟨62567450044328009644085639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41711633362885339762723759 62567450044328009644085639)
        ·
          refine ⟨93851175066492014466128459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62567450044328009644085639 93851175066492014466128459)
          ·
            refine ⟨140776762599738021699192689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93851175066492014466128459 140776762599738021699192689)
            ·
              refine ⟨105582571949803516274394517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140776762599738021699192689 105582571949803516274394517)
              ·
                refine ⟨4949183060147039825362243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105582571949803516274394517 4949183060147039825362243)
                ·
                  refine ⟨7423774590220559738043365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949183060147039825362243 7423774590220559738043365)
                  ·
                    refine ⟨1391957735666354950883131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423774590220559738043365 1391957735666354950883131)
                    ·
                      rfl

theorem cell23_8132484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_8132484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132484 prefixEnd_8132484 := by exact prefixLift 8132484
  have htrace : WordTrace (prefixWord ++ tailWord_8132484) baseStart_8132484 baseEnd_8132484 := by
    simpa [prefixWord, tailWord_8132484, baseEnd_8132484] using wordTrace_append hprefix tailTrace_8132484
  have hstable : (prefixWord ++ tailWord_8132484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132484).length < 2 ^ (prefixWord ++ tailWord_8132484).sum := by decide
  have hdescent : baseEnd_8132484 < baseStart_8132484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132497 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 6]
def baseStart_8132497 : Nat := 118140960795 + 8132497 * 2 ^ 59
def prefixEnd_8132497 : Nat := 4983230072969 + 3 ^ 40 * 8132497 * 2
def baseEnd_8132497 : Nat := 463986653583063700198537

theorem tailTrace_8132497 : CollatzResearch.WordTrace tailWord_8132497 prefixEnd_8132497 463986653583063700198537 := by
  unfold tailWord_8132497
  simp only [CollatzResearch.WordTrace]
  refine ⟨296616533618359763755147745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197744355745573175836765163 296616533618359763755147745)
  ·
    refine ⟨222462400213769822816360809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296616533618359763755147745 222462400213769822816360809)
    ·
      refine ⟨166846800160327367112270607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222462400213769822816360809 166846800160327367112270607)
      ·
        refine ⟨250270200240491050668405911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166846800160327367112270607 250270200240491050668405911)
        ·
          refine ⟨375405300360736576002608867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250270200240491050668405911 375405300360736576002608867)
          ·
            refine ⟨563107950541104864003913301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375405300360736576002608867 563107950541104864003913301)
            ·
              refine ⟨6598921295403572625045859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 563107950541104864003913301 6598921295403572625045859)
              ·
                refine ⟨9898381943105358937568789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598921295403572625045859 9898381943105358937568789)
                ·
                  refine ⟨463986653583063700198537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9898381943105358937568789 463986653583063700198537)
                  ·
                    rfl

theorem cell23_8132497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 6].length) (baseStart_8132497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132497 prefixEnd_8132497 := by exact prefixLift 8132497
  have htrace : WordTrace (prefixWord ++ tailWord_8132497) baseStart_8132497 baseEnd_8132497 := by
    simpa [prefixWord, tailWord_8132497, baseEnd_8132497] using wordTrace_append hprefix tailTrace_8132497
  have hstable : (prefixWord ++ tailWord_8132497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132497).length < 2 ^ (prefixWord ++ tailWord_8132497).sum := by decide
  have hdescent : baseEnd_8132497 < baseStart_8132497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132517 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 1, 5, 2]
def baseStart_8132517 : Nat := 118140960795 + 8132517 * 2 ^ 59
def prefixEnd_8132517 : Nat := 4983230072969 + 3 ^ 40 * 8132517 * 2
def baseEnd_8132517 : Nat := 4175890151860663223536741

theorem tailTrace_8132517 : CollatzResearch.WordTrace tailWord_8132517 prefixEnd_8132517 4175890151860663223536741 := by
  unfold tailWord_8132517
  simp only [CollatzResearch.WordTrace]
  refine ⟨296617263078287307170875805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197744842052191538113917203 296617263078287307170875805)
  ·
    refine ⟨111231473654357740189078427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296617263078287307170875805 111231473654357740189078427)
    ·
      refine ⟨166847210481536610283617641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111231473654357740189078427 166847210481536610283617641)
      ·
        refine ⟨125135407861152457712713231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166847210481536610283617641 125135407861152457712713231)
        ·
          refine ⟨187703111791728686569069847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125135407861152457712713231 187703111791728686569069847)
          ·
            refine ⟨281554667687593029853604771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187703111791728686569069847 281554667687593029853604771)
            ·
              refine ⟨422332001531389544780407157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281554667687593029853604771 422332001531389544780407157)
              ·
                refine ⟨39593625143567769823163171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422332001531389544780407157 39593625143567769823163171)
                ·
                  refine ⟨59390437715351654734744757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39593625143567769823163171 59390437715351654734744757)
                  ·
                    refine ⟨5567853535814217631382321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59390437715351654734744757 5567853535814217631382321)
                    ·
                      refine ⟨4175890151860663223536741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567853535814217631382321 4175890151860663223536741)
                      ·
                        rfl

theorem cell23_8132517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_8132517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132517 prefixEnd_8132517 := by exact prefixLift 8132517
  have htrace : WordTrace (prefixWord ++ tailWord_8132517) baseStart_8132517 baseEnd_8132517 := by
    simpa [prefixWord, tailWord_8132517, baseEnd_8132517] using wordTrace_append hprefix tailTrace_8132517
  have hstable : (prefixWord ++ tailWord_8132517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132517).length < 2 ^ (prefixWord ++ tailWord_8132517).sum := by decide
  have hdescent : baseEnd_8132517 < baseStart_8132517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132560 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_8132560 : Nat := 118140960795 + 8132560 * 2 ^ 59
def prefixEnd_8132560 : Nat := 4983230072969 + 3 ^ 40 * 8132560 * 2
def baseEnd_8132560 : Nat := 4175912231528806555299043

theorem tailTrace_8132560 : CollatzResearch.WordTrace tailWord_8132560 prefixEnd_8132560 4175912231528806555299043 := by
  unfold tailWord_8132560
  simp only [CollatzResearch.WordTrace]
  refine ⟨148309415708565762757345567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197745887611421017009794089 148309415708565762757345567)
  ·
    refine ⟨222464123562848644136018351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148309415708565762757345567 222464123562848644136018351)
    ·
      refine ⟨333696185344272966204027527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222464123562848644136018351 333696185344272966204027527)
      ·
        refine ⟨500544278016409449306041291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333696185344272966204027527 500544278016409449306041291)
        ·
          refine ⟨750816417024614173959061937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500544278016409449306041291 750816417024614173959061937)
          ·
            refine ⟨563112312768460630469296453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750816417024614173959061937 563112312768460630469296453)
            ·
              refine ⟨105583558644086368212993085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 563112312768460630469296453 105583558644086368212993085)
              ·
                refine ⟨39593834491532388079872407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105583558644086368212993085 39593834491532388079872407)
                ·
                  refine ⟨59390751737298582119808611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39593834491532388079872407 59390751737298582119808611)
                  ·
                    refine ⟨89086127605947873179712917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59390751737298582119808611 89086127605947873179712917)
                    ·
                      refine ⟨4175912231528806555299043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89086127605947873179712917 4175912231528806555299043)
                      ·
                        rfl

theorem cell23_8132560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_8132560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132560 prefixEnd_8132560 := by exact prefixLift 8132560
  have htrace : WordTrace (prefixWord ++ tailWord_8132560) baseStart_8132560 baseEnd_8132560 := by
    simpa [prefixWord, tailWord_8132560, baseEnd_8132560] using wordTrace_append hprefix tailTrace_8132560
  have hstable : (prefixWord ++ tailWord_8132560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132560).length < 2 ^ (prefixWord ++ tailWord_8132560).sum := by decide
  have hdescent : baseEnd_8132560 < baseStart_8132560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132564 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_8132564 : Nat := 118140960795 + 8132564 * 2 ^ 59
def prefixEnd_8132564 : Nat := 4983230072969 + 3 ^ 40 * 8132564 * 2
def baseEnd_8132564 : Nat := 4175914285451424539649025

theorem tailTrace_8132564 : CollatzResearch.WordTrace tailWord_8132564 prefixEnd_8132564 4175914285451424539649025 := by
  unfold tailWord_8132564
  simp only [CollatzResearch.WordTrace]
  refine ⟨148309488654558517098918373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197745984872744689465224497 148309488654558517098918373)
  ·
    refine ⟨27808029122729721956047195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148309488654558517098918373 27808029122729721956047195)
    ·
      refine ⟨41712043684094582934070793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27808029122729721956047195 41712043684094582934070793)
      ·
        refine ⟨31284032763070937200553095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41712043684094582934070793 31284032763070937200553095)
        ·
          refine ⟨46926049144606405800829643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31284032763070937200553095 46926049144606405800829643)
          ·
            refine ⟨70389073716909608701244465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46926049144606405800829643 70389073716909608701244465)
            ·
              refine ⟨52791805287682206525933349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70389073716909608701244465 52791805287682206525933349)
              ·
                refine ⟨9898463491440413723612503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52791805287682206525933349 9898463491440413723612503)
                ·
                  refine ⟨14847695237160620585418755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9898463491440413723612503 14847695237160620585418755)
                  ·
                    refine ⟨22271542855740930878128133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14847695237160620585418755 22271542855740930878128133)
                    ·
                      refine ⟨4175914285451424539649025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22271542855740930878128133 4175914285451424539649025)
                      ·
                        rfl

theorem cell23_8132564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_8132564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132564 prefixEnd_8132564 := by exact prefixLift 8132564
  have htrace : WordTrace (prefixWord ++ tailWord_8132564) baseStart_8132564 baseEnd_8132564 := by
    simpa [prefixWord, tailWord_8132564, baseEnd_8132564] using wordTrace_append hprefix tailTrace_8132564
  have hstable : (prefixWord ++ tailWord_8132564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132564).length < 2 ^ (prefixWord ++ tailWord_8132564).sum := by decide
  have hdescent : baseEnd_8132564 < baseStart_8132564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132567 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_8132567 : Nat := 118140960795 + 8132567 * 2 ^ 59
def prefixEnd_8132567 : Nat := 4983230072969 + 3 ^ 40 * 8132567 * 2
def baseEnd_8132567 : Nat := 4175915825893388027911511

theorem tailTrace_8132567 : CollatzResearch.WordTrace tailWord_8132567 prefixEnd_8132567 4175915825893388027911511 := by
  unfold tailWord_8132567
  simp only [CollatzResearch.WordTrace]
  refine ⟨296619086728106165710195955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197746057818737443806797303 296619086728106165710195955)
  ·
    refine ⟨444928630092159248565293933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296619086728106165710195955 444928630092159248565293933)
    ·
      refine ⟨166848236284559718211985225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444928630092159248565293933 166848236284559718211985225)
      ·
        refine ⟨125136177213419788658988919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166848236284559718211985225 125136177213419788658988919)
        ·
          refine ⟨187704265820129682988483379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125136177213419788658988919 187704265820129682988483379)
          ·
            refine ⟨281556398730194524482725069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187704265820129682988483379 281556398730194524482725069)
            ·
              refine ⟨105583649523822946681021901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281556398730194524482725069 105583649523822946681021901)
              ·
                refine ⟨39593868571433605005383213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105583649523822946681021901 39593868571433605005383213)
                ·
                  refine ⟨14847700714287601877018705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39593868571433605005383213 14847700714287601877018705)
                  ·
                    refine ⟨11135775535715701407764029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14847700714287601877018705 11135775535715701407764029)
                    ·
                      refine ⟨4175915825893388027911511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11135775535715701407764029 4175915825893388027911511)
                      ·
                        rfl

theorem cell23_8132567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_8132567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132567 prefixEnd_8132567 := by exact prefixLift 8132567
  have htrace : WordTrace (prefixWord ++ tailWord_8132567) baseStart_8132567 baseEnd_8132567 := by
    simpa [prefixWord, tailWord_8132567, baseEnd_8132567] using wordTrace_append hprefix tailTrace_8132567
  have hstable : (prefixWord ++ tailWord_8132567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132567).length < 2 ^ (prefixWord ++ tailWord_8132567).sum := by decide
  have hdescent : baseEnd_8132567 < baseStart_8132567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132577 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_8132577 : Nat := 118140960795 + 8132577 * 2 ^ 59
def prefixEnd_8132577 : Nat := 4983230072969 + 3 ^ 40 * 8132577 * 2
def baseEnd_8132577 : Nat := 4175920960699932988786465

theorem tailTrace_8132577 : CollatzResearch.WordTrace tailWord_8132577 prefixEnd_8132577 4175920960699932988786465 := by
  unfold tailWord_8132577
  simp only [CollatzResearch.WordTrace]
  refine ⟨296619451458069937418059985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197746300972046624945373323 296619451458069937418059985)
  ·
    refine ⟨222464588593552453063544989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296619451458069937418059985 222464588593552453063544989)
    ·
      refine ⟨83424220722582169898829371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222464588593552453063544989 83424220722582169898829371)
      ·
        refine ⟨125136331083873254848244057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83424220722582169898829371 125136331083873254848244057)
        ·
          refine ⟨93852248312904941136183043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125136331083873254848244057 93852248312904941136183043)
          ·
            refine ⟨140778372469357411704274565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93852248312904941136183043 140778372469357411704274565)
            ·
              refine ⟨26395944838004514694551481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140778372469357411704274565 26395944838004514694551481)
              ·
                refine ⟨19796958628503386020913611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26395944838004514694551481 19796958628503386020913611)
                ·
                  refine ⟨29695437942755079031370417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19796958628503386020913611 29695437942755079031370417)
                  ·
                    refine ⟨22271578457066309273527813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29695437942755079031370417 22271578457066309273527813)
                    ·
                      refine ⟨4175920960699932988786465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22271578457066309273527813 4175920960699932988786465)
                      ·
                        rfl

theorem cell23_8132577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_8132577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132577 prefixEnd_8132577 := by exact prefixLift 8132577
  have htrace : WordTrace (prefixWord ++ tailWord_8132577) baseStart_8132577 baseEnd_8132577 := by
    simpa [prefixWord, tailWord_8132577, baseEnd_8132577] using wordTrace_append hprefix tailTrace_8132577
  have hstable : (prefixWord ++ tailWord_8132577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132577).length < 2 ^ (prefixWord ++ tailWord_8132577).sum := by decide
  have hdescent : baseEnd_8132577 < baseStart_8132577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132600 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_8132600 : Nat := 118140960795 + 8132600 * 2 ^ 59
def prefixEnd_8132600 : Nat := 4983230072969 + 3 ^ 40 * 8132600 * 2
def baseEnd_8132600 : Nat := 1391977590251662132932953

theorem tailTrace_8132600 : CollatzResearch.WordTrace tailWord_8132600 prefixEnd_8132600 1391977590251662132932953 := by
  unfold tailWord_8132600
  simp only [CollatzResearch.WordTrace]
  refine ⟨148310145168493306173073627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197746860224657741564098169 148310145168493306173073627)
  ·
    refine ⟨222465217752739959259610441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148310145168493306173073627 222465217752739959259610441)
    ·
      refine ⟨166848913314554969444707831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222465217752739959259610441 166848913314554969444707831)
      ·
        refine ⟨250273369971832454167061747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166848913314554969444707831 250273369971832454167061747)
        ·
          refine ⟨375410054957748681250592621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250273369971832454167061747 375410054957748681250592621)
          ·
            refine ⟨140778770609155755468972233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375410054957748681250592621 140778770609155755468972233)
            ·
              refine ⟨105584077956866816601729175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140778770609155755468972233 105584077956866816601729175)
              ·
                refine ⟨158376116935300224902593763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105584077956866816601729175 158376116935300224902593763)
                ·
                  refine ⟨237564175402950337353890645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158376116935300224902593763 237564175402950337353890645)
                  ·
                    refine ⟨1391977590251662132932953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 237564175402950337353890645 1391977590251662132932953)
                    ·
                      rfl

theorem cell23_8132600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_8132600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132600 prefixEnd_8132600 := by exact prefixLift 8132600
  have htrace : WordTrace (prefixWord ++ tailWord_8132600) baseStart_8132600 baseEnd_8132600 := by
    simpa [prefixWord, tailWord_8132600, baseEnd_8132600] using wordTrace_append hprefix tailTrace_8132600
  have hstable : (prefixWord ++ tailWord_8132600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132600).length < 2 ^ (prefixWord ++ tailWord_8132600).sum := by decide
  have hdescent : baseEnd_8132600 < baseStart_8132600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132665 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 2, 1, 3]
def baseStart_8132665 : Nat := 118140960795 + 8132665 * 2 ^ 59
def prefixEnd_8132665 : Nat := 4983230072969 + 3 ^ 40 * 8132665 * 2
def baseEnd_8132665 : Nat := 4175966146997528644486061

theorem tailTrace_8132665 : CollatzResearch.WordTrace tailWord_8132665 prefixEnd_8132665 4175966146997528644486061 := by
  unfold tailWord_8132665
  simp only [CollatzResearch.WordTrace]
  refine ⟨296622661081751128447263449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197748440721167418964842299 296622661081751128447263449)
  ·
    refine ⟨222466995811313346335447587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296622661081751128447263449 222466995811313346335447587)
    ·
      refine ⟨333700493716970019503171381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222466995811313346335447587 333700493716970019503171381)
      ·
        refine ⟨31284421285965939328422317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333700493716970019503171381 31284421285965939328422317)
        ·
          refine ⟨11731657982237227248158369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31284421285965939328422317 11731657982237227248158369)
          ·
            refine ⟨8798743486677920436118777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11731657982237227248158369 8798743486677920436118777)
            ·
              refine ⟨6599057615008440327089083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8798743486677920436118777 6599057615008440327089083)
              ·
                refine ⟨9898586422512660490633625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6599057615008440327089083 9898586422512660490633625)
                ·
                  refine ⟨7423939816884495367975219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9898586422512660490633625 7423939816884495367975219)
                  ·
                    refine ⟨11135909725326743051962829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7423939816884495367975219 11135909725326743051962829)
                    ·
                      refine ⟨4175966146997528644486061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11135909725326743051962829 4175966146997528644486061)
                      ·
                        rfl

theorem cell23_8132665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_8132665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132665 prefixEnd_8132665 := by exact prefixLift 8132665
  have htrace : WordTrace (prefixWord ++ tailWord_8132665) baseStart_8132665 baseEnd_8132665 := by
    simpa [prefixWord, tailWord_8132665, baseEnd_8132665] using wordTrace_append hprefix tailTrace_8132665
  have hstable : (prefixWord ++ tailWord_8132665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132665).length < 2 ^ (prefixWord ++ tailWord_8132665).sum := by decide
  have hdescent : baseEnd_8132665 < baseStart_8132665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132687 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_8132687 : Nat := 118140960795 + 8132687 * 2 ^ 59
def prefixEnd_8132687 : Nat := 4983230072969 + 3 ^ 40 * 8132687 * 2
def baseEnd_8132687 : Nat := 4175977443571927558410959

theorem tailTrace_8132687 : CollatzResearch.WordTrace tailWord_8132687 prefixEnd_8132687 4175977443571927558410959 := by
  unfold tailWord_8132687
  simp only [CollatzResearch.WordTrace]
  refine ⟨296623463487671426204564315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197748975658447617469709543 296623463487671426204564315)
  ·
    refine ⟨444935195231507139306846473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296623463487671426204564315 444935195231507139306846473)
    ·
      refine ⟨333701396423630354480134855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444935195231507139306846473 333701396423630354480134855)
      ·
        refine ⟨500552094635445531720202283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333701396423630354480134855 500552094635445531720202283)
        ·
          refine ⟨750828141953168297580303425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500552094635445531720202283 750828141953168297580303425)
          ·
            refine ⟨563121106464876223185227569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750828141953168297580303425 563121106464876223185227569)
            ·
              refine ⟨422340829848657167388920677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563121106464876223185227569 422340829848657167388920677)
              ·
                refine ⟨79188905596623218885422627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422340829848657167388920677 79188905596623218885422627)
                ·
                  refine ⟨118783358394934828328133941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79188905596623218885422627 118783358394934828328133941)
                  ·
                    refine ⟨11135939849525140155762557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118783358394934828328133941 11135939849525140155762557)
                    ·
                      refine ⟨4175977443571927558410959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11135939849525140155762557 4175977443571927558410959)
                      ·
                        rfl

theorem cell23_8132687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_8132687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132687 prefixEnd_8132687 := by exact prefixLift 8132687
  have htrace : WordTrace (prefixWord ++ tailWord_8132687) baseStart_8132687 baseEnd_8132687 := by
    simpa [prefixWord, tailWord_8132687, baseEnd_8132687] using wordTrace_append hprefix tailTrace_8132687
  have hstable : (prefixWord ++ tailWord_8132687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132687).length < 2 ^ (prefixWord ++ tailWord_8132687).sum := by decide
  have hdescent : baseEnd_8132687 < baseStart_8132687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132741 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_8132741 : Nat := 118140960795 + 8132741 * 2 ^ 59
def prefixEnd_8132741 : Nat := 4983230072969 + 3 ^ 40 * 8132741 * 2
def baseEnd_8132741 : Nat := 1392001723842423449045237

theorem tailTrace_8132741 : CollatzResearch.WordTrace tailWord_8132741 prefixEnd_8132741 1392001723842423449045237 := by
  unfold tailWord_8132741
  simp only [CollatzResearch.WordTrace]
  refine ⟨296625433029475793427030077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197750288686317195618020051 296625433029475793427030077)
  ·
    refine ⟨111234537386053422535136279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296625433029475793427030077 111234537386053422535136279)
    ·
      refine ⟨166851806079080133802704419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111234537386053422535136279 166851806079080133802704419)
      ·
        refine ⟨250277709118620200704056629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166851806079080133802704419 250277709118620200704056629)
        ·
          refine ⟨23463535229870643816005309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250277709118620200704056629 23463535229870643816005309)
          ·
            refine ⟨8798825711201491431001991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23463535229870643816005309 8798825711201491431001991)
            ·
              refine ⟨13198238566802237146502987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798825711201491431001991 13198238566802237146502987)
              ·
                refine ⟨19797357850203355719754481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13198238566802237146502987 19797357850203355719754481)
                ·
                  refine ⟨14848018387652516789815861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19797357850203355719754481 14848018387652516789815861)
                  ·
                    refine ⟨1392001723842423449045237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14848018387652516789815861 1392001723842423449045237)
                    ·
                      rfl

theorem cell23_8132741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_8132741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132741 prefixEnd_8132741 := by exact prefixLift 8132741
  have htrace : WordTrace (prefixWord ++ tailWord_8132741) baseStart_8132741 baseEnd_8132741 := by
    simpa [prefixWord, tailWord_8132741, baseEnd_8132741] using wordTrace_append hprefix tailTrace_8132741
  have hstable : (prefixWord ++ tailWord_8132741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132741).length < 2 ^ (prefixWord ++ tailWord_8132741).sum := by decide
  have hdescent : baseEnd_8132741 < baseStart_8132741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132757 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_8132757 : Nat := 118140960795 + 8132757 * 2 ^ 59
def prefixEnd_8132757 : Nat := 4983230072969 + 3 ^ 40 * 8132757 * 2
def baseEnd_8132757 : Nat := 4176013387217742284535637

theorem tailTrace_8132757 : CollatzResearch.WordTrace tailWord_8132757 prefixEnd_8132757 4176013387217742284535637 := by
  unfold tailWord_8132757
  simp only [CollatzResearch.WordTrace]
  refine ⟨296626016597417828159612525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197750677731611885439741683 296626016597417828159612525)
  ·
    refine ⟨111234756224031685559854697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296626016597417828159612525 111234756224031685559854697)
    ·
      refine ⟨83426067168023764169891023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111234756224031685559854697 83426067168023764169891023)
      ·
        refine ⟨125139100752035646254836535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83426067168023764169891023 125139100752035646254836535)
        ·
          refine ⟨187708651128053469382254803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125139100752035646254836535 187708651128053469382254803)
          ·
            refine ⟨281562976692080204073382205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187708651128053469382254803 281562976692080204073382205)
            ·
              refine ⟨105586116259530076527518327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281562976692080204073382205 105586116259530076527518327)
              ·
                refine ⟨158379174389295114791277491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105586116259530076527518327 158379174389295114791277491)
                ·
                  refine ⟨237568761583942672186916237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158379174389295114791277491 237568761583942672186916237)
                  ·
                    refine ⟨89088285593978502070093589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237568761583942672186916237 89088285593978502070093589)
                    ·
                      refine ⟨4176013387217742284535637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89088285593978502070093589 4176013387217742284535637)
                      ·
                        rfl

theorem cell23_8132757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_8132757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132757 prefixEnd_8132757 := by exact prefixLift 8132757
  have htrace : WordTrace (prefixWord ++ tailWord_8132757) baseStart_8132757 baseEnd_8132757 := by
    simpa [prefixWord, tailWord_8132757, baseEnd_8132757] using wordTrace_append hprefix tailTrace_8132757
  have hstable : (prefixWord ++ tailWord_8132757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132757).length < 2 ^ (prefixWord ++ tailWord_8132757).sum := by decide
  have hdescent : baseEnd_8132757 < baseStart_8132757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132781 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_8132781 : Nat := 118140960795 + 8132781 * 2 ^ 59
def prefixEnd_8132781 : Nat := 4983230072969 + 3 ^ 40 * 8132781 * 2
def baseEnd_8132781 : Nat := 4176025710753450190635527

theorem tailTrace_8132781 : CollatzResearch.WordTrace tailWord_8132781 prefixEnd_8132781 4176025710753450190635527 := by
  unfold tailWord_8132781
  simp only [CollatzResearch.WordTrace]
  refine ⟨296626891949330880258486197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197751261299553920172324131 296626891949330880258486197)
  ·
    refine ⟨27808771120249770024233081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296626891949330880258486197 27808771120249770024233081)
    ·
      refine ⟨20856578340187327518174811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27808771120249770024233081 20856578340187327518174811)
      ·
        refine ⟨31284867510280991277262217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20856578340187327518174811 31284867510280991277262217)
        ·
          refine ⟨23463650632710743457946663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31284867510280991277262217 23463650632710743457946663)
          ·
            refine ⟨35195475949066115186919995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23463650632710743457946663 35195475949066115186919995)
            ·
              refine ⟨52793213923599172780379993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35195475949066115186919995 52793213923599172780379993)
              ·
                refine ⟨39594910442699379585284995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52793213923599172780379993 39594910442699379585284995)
                ·
                  refine ⟨59392365664049069377927493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39594910442699379585284995 59392365664049069377927493)
                  ·
                    refine ⟨11136068562009200508361405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59392365664049069377927493 11136068562009200508361405)
                    ·
                      refine ⟨4176025710753450190635527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136068562009200508361405 4176025710753450190635527)
                      ·
                        rfl

theorem cell23_8132781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_8132781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132781 prefixEnd_8132781 := by exact prefixLift 8132781
  have htrace : WordTrace (prefixWord ++ tailWord_8132781) baseStart_8132781 baseEnd_8132781 := by
    simpa [prefixWord, tailWord_8132781, baseEnd_8132781] using wordTrace_append hprefix tailTrace_8132781
  have hstable : (prefixWord ++ tailWord_8132781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132781).length < 2 ^ (prefixWord ++ tailWord_8132781).sum := by decide
  have hdescent : baseEnd_8132781 < baseStart_8132781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132787 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_8132787 : Nat := 118140960795 + 8132787 * 2 ^ 59
def prefixEnd_8132787 : Nat := 4983230072969 + 3 ^ 40 * 8132787 * 2
def baseEnd_8132787 : Nat := 4176028791637377167160499

theorem tailTrace_8132787 : CollatzResearch.WordTrace tailWord_8132787 prefixEnd_8132787 4176028791637377167160499 := by
  unfold tailWord_8132787
  simp only [CollatzResearch.WordTrace]
  refine ⟨296627110787309143283204615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197751407191539428855469743 296627110787309143283204615)
  ·
    refine ⟨444940666180963714924806923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296627110787309143283204615 444940666180963714924806923)
    ·
      refine ⟨667410999271445572387210385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444940666180963714924806923 667410999271445572387210385)
      ·
        refine ⟨500558249453584179290407789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667410999271445572387210385 500558249453584179290407789)
        ·
          refine ⟨187709343545094067233902921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500558249453584179290407789 187709343545094067233902921)
          ·
            refine ⟨140782007658820550425427191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187709343545094067233902921 140782007658820550425427191)
            ·
              refine ⟨211173011488230825638140787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140782007658820550425427191 211173011488230825638140787)
              ·
                refine ⟨316759517232346238457211181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211173011488230825638140787 316759517232346238457211181)
                ·
                  refine ⟨118784818962129839421454193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316759517232346238457211181 118784818962129839421454193)
                  ·
                    refine ⟨89088614221597379566090645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118784818962129839421454193 89088614221597379566090645)
                    ·
                      refine ⟨4176028791637377167160499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89088614221597379566090645 4176028791637377167160499)
                      ·
                        rfl

theorem cell23_8132787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_8132787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132787 prefixEnd_8132787 := by exact prefixLift 8132787
  have htrace : WordTrace (prefixWord ++ tailWord_8132787) baseStart_8132787 baseEnd_8132787 := by
    simpa [prefixWord, tailWord_8132787, baseEnd_8132787] using wordTrace_append hprefix tailTrace_8132787
  have hstable : (prefixWord ++ tailWord_8132787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132787).length < 2 ^ (prefixWord ++ tailWord_8132787).sum := by decide
  have hdescent : baseEnd_8132787 < baseStart_8132787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132835 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 6]
def baseStart_8132835 : Nat := 118140960795 + 8132835 * 2 ^ 59
def prefixEnd_8132835 : Nat := 4983230072969 + 3 ^ 40 * 8132835 * 2
def baseEnd_8132835 : Nat := 464005937634310331040031

theorem tailTrace_8132835 : CollatzResearch.WordTrace tailWord_8132835 prefixEnd_8132835 464005937634310331040031 := by
  unfold tailWord_8132835
  simp only [CollatzResearch.WordTrace]
  refine ⟨296628861491135247480951959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197752574327423498320634639 296628861491135247480951959)
  ·
    refine ⟨444943292236702871221427939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296628861491135247480951959 444943292236702871221427939)
    ·
      refine ⟨667414938355054306832141909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444943292236702871221427939 667414938355054306832141909)
      ·
        refine ⟨7821268808848292658189163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 667414938355054306832141909 7821268808848292658189163)
        ·
          refine ⟨11731903213272438987283745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821268808848292658189163 11731903213272438987283745)
          ·
            refine ⟨8798927409954329240462809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11731903213272438987283745 8798927409954329240462809)
            ·
              refine ⟨6599195557465746930347107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8798927409954329240462809 6599195557465746930347107)
              ·
                refine ⟨9898793336198620395520661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6599195557465746930347107 9898793336198620395520661)
                ·
                  refine ⟨464005937634310331040031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9898793336198620395520661 464005937634310331040031)
                  ·
                    rfl

theorem cell23_8132835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 6].length) (baseStart_8132835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132835 prefixEnd_8132835 := by exact prefixLift 8132835
  have htrace : WordTrace (prefixWord ++ tailWord_8132835) baseStart_8132835 baseEnd_8132835 := by
    simpa [prefixWord, tailWord_8132835, baseEnd_8132835] using wordTrace_append hprefix tailTrace_8132835
  have hstable : (prefixWord ++ tailWord_8132835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132835).length < 2 ^ (prefixWord ++ tailWord_8132835).sum := by decide
  have hdescent : baseEnd_8132835 < baseStart_8132835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132844 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_8132844 : Nat := 118140960795 + 8132844 * 2 ^ 59
def prefixEnd_8132844 : Nat := 4983230072969 + 3 ^ 40 * 8132844 * 2
def baseEnd_8132844 : Nat := 1392019353344894481382579

theorem tailTrace_8132844 : CollatzResearch.WordTrace tailWord_8132844 prefixEnd_8132844 1392019353344894481382579 := by
  unfold tailWord_8132844
  simp only [CollatzResearch.WordTrace]
  refine ⟨148314594874051321009014793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197752793165401761345353057 148314594874051321009014793)
  ·
    refine ⟨111235946155538490756761095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148314594874051321009014793 111235946155538490756761095)
    ·
      refine ⟨166853919233307736135141643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111235946155538490756761095 166853919233307736135141643)
      ·
        refine ⟨250280878849961604202712465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166853919233307736135141643 250280878849961604202712465)
        ·
          refine ⟨187710659137471203152034349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250280878849961604202712465 187710659137471203152034349)
          ·
            refine ⟨70391497176551701182012881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187710659137471203152034349 70391497176551701182012881)
            ·
              refine ⟨52793622882413775886509661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70391497176551701182012881 52793622882413775886509661)
              ·
                refine ⟨19797608580905165957441123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52793622882413775886509661 19797608580905165957441123)
                ·
                  refine ⟨29696412871357748936161685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19797608580905165957441123 29696412871357748936161685)
                  ·
                    refine ⟨1392019353344894481382579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29696412871357748936161685 1392019353344894481382579)
                    ·
                      rfl

theorem cell23_8132844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_8132844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132844 prefixEnd_8132844 := by exact prefixLift 8132844
  have htrace : WordTrace (prefixWord ++ tailWord_8132844) baseStart_8132844 baseEnd_8132844 := by
    simpa [prefixWord, tailWord_8132844, baseEnd_8132844] using wordTrace_append hprefix tailTrace_8132844
  have hstable : (prefixWord ++ tailWord_8132844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132844).length < 2 ^ (prefixWord ++ tailWord_8132844).sum := by decide
  have hdescent : baseEnd_8132844 < baseStart_8132844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132864 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_8132864 : Nat := 118140960795 + 8132864 * 2 ^ 59
def prefixEnd_8132864 : Nat := 4983230072969 + 3 ^ 40 * 8132864 * 2
def baseEnd_8132864 : Nat := 4176068329647773365897645

theorem tailTrace_8132864 : CollatzResearch.WordTrace tailWord_8132864 prefixEnd_8132864 4176068329647773365897645 := by
  unfold tailWord_8132864
  simp only [CollatzResearch.WordTrace]
  refine ⟨148314959604015092716878823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197753279472020123622505097 148314959604015092716878823)
  ·
    refine ⟨222472439406022639075318235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148314959604015092716878823 222472439406022639075318235)
    ·
      refine ⟨333708659109033958612977353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222472439406022639075318235 333708659109033958612977353)
      ·
        refine ⟨250281494331775468959733015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333708659109033958612977353 250281494331775468959733015)
        ·
          refine ⟨375422241497663203439599523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250281494331775468959733015 375422241497663203439599523)
          ·
            refine ⟨563133362246494805159399285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375422241497663203439599523 563133362246494805159399285)
            ·
              refine ⟨52793752710608887983693683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 563133362246494805159399285 52793752710608887983693683)
              ·
                refine ⟨79190629065913331975540525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52793752710608887983693683 79190629065913331975540525)
                ·
                  refine ⟨29696485899717499490827697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79190629065913331975540525 29696485899717499490827697)
                  ·
                    refine ⟨22272364424788124618120773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29696485899717499490827697 22272364424788124618120773)
                    ·
                      refine ⟨4176068329647773365897645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22272364424788124618120773 4176068329647773365897645)
                      ·
                        rfl

theorem cell23_8132864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_8132864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132864 prefixEnd_8132864 := by exact prefixLift 8132864
  have htrace : WordTrace (prefixWord ++ tailWord_8132864) baseStart_8132864 baseEnd_8132864 := by
    simpa [prefixWord, tailWord_8132864, baseEnd_8132864] using wordTrace_append hprefix tailTrace_8132864
  have hstable : (prefixWord ++ tailWord_8132864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132864).length < 2 ^ (prefixWord ++ tailWord_8132864).sum := by decide
  have hdescent : baseEnd_8132864 < baseStart_8132864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132878 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_8132878 : Nat := 118140960795 + 8132878 * 2 ^ 59
def prefixEnd_8132878 : Nat := 4983230072969 + 3 ^ 40 * 8132878 * 2
def baseEnd_8132878 : Nat := 1392025172792312103707527

theorem tailTrace_8132878 : CollatzResearch.WordTrace tailWord_8132878 prefixEnd_8132878 1392025172792312103707527 := by
  unfold tailWord_8132878
  simp only [CollatzResearch.WordTrace]
  refine ⟨37078803728747433228095911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197753619886652977216511525 37078803728747433228095911)
  ·
    refine ⟨55618205593121149842143867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37078803728747433228095911 55618205593121149842143867)
    ·
      refine ⟨83427308389681724763215801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55618205593121149842143867 83427308389681724763215801)
      ·
        refine ⟨62570481292261293572411851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83427308389681724763215801 62570481292261293572411851)
        ·
          refine ⟨93855721938391940358617777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62570481292261293572411851 93855721938391940358617777)
          ·
            refine ⟨70391791453793955268963333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93855721938391940358617777 70391791453793955268963333)
            ·
              refine ⟨13198460897586366612930625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70391791453793955268963333 13198460897586366612930625)
              ·
                refine ⟨9898845673189774959697969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13198460897586366612930625 9898845673189774959697969)
                ·
                  refine ⟨7424134254892331219773477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9898845673189774959697969 7424134254892331219773477)
                  ·
                    refine ⟨1392025172792312103707527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7424134254892331219773477 1392025172792312103707527)
                    ·
                      rfl

theorem cell23_8132878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_8132878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132878 prefixEnd_8132878 := by exact prefixLift 8132878
  have htrace : WordTrace (prefixWord ++ tailWord_8132878) baseStart_8132878 baseEnd_8132878 := by
    simpa [prefixWord, tailWord_8132878, baseEnd_8132878] using wordTrace_append hprefix tailTrace_8132878
  have hstable : (prefixWord ++ tailWord_8132878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132878).length < 2 ^ (prefixWord ++ tailWord_8132878).sum := by decide
  have hdescent : baseEnd_8132878 < baseStart_8132878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132898 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_8132898 : Nat := 118140960795 + 8132898 * 2 ^ 59
def prefixEnd_8132898 : Nat := 4983230072969 + 3 ^ 40 * 8132898 * 2
def baseEnd_8132898 : Nat := 4176085787990026232872489

theorem tailTrace_8132898 : CollatzResearch.WordTrace tailWord_8132898 prefixEnd_8132898 4176085787990026232872489 := by
  unfold tailWord_8132898
  simp only [CollatzResearch.WordTrace]
  refine ⟨74157789822476752310123837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197754106193271339493663565 74157789822476752310123837)
  ·
    refine ⟨27809171183428782116296439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74157789822476752310123837 27809171183428782116296439)
    ·
      refine ⟨41713756775143173174444659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27809171183428782116296439 41713756775143173174444659)
      ·
        refine ⟨62570635162714759761666989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41713756775143173174444659 62570635162714759761666989)
        ·
          refine ⟨23463988186018034910625121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62570635162714759761666989 23463988186018034910625121)
          ·
            refine ⟨17597991139513526182968841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23463988186018034910625121 17597991139513526182968841)
            ·
              refine ⟨13198493354635144637226631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17597991139513526182968841 13198493354635144637226631)
              ·
                refine ⟨19797740031952716955839947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13198493354635144637226631 19797740031952716955839947)
                ·
                  refine ⟨29696610047929075433759921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19797740031952716955839947 29696610047929075433759921)
                  ·
                    refine ⟨22272457535946806575319941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29696610047929075433759921 22272457535946806575319941)
                    ·
                      refine ⟨4176085787990026232872489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22272457535946806575319941 4176085787990026232872489)
                      ·
                        rfl

theorem cell23_8132898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_8132898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132898 prefixEnd_8132898 := by exact prefixLift 8132898
  have htrace : WordTrace (prefixWord ++ tailWord_8132898) baseStart_8132898 baseEnd_8132898 := by
    simpa [prefixWord, tailWord_8132898, baseEnd_8132898] using wordTrace_append hprefix tailTrace_8132898
  have hstable : (prefixWord ++ tailWord_8132898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132898).length < 2 ^ (prefixWord ++ tailWord_8132898).sum := by decide
  have hdescent : baseEnd_8132898 < baseStart_8132898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132962 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_8132962 : Nat := 118140960795 + 8132962 * 2 ^ 59
def prefixEnd_8132962 : Nat := 4983230072969 + 3 ^ 40 * 8132962 * 2
def baseEnd_8132962 : Nat := 4176118650751913982472195

theorem tailTrace_8132962 : CollatzResearch.WordTrace tailWord_8132962 prefixEnd_8132962 4176118650751913982472195 := by
  unfold tailWord_8132962
  simp only [CollatzResearch.WordTrace]
  refine ⟨74158373390418787042706285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197755662374450098780550093 74158373390418787042706285)
  ·
    refine ⟨27809390021407045141014857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74158373390418787042706285 27809390021407045141014857)
    ·
      refine ⟨20857042516055283855761143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27809390021407045141014857 20857042516055283855761143)
      ·
        refine ⟨31285563774082925783641715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20857042516055283855761143 31285563774082925783641715)
        ·
          refine ⟨46928345661124388675462573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31285563774082925783641715 46928345661124388675462573)
          ·
            refine ⟨17598129622921645753298465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46928345661124388675462573 17598129622921645753298465)
            ·
              refine ⟨13198597217191234314973849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17598129622921645753298465 13198597217191234314973849)
              ·
                refine ⟨9898947912893425736230387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13198597217191234314973849 9898947912893425736230387)
                ·
                  refine ⟨14848421869340138604345581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9898947912893425736230387 14848421869340138604345581)
                  ·
                    refine ⟨5568158201002551976629593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14848421869340138604345581 5568158201002551976629593)
                    ·
                      refine ⟨4176118650751913982472195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568158201002551976629593 4176118650751913982472195)
                      ·
                        rfl

theorem cell23_8132962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_8132962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132962 prefixEnd_8132962 := by exact prefixLift 8132962
  have htrace : WordTrace (prefixWord ++ tailWord_8132962) baseStart_8132962 baseEnd_8132962 := by
    simpa [prefixWord, tailWord_8132962, baseEnd_8132962] using wordTrace_append hprefix tailTrace_8132962
  have hstable : (prefixWord ++ tailWord_8132962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132962).length < 2 ^ (prefixWord ++ tailWord_8132962).sum := by decide
  have hdescent : baseEnd_8132962 < baseStart_8132962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132984 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_8132984 : Nat := 118140960795 + 8132984 * 2 ^ 59
def prefixEnd_8132984 : Nat := 4983230072969 + 3 ^ 40 * 8132984 * 2
def baseEnd_8132984 : Nat := 4176129947326312896397093

theorem tailTrace_8132984 : CollatzResearch.WordTrace tailWord_8132984 prefixEnd_8132984 4176129947326312896397093 := by
  unfold tailWord_8132984
  simp only [CollatzResearch.WordTrace]
  refine ⟨148317147983797722964063003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197756197311730297285417337 148317147983797722964063003)
  ·
    refine ⟨222475721975696584446094505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148317147983797722964063003 222475721975696584446094505)
    ·
      refine ⟨166856791481772438334570879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222475721975696584446094505 166856791481772438334570879)
      ·
        refine ⟨250285187222658657501856319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166856791481772438334570879 250285187222658657501856319)
        ·
          refine ⟨375427780833987986252784479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250285187222658657501856319 375427780833987986252784479)
          ·
            refine ⟨563141671250981979379176719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375427780833987986252784479 563141671250981979379176719)
            ·
              refine ⟨844712506876472969068765079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563141671250981979379176719 844712506876472969068765079)
              ·
                refine ⟨1267068760314709453603147619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844712506876472969068765079 1267068760314709453603147619)
                ·
                  refine ⟨1900603140472064180404721429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267068760314709453603147619 1900603140472064180404721429)
                  ·
                    refine ⟨89090772209628008456471317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1900603140472064180404721429 89090772209628008456471317)
                    ·
                      refine ⟨4176129947326312896397093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89090772209628008456471317 4176129947326312896397093)
                      ·
                        rfl

theorem cell23_8132984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_8132984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132984 prefixEnd_8132984 := by exact prefixLift 8132984
  have htrace : WordTrace (prefixWord ++ tailWord_8132984) baseStart_8132984 baseEnd_8132984 := by
    simpa [prefixWord, tailWord_8132984, baseEnd_8132984] using wordTrace_append hprefix tailTrace_8132984
  have hstable : (prefixWord ++ tailWord_8132984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132984).length < 2 ^ (prefixWord ++ tailWord_8132984).sum := by decide
  have hdescent : baseEnd_8132984 < baseStart_8132984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133048 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 2, 4, 2]
def baseStart_8133048 : Nat := 118140960795 + 8133048 * 2 ^ 59
def prefixEnd_8133048 : Nat := 4983230072969 + 3 ^ 40 * 8133048 * 2
def baseEnd_8133048 : Nat := 4176162810088200645996799

theorem tailTrace_8133048 : CollatzResearch.WordTrace tailWord_8133048 prefixEnd_8133048 4176162810088200645996799 := by
  unfold tailWord_8133048
  simp only [CollatzResearch.WordTrace]
  refine ⟨148318315119681792429227899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197757753492909056572303865 148318315119681792429227899)
  ·
    refine ⟨222477472679522688643841849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148318315119681792429227899 222477472679522688643841849)
    ·
      refine ⟨166858104509642016482881387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222477472679522688643841849 166858104509642016482881387)
      ·
        refine ⟨250287156764463024724322081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166858104509642016482881387 250287156764463024724322081)
        ·
          refine ⟨187715367573347268543241561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250287156764463024724322081 187715367573347268543241561)
          ·
            refine ⟨140786525680010451407431171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187715367573347268543241561 140786525680010451407431171)
            ·
              refine ⟨211179788520015677111146757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140786525680010451407431171 211179788520015677111146757)
              ·
                refine ⟨39596210347502939458340017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211179788520015677111146757 39596210347502939458340017)
                ·
                  refine ⟨29697157760627204593755013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39596210347502939458340017 29697157760627204593755013)
                  ·
                    refine ⟨5568217080117600861329065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29697157760627204593755013 5568217080117600861329065)
                    ·
                      refine ⟨4176162810088200645996799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568217080117600861329065 4176162810088200645996799)
                      ·
                        rfl

theorem cell23_8133048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_8133048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133048 prefixEnd_8133048 := by exact prefixLift 8133048
  have htrace : WordTrace (prefixWord ++ tailWord_8133048) baseStart_8133048 baseEnd_8133048 := by
    simpa [prefixWord, tailWord_8133048, baseEnd_8133048] using wordTrace_append hprefix tailTrace_8133048
  have hstable : (prefixWord ++ tailWord_8133048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133048).length < 2 ^ (prefixWord ++ tailWord_8133048).sum := by decide
  have hdescent : baseEnd_8133048 < baseStart_8133048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133149 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_8133149 : Nat := 118140960795 + 8133149 * 2 ^ 59
def prefixEnd_8133149 : Nat := 4983230072969 + 3 ^ 40 * 8133149 * 2
def baseEnd_8133149 : Nat := 4176214671634304750833835

theorem tailTrace_8133149 : CollatzResearch.WordTrace tailWord_8133149 prefixEnd_8133149 4176214671634304750833835 := by
  unfold tailWord_8133149
  simp only [CollatzResearch.WordTrace]
  refine ⟨296640314011997679107882501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197760209341331786071921667 296640314011997679107882501)
  ·
    refine ⟨55620058877249564832727969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296640314011997679107882501 55620058877249564832727969)
    ·
      refine ⟨41715044157937173624545977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55620058877249564832727969 41715044157937173624545977)
      ·
        refine ⟨31286283118452880218409483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41715044157937173624545977 31286283118452880218409483)
        ·
          refine ⟨46929424677679320327614225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31286283118452880218409483 46929424677679320327614225)
          ·
            refine ⟨35197068508259490245710669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46929424677679320327614225 35197068508259490245710669)
            ·
              refine ⟨13198900690597308842141501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35197068508259490245710669 13198900690597308842141501)
              ·
                refine ⟨4949587758973990815803063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13198900690597308842141501 4949587758973990815803063)
                ·
                  refine ⟨7424381638460986223704595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949587758973990815803063 7424381638460986223704595)
                  ·
                    refine ⟨11136572457691479335556893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424381638460986223704595 11136572457691479335556893)
                    ·
                      refine ⟨4176214671634304750833835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136572457691479335556893 4176214671634304750833835)
                      ·
                        rfl

theorem cell23_8133149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_8133149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133149 prefixEnd_8133149 := by exact prefixLift 8133149
  have htrace : WordTrace (prefixWord ++ tailWord_8133149) baseStart_8133149 baseEnd_8133149 := by
    simpa [prefixWord, tailWord_8133149, baseEnd_8133149] using wordTrace_append hprefix tailTrace_8133149
  have hstable : (prefixWord ++ tailWord_8133149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133149).length < 2 ^ (prefixWord ++ tailWord_8133149).sum := by decide
  have hdescent : baseEnd_8133149 < baseStart_8133149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133155 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 4]
def baseStart_8133155 : Nat := 118140960795 + 8133155 * 2 ^ 59
def prefixEnd_8133155 : Nat := 4983230072969 + 3 ^ 40 * 8133155 * 2
def baseEnd_8133155 : Nat := 4176217752518231727358807

theorem tailTrace_8133155 : CollatzResearch.WordTrace tailWord_8133155 prefixEnd_8133155 4176217752518231727358807 := by
  unfold tailWord_8133155
  simp only [CollatzResearch.WordTrace]
  refine ⟨296640532849975942132600919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197760355233317294755067279 296640532849975942132600919)
  ·
    refine ⟨444960799274963913198901379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296640532849975942132600919 444960799274963913198901379)
    ·
      refine ⟨667441198912445869798352069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444960799274963913198901379 667441198912445869798352069)
      ·
        refine ⟨125145224796083600587191013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 667441198912445869798352069 125145224796083600587191013)
        ·
          refine ⟨23464729649265675110098315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125145224796083600587191013 23464729649265675110098315)
          ·
            refine ⟨35197094473898512665147473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23464729649265675110098315 35197094473898512665147473)
            ·
              refine ⟨26397820855423884498860605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35197094473898512665147473 26397820855423884498860605)
              ·
                refine ⟨9899182820783956687072727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26397820855423884498860605 9899182820783956687072727)
                ·
                  refine ⟨14848774231175935030609091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899182820783956687072727 14848774231175935030609091)
                  ·
                    refine ⟨22273161346763902545913637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14848774231175935030609091 22273161346763902545913637)
                    ·
                      refine ⟨4176217752518231727358807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22273161346763902545913637 4176217752518231727358807)
                      ·
                        rfl

theorem cell23_8133155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_8133155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133155 prefixEnd_8133155 := by exact prefixLift 8133155
  have htrace : WordTrace (prefixWord ++ tailWord_8133155) baseStart_8133155 baseEnd_8133155 := by
    simpa [prefixWord, tailWord_8133155, baseEnd_8133155] using wordTrace_append hprefix tailTrace_8133155
  have hstable : (prefixWord ++ tailWord_8133155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133155).length < 2 ^ (prefixWord ++ tailWord_8133155).sum := by decide
  have hdescent : baseEnd_8133155 < baseStart_8133155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133166 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_8133166 : Nat := 118140960795 + 8133166 * 2 ^ 59
def prefixEnd_8133166 : Nat := 4983230072969 + 3 ^ 40 * 8133166 * 2
def baseEnd_8133166 : Nat := 4176223400805431184321257

theorem tailTrace_8133166 : CollatzResearch.WordTrace tailWord_8133166 prefixEnd_8133166 4176223400805431184321257 := by
  unfold tailWord_8133166
  simp only [CollatzResearch.WordTrace]
  refine ⟨37080116756617011376406419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197760622701957394007500901 37080116756617011376406419)
  ·
    refine ⟨55620175134925517064609629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37080116756617011376406419 55620175134925517064609629)
    ·
      refine ⟨20857565675597068899228611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55620175134925517064609629 20857565675597068899228611)
      ·
        refine ⟨31286348513395603348842917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20857565675597068899228611 31286348513395603348842917)
        ·
          refine ⟨5866190346261675627908047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31286348513395603348842917 5866190346261675627908047)
          ·
            refine ⟨8799285519392513441862071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866190346261675627908047 8799285519392513441862071)
            ·
              refine ⟨13198928279088770162793107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799285519392513441862071 13198928279088770162793107)
              ·
                refine ⟨19798392418633155244189661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13198928279088770162793107 19798392418633155244189661)
                ·
                  refine ⟨7424397156987433216571123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19798392418633155244189661 7424397156987433216571123)
                  ·
                    refine ⟨11136595735481149824856685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424397156987433216571123 11136595735481149824856685)
                    ·
                      refine ⟨4176223400805431184321257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136595735481149824856685 4176223400805431184321257)
                      ·
                        rfl

theorem cell23_8133166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_8133166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133166 prefixEnd_8133166 := by exact prefixLift 8133166
  have htrace : WordTrace (prefixWord ++ tailWord_8133166) baseStart_8133166 baseEnd_8133166 := by
    simpa [prefixWord, tailWord_8133166, baseEnd_8133166] using wordTrace_append hprefix tailTrace_8133166
  have hstable : (prefixWord ++ tailWord_8133166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133166).length < 2 ^ (prefixWord ++ tailWord_8133166).sum := by decide
  have hdescent : baseEnd_8133166 < baseStart_8133166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133178 : List Nat := [3, 1, 1, 1, 3, 4, 2, 8]
def baseStart_8133178 : Nat := 118140960795 + 8133178 * 2 ^ 59
def prefixEnd_8133178 : Nat := 4983230072969 + 3 ^ 40 * 8133178 * 2
def baseEnd_8133178 : Nat := 154675168984195745828563

theorem tailTrace_8133178 : CollatzResearch.WordTrace tailWord_8133178 prefixEnd_8133178 154675168984195745828563 := by
  unfold tailWord_8133178
  simp only [CollatzResearch.WordTrace]
  refine ⟨74160342932223154265172047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197760914485928411373792125 74160342932223154265172047)
  ·
    refine ⟨111240514398334731397758071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74160342932223154265172047 111240514398334731397758071)
    ·
      refine ⟨166860771597502097096637107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111240514398334731397758071 166860771597502097096637107)
      ·
        refine ⟨250291157396253145644955661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166860771597502097096637107 250291157396253145644955661)
        ·
          refine ⟨93859184023594929616858373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250291157396253145644955661 93859184023594929616858373)
          ·
            refine ⟨17598597004424049303160945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93859184023594929616858373 17598597004424049303160945)
            ·
              refine ⟨13198947753318036977370709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17598597004424049303160945 13198947753318036977370709)
              ·
                refine ⟨154675168984195745828563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13198947753318036977370709 154675168984195745828563)
                ·
                  rfl

theorem cell23_8133178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_8133178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133178 prefixEnd_8133178 := by exact prefixLift 8133178
  have htrace : WordTrace (prefixWord ++ tailWord_8133178) baseStart_8133178 baseEnd_8133178 := by
    simpa [prefixWord, tailWord_8133178, baseEnd_8133178] using wordTrace_append hprefix tailTrace_8133178
  have hstable : (prefixWord ++ tailWord_8133178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133178).length < 2 ^ (prefixWord ++ tailWord_8133178).sum := by decide
  have hdescent : baseEnd_8133178 < baseStart_8133178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133205 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_8133205 : Nat := 118140960795 + 8133205 * 2 ^ 59
def prefixEnd_8133205 : Nat := 4983230072969 + 3 ^ 40 * 8133205 * 2
def baseEnd_8133205 : Nat := 4176243426550956531733577

theorem tailTrace_8133205 : CollatzResearch.WordTrace tailWord_8133205 prefixEnd_8133205 4176243426550956531733577 := by
  unfold tailWord_8133205
  simp only [CollatzResearch.WordTrace]
  refine ⟨296642356499794800671921069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197761570999863200447947379 296642356499794800671921069)
  ·
    refine ⟨111240883687423050251970401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296642356499794800671921069 111240883687423050251970401)
    ·
      refine ⟨83430662765567287688977801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111240883687423050251970401 83430662765567287688977801)
      ·
        refine ⟨62572997074175465766733351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83430662765567287688977801 62572997074175465766733351)
        ·
          refine ⟨93859495611263198650100027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62572997074175465766733351 93859495611263198650100027)
          ·
            refine ⟨140789243416894797975150041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93859495611263198650100027 140789243416894797975150041)
            ·
              refine ⟨105591932562671098481362531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140789243416894797975150041 105591932562671098481362531)
              ·
                refine ⟨158387898844006647722043797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105591932562671098481362531 158387898844006647722043797)
                ·
                  refine ⟨7424432758312811611970803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158387898844006647722043797 7424432758312811611970803)
                  ·
                    refine ⟨11136649137469217417956205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424432758312811611970803 11136649137469217417956205)
                    ·
                      refine ⟨4176243426550956531733577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136649137469217417956205 4176243426550956531733577)
                      ·
                        rfl

theorem cell23_8133205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_8133205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133205 prefixEnd_8133205 := by exact prefixLift 8133205
  have htrace : WordTrace (prefixWord ++ tailWord_8133205) baseStart_8133205 baseEnd_8133205 := by
    simpa [prefixWord, tailWord_8133205, baseEnd_8133205] using wordTrace_append hprefix tailTrace_8133205
  have hstable : (prefixWord ++ tailWord_8133205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133205).length < 2 ^ (prefixWord ++ tailWord_8133205).sum := by decide
  have hdescent : baseEnd_8133205 < baseStart_8133205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133228 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_8133228 : Nat := 118140960795 + 8133228 * 2 ^ 59
def prefixEnd_8133228 : Nat := 4983230072969 + 3 ^ 40 * 8133228 * 2
def baseEnd_8133228 : Nat := 4176255236606009941745971

theorem tailTrace_8133228 : CollatzResearch.WordTrace tailWord_8133228 prefixEnd_8133228 4176255236606009941745971 := by
  unfold tailWord_8133228
  simp only [CollatzResearch.WordTrace]
  refine ⟨148321597689355737800004169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197762130252474317066672225 148321597689355737800004169)
  ·
    refine ⟨111241198267016803350003127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148321597689355737800004169 111241198267016803350003127)
    ·
      refine ⟨166861797400525205025004691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111241198267016803350003127 166861797400525205025004691)
      ·
        refine ⟨250292696100787807537507037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166861797400525205025004691 250292696100787807537507037)
        ·
          refine ⟨93859761037795427826565139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250292696100787807537507037 93859761037795427826565139)
          ·
            refine ⟨140789641556693141739847709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93859761037795427826565139 140789641556693141739847709)
            ·
              refine ⟨52796115583759928152442891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140789641556693141739847709 52796115583759928152442891)
              ·
                refine ⟨79194173375639892228664337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52796115583759928152442891 79194173375639892228664337)
                ·
                  refine ⟨59395630031729919171498253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79194173375639892228664337 59395630031729919171498253)
                  ·
                    refine ⟨22273361261898719689311845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59395630031729919171498253 22273361261898719689311845)
                    ·
                      refine ⟨4176255236606009941745971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22273361261898719689311845 4176255236606009941745971)
                      ·
                        rfl

theorem cell23_8133228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_8133228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133228 prefixEnd_8133228 := by exact prefixLift 8133228
  have htrace : WordTrace (prefixWord ++ tailWord_8133228) baseStart_8133228 baseEnd_8133228 := by
    simpa [prefixWord, tailWord_8133228, baseEnd_8133228] using wordTrace_append hprefix tailTrace_8133228
  have hstable : (prefixWord ++ tailWord_8133228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133228).length < 2 ^ (prefixWord ++ tailWord_8133228).sum := by decide
  have hdescent : baseEnd_8133228 < baseStart_8133228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133262 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_8133262 : Nat := 118140960795 + 8133262 * 2 ^ 59
def prefixEnd_8133262 : Nat := 4983230072969 + 3 ^ 40 * 8133262 * 2
def baseEnd_8133262 : Nat := 4176272694948262808720815

theorem tailTrace_8133262 : CollatzResearch.WordTrace tailWord_8133262 prefixEnd_8133262 4176272694948262808720815 := by
  unfold tailWord_8133262
  simp only [CollatzResearch.WordTrace]
  refine ⟨37080554432573537425843255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197762956973725532937830693 37080554432573537425843255)
  ·
    refine ⟨55620831648860306138764883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37080554432573537425843255 55620831648860306138764883)
    ·
      refine ⟨83431247473290459208147325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55620831648860306138764883 83431247473290459208147325)
      ·
        refine ⟨31286717802483922203055247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83431247473290459208147325 31286717802483922203055247)
        ·
          refine ⟨46930076703725883304582871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31286717802483922203055247 46930076703725883304582871)
          ·
            refine ⟨70395115055588824956874307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46930076703725883304582871 70395115055588824956874307)
            ·
              refine ⟨105592672583383237435311461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70395115055588824956874307 105592672583383237435311461)
              ·
                refine ⟨19798626109384357019120899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105592672583383237435311461 19798626109384357019120899)
                ·
                  refine ⟨29697939164076535528681349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19798626109384357019120899 29697939164076535528681349)
                  ·
                    refine ⟨5568363593264350411627753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29697939164076535528681349 5568363593264350411627753)
                    ·
                      refine ⟨4176272694948262808720815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568363593264350411627753 4176272694948262808720815)
                      ·
                        rfl

theorem cell23_8133262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_8133262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133262 prefixEnd_8133262 := by exact prefixLift 8133262
  have htrace : WordTrace (prefixWord ++ tailWord_8133262) baseStart_8133262 baseEnd_8133262 := by
    simpa [prefixWord, tailWord_8133262, baseEnd_8133262] using wordTrace_append hprefix tailTrace_8133262
  have hstable : (prefixWord ++ tailWord_8133262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133262).length < 2 ^ (prefixWord ++ tailWord_8133262).sum := by decide
  have hdescent : baseEnd_8133262 < baseStart_8133262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133266 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_8133266 : Nat := 118140960795 + 8133266 * 2 ^ 59
def prefixEnd_8133266 : Nat := 4983230072969 + 3 ^ 40 * 8133266 * 2
def baseEnd_8133266 : Nat := 4176274748870880793070797

theorem tailTrace_8133266 : CollatzResearch.WordTrace tailWord_8133266 prefixEnd_8133266 4176274748870880793070797 := by
  unfold tailWord_8133266
  simp only [CollatzResearch.WordTrace]
  refine ⟨74161145338143452022472913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197763054235049205393261101 74161145338143452022472913)
  ·
    refine ⟨55620859003607589016854685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74161145338143452022472913 55620859003607589016854685)
    ·
      refine ⟨20857822126352845881320507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55620859003607589016854685 20857822126352845881320507)
      ·
        refine ⟨31286733189529268821980761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20857822126352845881320507 31286733189529268821980761)
        ·
          refine ⟨23465049892146951616485571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31286733189529268821980761 23465049892146951616485571)
          ·
            refine ⟨35197574838220427424728357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23465049892146951616485571 35197574838220427424728357)
            ·
              refine ⟨6599545282166330142136567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35197574838220427424728357 6599545282166330142136567)
              ·
                refine ⟨9899317923249495213204851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6599545282166330142136567 9899317923249495213204851)
                ·
                  refine ⟨14848976884874242819807277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899317923249495213204851 14848976884874242819807277)
                  ·
                    refine ⟨5568366331827841057427729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14848976884874242819807277 5568366331827841057427729)
                    ·
                      refine ⟨4176274748870880793070797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568366331827841057427729 4176274748870880793070797)
                      ·
                        rfl

theorem cell23_8133266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_8133266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133266 prefixEnd_8133266 := by exact prefixLift 8133266
  have htrace : WordTrace (prefixWord ++ tailWord_8133266) baseStart_8133266 baseEnd_8133266 := by
    simpa [prefixWord, tailWord_8133266, baseEnd_8133266] using wordTrace_append hprefix tailTrace_8133266
  have hstable : (prefixWord ++ tailWord_8133266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133266).length < 2 ^ (prefixWord ++ tailWord_8133266).sum := by decide
  have hdescent : baseEnd_8133266 < baseStart_8133266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133295 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_8133295 : Nat := 118140960795 + 8133295 * 2 ^ 59
def prefixEnd_8133295 : Nat := 4983230072969 + 3 ^ 40 * 8133295 * 2
def baseEnd_8133295 : Nat := 4176289639809861179608163

theorem tailTrace_8133295 : CollatzResearch.WordTrace tailWord_8133295 prefixEnd_8133295 4176289639809861179608163 := by
  unfold tailWord_8133295
  simp only [CollatzResearch.WordTrace]
  refine ⟨296645639069468746042697339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197763759379645830695131559 296645639069468746042697339)
  ·
    refine ⟨444968458604203119064046009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296645639069468746042697339 444968458604203119064046009)
    ·
      refine ⟨333726343953152339298034507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444968458604203119064046009 333726343953152339298034507)
      ·
        refine ⟨500589515929728508947051761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333726343953152339298034507 500589515929728508947051761)
        ·
          refine ⟨375442136947296381710288821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500589515929728508947051761 375442136947296381710288821)
          ·
            refine ⟨35197700338809035785339577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375442136947296381710288821 35197700338809035785339577)
            ·
              refine ⟨26398275254106776839004683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35197700338809035785339577 26398275254106776839004683)
              ·
                refine ⟨39597412881160165258507025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26398275254106776839004683 39597412881160165258507025)
                ·
                  refine ⟨29698059660870123943880269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39597412881160165258507025 29698059660870123943880269)
                  ·
                    refine ⟨11136772372826296478955101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29698059660870123943880269 11136772372826296478955101)
                    ·
                      refine ⟨4176289639809861179608163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136772372826296478955101 4176289639809861179608163)
                      ·
                        rfl

theorem cell23_8133295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_8133295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133295 prefixEnd_8133295 := by exact prefixLift 8133295
  have htrace : WordTrace (prefixWord ++ tailWord_8133295) baseStart_8133295 baseEnd_8133295 := by
    simpa [prefixWord, tailWord_8133295, baseEnd_8133295] using wordTrace_append hprefix tailTrace_8133295
  have hstable : (prefixWord ++ tailWord_8133295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133295).length < 2 ^ (prefixWord ++ tailWord_8133295).sum := by decide
  have hdescent : baseEnd_8133295 < baseStart_8133295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133335 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_8133335 : Nat := 118140960795 + 8133335 * 2 ^ 59
def prefixEnd_8133335 : Nat := 4983230072969 + 3 ^ 40 * 8133335 * 2
def baseEnd_8133335 : Nat := 4176310179036041023107979

theorem tailTrace_8133335 : CollatzResearch.WordTrace tailWord_8133335 prefixEnd_8133335 4176310179036041023107979 := by
  unfold tailWord_8133335
  simp only [CollatzResearch.WordTrace]
  refine ⟨296647097989323832874153459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197764731992882555249435639 296647097989323832874153459)
  ·
    refine ⟨444970646983985749311230189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296647097989323832874153459 444970646983985749311230189)
    ·
      refine ⟨166863992618994655991711321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444970646983985749311230189 166863992618994655991711321)
      ·
        refine ⟨125147994464245991993783491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166863992618994655991711321 125147994464245991993783491)
        ·
          refine ⟨187721991696368987990675237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125147994464245991993783491 187721991696368987990675237)
          ·
            refine ⟨35197873443069185248251607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187721991696368987990675237 35197873443069185248251607)
            ·
              refine ⟨52796810164603777872377411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35197873443069185248251607 52796810164603777872377411)
              ·
                refine ⟨79195215246905666808566117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52796810164603777872377411 79195215246905666808566117)
                ·
                  refine ⟨14849102858794812526606147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79195215246905666808566117 14849102858794812526606147)
                  ·
                    refine ⟨22273654288192218789909221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14849102858794812526606147 22273654288192218789909221)
                    ·
                      refine ⟨4176310179036041023107979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22273654288192218789909221 4176310179036041023107979)
                      ·
                        rfl

theorem cell23_8133335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_8133335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133335 prefixEnd_8133335 := by exact prefixLift 8133335
  have htrace : WordTrace (prefixWord ++ tailWord_8133335) baseStart_8133335 baseEnd_8133335 := by
    simpa [prefixWord, tailWord_8133335, baseEnd_8133335] using wordTrace_append hprefix tailTrace_8133335
  have hstable : (prefixWord ++ tailWord_8133335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133335).length < 2 ^ (prefixWord ++ tailWord_8133335).sum := by decide
  have hdescent : baseEnd_8133335 < baseStart_8133335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133355 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 3]
def baseStart_8133355 : Nat := 118140960795 + 8133355 * 2 ^ 59
def prefixEnd_8133355 : Nat := 4983230072969 + 3 ^ 40 * 8133355 * 2
def baseEnd_8133355 : Nat := 4176320448649130944857887

theorem tailTrace_8133355 : CollatzResearch.WordTrace tailWord_8133355 prefixEnd_8133355 4176320448649130944857887 := by
  unfold tailWord_8133355
  simp only [CollatzResearch.WordTrace]
  refine ⟨296647827449251376289881519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197765218299500917526587679 296647827449251376289881519)
  ·
    refine ⟨444971741173877064434822279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296647827449251376289881519 444971741173877064434822279)
    ·
      refine ⟨667457611760815596652233419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444971741173877064434822279 667457611760815596652233419)
      ·
        refine ⟨1001186417641223394978350129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667457611760815596652233419 1001186417641223394978350129)
        ·
          refine ⟨750889813230917546233762597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001186417641223394978350129 750889813230917546233762597)
          ·
            refine ⟨140791839980797039918830487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 750889813230917546233762597 140791839980797039918830487)
            ·
              refine ⟨211187759971195559878245731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140791839980797039918830487 211187759971195559878245731)
              ·
                refine ⟨316781639956793339817368597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211187759971195559878245731 316781639956793339817368597)
                ·
                  refine ⟨14849139372974687803939153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 316781639956793339817368597 14849139372974687803939153)
                  ·
                    refine ⟨11136854529731015852954365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14849139372974687803939153 11136854529731015852954365)
                    ·
                      refine ⟨4176320448649130944857887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136854529731015852954365 4176320448649130944857887)
                      ·
                        rfl

theorem cell23_8133355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 3].length) (baseStart_8133355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133355 prefixEnd_8133355 := by exact prefixLift 8133355
  have htrace : WordTrace (prefixWord ++ tailWord_8133355) baseStart_8133355 baseEnd_8133355 := by
    simpa [prefixWord, tailWord_8133355, baseEnd_8133355] using wordTrace_append hprefix tailTrace_8133355
  have hstable : (prefixWord ++ tailWord_8133355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133355).length < 2 ^ (prefixWord ++ tailWord_8133355).sum := by decide
  have hdescent : baseEnd_8133355 < baseStart_8133355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133372 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_8133372 : Nat := 118140960795 + 8133372 * 2 ^ 59
def prefixEnd_8133372 : Nat := 4983230072969 + 3 ^ 40 * 8133372 * 2
def baseEnd_8133372 : Nat := 4176329177820257378345309

theorem tailTrace_8133372 : CollatzResearch.WordTrace tailWord_8133372 prefixEnd_8133372 4176329177820257378345309 := by
  unfold tailWord_8133372
  simp only [CollatzResearch.WordTrace]
  refine ⟨148324223745094894096625185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197765631660126525462166913 148324223745094894096625185)
  ·
    refine ⟨111243167808821170572468889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148324223745094894096625185 111243167808821170572468889)
    ·
      refine ⟨83432375856615877929351667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111243167808821170572468889 83432375856615877929351667)
      ·
        refine ⟨125148563784923816894027501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83432375856615877929351667 125148563784923816894027501)
        ·
          refine ⟨46930711419346431335260313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125148563784923816894027501 46930711419346431335260313)
          ·
            refine ⟨35198033564509823501445235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46930711419346431335260313 35198033564509823501445235)
            ·
              refine ⟨52797050346764735252167853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35198033564509823501445235 52797050346764735252167853)
              ·
                refine ⟨19798893880036775719562945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52797050346764735252167853 19798893880036775719562945)
                ·
                  refine ⟨14849170410027581789672209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19798893880036775719562945 14849170410027581789672209)
                  ·
                    refine ⟨11136877807520686342254157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14849170410027581789672209 11136877807520686342254157)
                    ·
                      refine ⟨4176329177820257378345309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136877807520686342254157 4176329177820257378345309)
                      ·
                        rfl

theorem cell23_8133372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_8133372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133372 prefixEnd_8133372 := by exact prefixLift 8133372
  have htrace : WordTrace (prefixWord ++ tailWord_8133372) baseStart_8133372 baseEnd_8133372 := by
    simpa [prefixWord, tailWord_8133372, baseEnd_8133372] using wordTrace_append hprefix tailTrace_8133372
  have hstable : (prefixWord ++ tailWord_8133372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133372).length < 2 ^ (prefixWord ++ tailWord_8133372).sum := by decide
  have hdescent : baseEnd_8133372 < baseStart_8133372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133429 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_8133429 : Nat := 118140960795 + 8133429 * 2 ^ 59
def prefixEnd_8133429 : Nat := 4983230072969 + 3 ^ 40 * 8133429 * 2
def baseEnd_8133429 : Nat := 4176358446217563655332547

theorem tailTrace_8133429 : CollatzResearch.WordTrace tailWord_8133429 prefixEnd_8133429 4176358446217563655332547 := by
  unfold tailWord_8133429
  simp only [CollatzResearch.WordTrace]
  refine ⟨296650526450983286928075341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197767017633988857952050227 296650526450983286928075341)
  ·
    refine ⟨111243947419118732598028253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296650526450983286928075341 111243947419118732598028253)
    ·
      refine ⟨41716480282169524724260595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111243947419118732598028253 41716480282169524724260595)
      ·
        refine ⟨62574720423254287086390893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41716480282169524724260595 62574720423254287086390893)
        ·
          refine ⟨23465520158720357657396585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62574720423254287086390893 23465520158720357657396585)
          ·
            refine ⟨17599140119040268243047439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23465520158720357657396585 17599140119040268243047439)
            ·
              refine ⟨26398710178560402364571159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17599140119040268243047439 26398710178560402364571159)
              ·
                refine ⟨39598065267840603546856739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26398710178560402364571159 39598065267840603546856739)
                ·
                  refine ⟨59397097901760905320285109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39598065267840603546856739 59397097901760905320285109)
                  ·
                    refine ⟨5568477928290084873776729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59397097901760905320285109 5568477928290084873776729)
                    ·
                      refine ⟨4176358446217563655332547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568477928290084873776729 4176358446217563655332547)
                      ·
                        rfl

theorem cell23_8133429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_8133429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133429 prefixEnd_8133429 := by exact prefixLift 8133429
  have htrace : WordTrace (prefixWord ++ tailWord_8133429) baseStart_8133429 baseEnd_8133429 := by
    simpa [prefixWord, tailWord_8133429, baseEnd_8133429] using wordTrace_append hprefix tailTrace_8133429
  have hstable : (prefixWord ++ tailWord_8133429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133429).length < 2 ^ (prefixWord ++ tailWord_8133429).sum := by decide
  have hdescent : baseEnd_8133429 < baseStart_8133429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133439 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 1, 5]
def baseStart_8133439 : Nat := 118140960795 + 8133439 * 2 ^ 59
def prefixEnd_8133439 : Nat := 4983230072969 + 3 ^ 40 * 8133439 * 2
def baseEnd_8133439 : Nat := 1392121193674702872069167

theorem tailTrace_8133439 : CollatzResearch.WordTrace tailWord_8133439 prefixEnd_8133439 1392121193674702872069167 := by
  unfold tailWord_8133439
  simp only [CollatzResearch.WordTrace]
  refine ⟨296650891180947058635939371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197767260787298039090626247 296650891180947058635939371)
  ·
    refine ⟨444976336771420587953909057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296650891180947058635939371 444976336771420587953909057)
    ·
      refine ⟨333732252578565440965431793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444976336771420587953909057 333732252578565440965431793)
      ·
        refine ⟨250299189433924080724073845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333732252578565440965431793 250299189433924080724073845)
        ·
          refine ⟨23465549009430382567881923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250299189433924080724073845 23465549009430382567881923)
          ·
            refine ⟨35198323514145573851822885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23465549009430382567881923 35198323514145573851822885)
            ·
              refine ⟨6599685658902295097216791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35198323514145573851822885 6599685658902295097216791)
              ·
                refine ⟨9899528488353442645825187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6599685658902295097216791 9899528488353442645825187)
                ·
                  refine ⟨14849292732530163968737781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899528488353442645825187 14849292732530163968737781)
                  ·
                    refine ⟨1392121193674702872069167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14849292732530163968737781 1392121193674702872069167)
                    ·
                      rfl

theorem cell23_8133439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 5].length) (baseStart_8133439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133439 prefixEnd_8133439 := by exact prefixLift 8133439
  have htrace : WordTrace (prefixWord ++ tailWord_8133439) baseStart_8133439 baseEnd_8133439 := by
    simpa [prefixWord, tailWord_8133439, baseEnd_8133439] using wordTrace_append hprefix tailTrace_8133439
  have hstable : (prefixWord ++ tailWord_8133439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133439).length < 2 ^ (prefixWord ++ tailWord_8133439).sum := by decide
  have hdescent : baseEnd_8133439 < baseStart_8133439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133453 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_8133453 : Nat := 118140960795 + 8133453 * 2 ^ 59
def prefixEnd_8133453 : Nat := 4983230072969 + 3 ^ 40 * 8133453 * 2
def baseEnd_8133453 : Nat := 4176370769753271561432437

theorem tailTrace_8133453 : CollatzResearch.WordTrace tailWord_8133453 prefixEnd_8133453 4176370769753271561432437 := by
  unfold tailWord_8133453
  simp only [CollatzResearch.WordTrace]
  refine ⟨296651401802896339026949013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197767601201930892684632675 296651401802896339026949013)
  ·
    refine ⟨13905534459510765891888235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296651401802896339026949013 13905534459510765891888235)
    ·
      refine ⟨20858301689266148837832353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13905534459510765891888235 20858301689266148837832353)
      ·
        refine ⟨15643726266949611628374265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20858301689266148837832353 15643726266949611628374265)
        ·
          refine ⟨11732794700212208721280699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15643726266949611628374265 11732794700212208721280699)
          ·
            refine ⟨17599192050318313081921049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732794700212208721280699 17599192050318313081921049)
            ·
              refine ⟨13199394037738734811440787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17599192050318313081921049 13199394037738734811440787)
              ·
                refine ⟨19799091056608102217161181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13199394037738734811440787 19799091056608102217161181)
                ·
                  refine ⟨7424659146228038331435443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19799091056608102217161181 7424659146228038331435443)
                  ·
                    refine ⟨11136988719342057497153165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424659146228038331435443 11136988719342057497153165)
                    ·
                      refine ⟨4176370769753271561432437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11136988719342057497153165 4176370769753271561432437)
                      ·
                        rfl

theorem cell23_8133453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_8133453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133453 prefixEnd_8133453 := by exact prefixLift 8133453
  have htrace : WordTrace (prefixWord ++ tailWord_8133453) baseStart_8133453 baseEnd_8133453 := by
    simpa [prefixWord, tailWord_8133453, baseEnd_8133453] using wordTrace_append hprefix tailTrace_8133453
  have hstable : (prefixWord ++ tailWord_8133453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133453).length < 2 ^ (prefixWord ++ tailWord_8133453).sum := by decide
  have hdescent : baseEnd_8133453 < baseStart_8133453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133476 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_8133476 : Nat := 118140960795 + 8133476 * 2 ^ 59
def prefixEnd_8133476 : Nat := 4983230072969 + 3 ^ 40 * 8133476 * 2
def baseEnd_8133476 : Nat := 4176382579808324971444831

theorem tailTrace_8133476 : CollatzResearch.WordTrace tailWord_8133476 prefixEnd_8133476 4176382579808324971444831 := by
  unfold tailWord_8133476
  simp only [CollatzResearch.WordTrace]
  refine ⟨148326120340906506977518141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197768160454542009303357521 148326120340906506977518141)
  ·
    refine ⟨55622295127839940116569303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148326120340906506977518141 55622295127839940116569303)
    ·
      refine ⟨83433442691759910174853955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55622295127839940116569303 83433442691759910174853955)
      ·
        refine ⟨125150164037639865262280933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83433442691759910174853955 125150164037639865262280933)
        ·
          refine ⟨23465655757057474736677675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125150164037639865262280933 23465655757057474736677675)
          ·
            refine ⟨35198483635586212105016513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23465655757057474736677675 35198483635586212105016513)
            ·
              refine ⟨26398862726689659078762385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35198483635586212105016513 26398862726689659078762385)
              ·
                refine ⟨19799147045017244309071789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26398862726689659078762385 19799147045017244309071789)
                ·
                  refine ⟨7424680141881466615901921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19799147045017244309071789 7424680141881466615901921)
                  ·
                    refine ⟨5568510106411099961926441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7424680141881466615901921 5568510106411099961926441)
                    ·
                      refine ⟨4176382579808324971444831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568510106411099961926441 4176382579808324971444831)
                      ·
                        rfl

theorem cell23_8133476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_8133476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133476 prefixEnd_8133476 := by exact prefixLift 8133476
  have htrace : WordTrace (prefixWord ++ tailWord_8133476) baseStart_8133476 baseEnd_8133476 := by
    simpa [prefixWord, tailWord_8133476, baseEnd_8133476] using wordTrace_append hprefix tailTrace_8133476
  have hstable : (prefixWord ++ tailWord_8133476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133476).length < 2 ^ (prefixWord ++ tailWord_8133476).sum := by decide
  have hdescent : baseEnd_8133476 < baseStart_8133476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133479 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_8133479 : Nat := 118140960795 + 8133479 * 2 ^ 59
def prefixEnd_8133479 : Nat := 4983230072969 + 3 ^ 40 * 8133479 * 2
def baseEnd_8133479 : Nat := 4176384120250288459707317

theorem tailTrace_8133479 : CollatzResearch.WordTrace tailWord_8133479 prefixEnd_8133479 4176384120250288459707317 := by
  unfold tailWord_8133479
  simp only [CollatzResearch.WordTrace]
  refine ⟨296652350100802145467395491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197768233400534763644930327 296652350100802145467395491)
  ·
    refine ⟨444978525151203218201093237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296652350100802145467395491 444978525151203218201093237)
    ·
      refine ⟨41716736732925301706352491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 444978525151203218201093237 41716736732925301706352491)
      ·
        refine ⟨62575105099387952559528737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41716736732925301706352491 62575105099387952559528737)
        ·
          refine ⟨46931328824540964419646553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62575105099387952559528737 46931328824540964419646553)
          ·
            refine ⟨35198496618405723314734915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46931328824540964419646553 35198496618405723314734915)
            ·
              refine ⟨52797744927608584972102373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35198496618405723314734915 52797744927608584972102373)
              ·
                refine ⟨9899577173926609682269195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52797744927608584972102373 9899577173926609682269195)
                ·
                  refine ⟨14849365760889914523403793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899577173926609682269195 14849365760889914523403793)
                  ·
                    refine ⟨11137024320667435892552845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14849365760889914523403793 11137024320667435892552845)
                    ·
                      refine ⟨4176384120250288459707317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137024320667435892552845 4176384120250288459707317)
                      ·
                        rfl

theorem cell23_8133479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_8133479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133479 prefixEnd_8133479 := by exact prefixLift 8133479
  have htrace : WordTrace (prefixWord ++ tailWord_8133479) baseStart_8133479 baseEnd_8133479 := by
    simpa [prefixWord, tailWord_8133479, baseEnd_8133479] using wordTrace_append hprefix tailTrace_8133479
  have hstable : (prefixWord ++ tailWord_8133479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133479).length < 2 ^ (prefixWord ++ tailWord_8133479).sum := by decide
  have hdescent : baseEnd_8133479 < baseStart_8133479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133509 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_8133509 : Nat := 118140960795 + 8133509 * 2 ^ 59
def prefixEnd_8133509 : Nat := 4983230072969 + 3 ^ 40 * 8133509 * 2
def baseEnd_8133509 : Nat := 4176399524669923342332179

theorem tailTrace_8133509 : CollatzResearch.WordTrace tailWord_8133509 prefixEnd_8133509 4176399524669923342332179 := by
  unfold tailWord_8133509
  simp only [CollatzResearch.WordTrace]
  refine ⟨296653444290693460590987581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197768962860462307060658387 296653444290693460590987581)
  ·
    refine ⟨111245041609010047721620343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296653444290693460590987581 111245041609010047721620343)
    ·
      refine ⟨166867562413515071582430515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111245041609010047721620343 166867562413515071582430515)
      ·
        refine ⟨250301343620272607373645773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166867562413515071582430515 250301343620272607373645773)
        ·
          refine ⟨93863003857602227765117165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250301343620272607373645773 93863003857602227765117165)
          ·
            refine ⟨35198626446600835411918937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93863003857602227765117165 35198626446600835411918937)
            ·
              refine ⟨26398969834950626558939203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35198626446600835411918937 26398969834950626558939203)
              ·
                refine ⟨39598454752425939838408805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26398969834950626558939203 39598454752425939838408805)
                ·
                  refine ⟨7424710266079863719701651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39598454752425939838408805 7424710266079863719701651)
                  ·
                    refine ⟨11137065399119795579552477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424710266079863719701651 11137065399119795579552477)
                    ·
                      refine ⟨4176399524669923342332179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137065399119795579552477 4176399524669923342332179)
                      ·
                        rfl

theorem cell23_8133509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_8133509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133509 prefixEnd_8133509 := by exact prefixLift 8133509
  have htrace : WordTrace (prefixWord ++ tailWord_8133509) baseStart_8133509 baseEnd_8133509 := by
    simpa [prefixWord, tailWord_8133509, baseEnd_8133509] using wordTrace_append hprefix tailTrace_8133509
  have hstable : (prefixWord ++ tailWord_8133509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133509).length < 2 ^ (prefixWord ++ tailWord_8133509).sum := by decide
  have hdescent : baseEnd_8133509 < baseStart_8133509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133536 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 1, 3, 2]
def baseStart_8133536 : Nat := 118140960795 + 8133536 * 2 ^ 59
def prefixEnd_8133536 : Nat := 4983230072969 + 3 ^ 40 * 8133536 * 2
def baseEnd_8133536 : Nat := 4176413388647594736694555

theorem tailTrace_8133536 : CollatzResearch.WordTrace tailWord_8133536 prefixEnd_8133536 4176413388647594736694555 := by
  unfold tailWord_8133536
  simp only [CollatzResearch.WordTrace]
  refine ⟨148327214530797822101110231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197769619374397096134813641 148327214530797822101110231)
  ·
    refine ⟨222490821796196733151665347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148327214530797822101110231 222490821796196733151665347)
    ·
      refine ⟨333736232694295099727498021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222490821796196733151665347 333736232694295099727498021)
      ·
        refine ⟨62575543630180331198905879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333736232694295099727498021 62575543630180331198905879)
        ·
          refine ⟨93863315445270496798358819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62575543630180331198905879 93863315445270496798358819)
          ·
            refine ⟨140794973167905745197538229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93863315445270496798358819 140794973167905745197538229)
            ·
              refine ⟨13199528734491163612269209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140794973167905745197538229 13199528734491163612269209)
              ·
                refine ⟨9899646550868372709201907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13199528734491163612269209 9899646550868372709201907)
                ·
                  refine ⟨14849469826302559063802861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899646550868372709201907 14849469826302559063802861)
                  ·
                    refine ⟨5568551184863459648926073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14849469826302559063802861 5568551184863459648926073)
                    ·
                      refine ⟨4176413388647594736694555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568551184863459648926073 4176413388647594736694555)
                      ·
                        rfl

theorem cell23_8133536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_8133536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133536 prefixEnd_8133536 := by exact prefixLift 8133536
  have htrace : WordTrace (prefixWord ++ tailWord_8133536) baseStart_8133536 baseEnd_8133536 := by
    simpa [prefixWord, tailWord_8133536, baseEnd_8133536] using wordTrace_append hprefix tailTrace_8133536
  have hstable : (prefixWord ++ tailWord_8133536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133536).length < 2 ^ (prefixWord ++ tailWord_8133536).sum := by decide
  have hdescent : baseEnd_8133536 < baseStart_8133536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133555 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 11]
def baseStart_8133555 : Nat := 118140960795 + 8133555 * 2 ^ 59
def prefixEnd_8133555 : Nat := 4983230072969 + 3 ^ 40 * 8133555 * 2
def baseEnd_8133555 : Nat := 464047016086670018039663

theorem tailTrace_8133555 : CollatzResearch.WordTrace tailWord_8133555 prefixEnd_8133555 464047016086670018039663 := by
  unfold tailWord_8133555
  simp only [CollatzResearch.WordTrace]
  refine ⟨296655122048526810447162119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197770081365684540298108079 296655122048526810447162119)
  ·
    refine ⟨444982683072790215670743179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296655122048526810447162119 444982683072790215670743179)
    ·
      refine ⟨667474024609185323506114769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444982683072790215670743179 667474024609185323506114769)
      ·
        refine ⟨500605518456888992629586077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667474024609185323506114769 500605518456888992629586077)
        ·
          refine ⟨187727069421333372236094779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500605518456888992629586077 187727069421333372236094779)
          ·
            refine ⟨281590604132000058354142169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187727069421333372236094779 281590604132000058354142169)
            ·
              refine ⟨211192953099000043765606627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281590604132000058354142169 211192953099000043765606627)
              ·
                refine ⟨316789429648500065648409941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211192953099000043765606627 316789429648500065648409941)
                ·
                  refine ⟨464047016086670018039663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 316789429648500065648409941 464047016086670018039663)
                  ·
                    rfl

theorem cell23_8133555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 11].length) (baseStart_8133555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133555 prefixEnd_8133555 := by exact prefixLift 8133555
  have htrace : WordTrace (prefixWord ++ tailWord_8133555) baseStart_8133555 baseEnd_8133555 := by
    simpa [prefixWord, tailWord_8133555, baseEnd_8133555] using wordTrace_append hprefix tailTrace_8133555
  have hstable : (prefixWord ++ tailWord_8133555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133555).length < 2 ^ (prefixWord ++ tailWord_8133555).sum := by decide
  have hdescent : baseEnd_8133555 < baseStart_8133555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133562 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_8133562 : Nat := 118140960795 + 8133562 * 2 ^ 59
def prefixEnd_8133562 : Nat := 4983230072969 + 3 ^ 40 * 8133562 * 2
def baseEnd_8133562 : Nat := 4176426739144611634969435

theorem tailTrace_8133562 : CollatzResearch.WordTrace tailWord_8133562 prefixEnd_8133562 4176426739144611634969435 := by
  unfold tailWord_8133562
  simp only [CollatzResearch.WordTrace]
  refine ⟨74163844339875362660666735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197770251573000967095111293 74163844339875362660666735)
  ·
    refine ⟨111245766509813043991000103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74163844339875362660666735 111245766509813043991000103)
    ·
      refine ⟨166868649764719565986500155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111245766509813043991000103 166868649764719565986500155)
      ·
        refine ⟨250302974647079348979750233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166868649764719565986500155 250302974647079348979750233)
        ·
          refine ⟨187727230985309511734812675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250302974647079348979750233 187727230985309511734812675)
          ·
            refine ⟨281590846477964267602219013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187727230985309511734812675 281590846477964267602219013)
            ·
              refine ⟨52798283714618300175416065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281590846477964267602219013 52798283714618300175416065)
              ·
                refine ⟨39598712785963725131562049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52798283714618300175416065 39598712785963725131562049)
                ·
                  refine ⟨29699034589472793848671537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39598712785963725131562049 29699034589472793848671537)
                  ·
                    refine ⟨22274275942104595386503653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29699034589472793848671537 22274275942104595386503653)
                    ·
                      refine ⟨4176426739144611634969435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22274275942104595386503653 4176426739144611634969435)
                      ·
                        rfl

theorem cell23_8133562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_8133562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133562 prefixEnd_8133562 := by exact prefixLift 8133562
  have htrace : WordTrace (prefixWord ++ tailWord_8133562) baseStart_8133562 baseEnd_8133562 := by
    simpa [prefixWord, tailWord_8133562, baseEnd_8133562] using wordTrace_append hprefix tailTrace_8133562
  have hstable : (prefixWord ++ tailWord_8133562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133562).length < 2 ^ (prefixWord ++ tailWord_8133562).sum := by decide
  have hdescent : baseEnd_8133562 < baseStart_8133562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133589 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 7]
def baseStart_8133589 : Nat := 118140960795 + 8133589 * 2 ^ 59
def prefixEnd_8133589 : Nat := 4983230072969 + 3 ^ 40 * 8133589 * 2
def baseEnd_8133589 : Nat := 464048955902475892147979

theorem tailTrace_8133589 : CollatzResearch.WordTrace tailWord_8133589 prefixEnd_8133589 464048955902475892147979 := by
  unfold tailWord_8133589
  simp only [CollatzResearch.WordTrace]
  refine ⟨296656362130403634253899821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197770908086935756169266547 296656362130403634253899821)
  ·
    refine ⟨111246135798901362845212433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296656362130403634253899821 111246135798901362845212433)
    ·
      refine ⟨83434601849176022133909325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111246135798901362845212433 83434601849176022133909325)
      ·
        refine ⟨31287975693441008300215997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83434601849176022133909325 31287975693441008300215997)
        ·
          refine ⟨11732990885040378112580999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31287975693441008300215997 11732990885040378112580999)
          ·
            refine ⟨17599486327560567168871499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732990885040378112580999 17599486327560567168871499)
            ·
              refine ⟨26399229491340850753307249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17599486327560567168871499 26399229491340850753307249)
              ·
                refine ⟨19799422118505638064980437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26399229491340850753307249 19799422118505638064980437)
                ·
                  refine ⟨464048955902475892147979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19799422118505638064980437 464048955902475892147979)
                  ·
                    rfl

theorem cell23_8133589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_8133589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133589 prefixEnd_8133589 := by exact prefixLift 8133589
  have htrace : WordTrace (prefixWord ++ tailWord_8133589) baseStart_8133589 baseEnd_8133589 := by
    simpa [prefixWord, tailWord_8133589, baseEnd_8133589] using wordTrace_append hprefix tailTrace_8133589
  have hstable : (prefixWord ++ tailWord_8133589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133589).length < 2 ^ (prefixWord ++ tailWord_8133589).sum := by decide
  have hdescent : baseEnd_8133589 < baseStart_8133589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133634 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_8133634 : Nat := 118140960795 + 8133634 * 2 ^ 59
def prefixEnd_8133634 : Nat := 4983230072969 + 3 ^ 40 * 8133634 * 2
def baseEnd_8133634 : Nat := 4176463709751735353269105

theorem tailTrace_8133634 : CollatzResearch.WordTrace tailWord_8133634 prefixEnd_8133634 4176463709751735353269105 := by
  unfold tailWord_8133634
  simp only [CollatzResearch.WordTrace]
  refine ⟨74164500853810151734821989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197772002276827071292858637 74164500853810151734821989)
  ·
    refine ⟨13905843910089403450279123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74164500853810151734821989 13905843910089403450279123)
    ·
      refine ⟨20858765865134105175418685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13905843910089403450279123 20858765865134105175418685)
      ·
        refine ⟨7822037199425289440782007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20858765865134105175418685 7822037199425289440782007)
        ·
          refine ⟨11733055799137934161173011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822037199425289440782007 11733055799137934161173011)
          ·
            refine ⟨17599583698706901241759517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11733055799137934161173011 17599583698706901241759517)
            ·
              refine ⟨6599843887015087965659819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17599583698706901241759517 6599843887015087965659819)
              ·
                refine ⟨9899765830522631948489729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6599843887015087965659819 9899765830522631948489729)
                ·
                  refine ⟨7424824372891973961367297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9899765830522631948489729 7424824372891973961367297)
                  ·
                    refine ⟨5568618279668980471025473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7424824372891973961367297 5568618279668980471025473)
                    ·
                      refine ⟨4176463709751735353269105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568618279668980471025473 4176463709751735353269105)
                      ·
                        rfl

theorem cell23_8133634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_8133634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133634 prefixEnd_8133634 := by exact prefixLift 8133634
  have htrace : WordTrace (prefixWord ++ tailWord_8133634) baseStart_8133634 baseEnd_8133634 := by
    simpa [prefixWord, tailWord_8133634, baseEnd_8133634] using wordTrace_append hprefix tailTrace_8133634
  have hstable : (prefixWord ++ tailWord_8133634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133634).length < 2 ^ (prefixWord ++ tailWord_8133634).sum := by decide
  have hdescent : baseEnd_8133634 < baseStart_8133634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133706 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_8133706 : Nat := 118140960795 + 8133706 * 2 ^ 59
def prefixEnd_8133706 : Nat := 4983230072969 + 3 ^ 40 * 8133706 * 2
def baseEnd_8133706 : Nat := 4176500680358859071568773

theorem tailTrace_8133706 : CollatzResearch.WordTrace tailWord_8133706 prefixEnd_8133706 4176500680358859071568773 := by
  unfold tailWord_8133706
  simp only [CollatzResearch.WordTrace]
  refine ⟨74165157367744940808977243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197773752980653175490605981 74165157367744940808977243)
  ·
    refine ⟨111247736051617411213465865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74165157367744940808977243 111247736051617411213465865)
    ·
      refine ⟨83435802038713058410099399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111247736051617411213465865 83435802038713058410099399)
      ·
        refine ⟨125153703058069587615149099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83435802038713058410099399 125153703058069587615149099)
        ·
          refine ⟨187730554587104381422723649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125153703058069587615149099 187730554587104381422723649)
          ·
            refine ⟨140797915940328286067042737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187730554587104381422723649 140797915940328286067042737)
            ·
              refine ⟨105598436955246214550282053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140797915940328286067042737 105598436955246214550282053)
              ·
                refine ⟨19799706929108665228177885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105598436955246214550282053 19799706929108665228177885)
                ·
                  refine ⟨7424890098415749460566707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19799706929108665228177885 7424890098415749460566707)
                  ·
                    refine ⟨11137335147623624190850061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424890098415749460566707 11137335147623624190850061)
                    ·
                      refine ⟨4176500680358859071568773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137335147623624190850061 4176500680358859071568773)
                      ·
                        rfl

theorem cell23_8133706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_8133706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133706 prefixEnd_8133706 := by exact prefixLift 8133706
  have htrace : WordTrace (prefixWord ++ tailWord_8133706) baseStart_8133706 baseEnd_8133706 := by
    simpa [prefixWord, tailWord_8133706, baseEnd_8133706] using wordTrace_append hprefix tailTrace_8133706
  have hstable : (prefixWord ++ tailWord_8133706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133706).length < 2 ^ (prefixWord ++ tailWord_8133706).sum := by decide
  have hdescent : baseEnd_8133706 < baseStart_8133706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133716 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_8133716 : Nat := 118140960795 + 8133716 * 2 ^ 59
def prefixEnd_8133716 : Nat := 4983230072969 + 3 ^ 40 * 8133716 * 2
def baseEnd_8133716 : Nat := 4176505815165404032443727

theorem tailTrace_8133716 : CollatzResearch.WordTrace tailWord_8133716 prefixEnd_8133716 4176505815165404032443727 := by
  unfold tailWord_8133716
  simp only [CollatzResearch.WordTrace]
  refine ⟨148330497100471767471886501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197773996133962356629182001 148330497100471767471886501)
  ·
    refine ⟨27811968206338456400978719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148330497100471767471886501 27811968206338456400978719)
    ·
      refine ⟨41717952309507684601468079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27811968206338456400978719 41717952309507684601468079)
      ·
        refine ⟨62576928464261526902202119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41717952309507684601468079 62576928464261526902202119)
        ·
          refine ⟨93865392696392290353303179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62576928464261526902202119 93865392696392290353303179)
          ·
            refine ⟨140798089044588435529954769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93865392696392290353303179 140798089044588435529954769)
            ·
              refine ⟨105598566783441326647466077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140798089044588435529954769 105598566783441326647466077)
              ·
                refine ⟨39599462543790497492799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105598566783441326647466077 39599462543790497492799779)
                ·
                  refine ⟨59399193815685746239199669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39599462543790497492799779 59399193815685746239199669)
                  ·
                    refine ⟨5568674420220538709924969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59399193815685746239199669 5568674420220538709924969)
                    ·
                      refine ⟨4176505815165404032443727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568674420220538709924969 4176505815165404032443727)
                      ·
                        rfl

theorem cell23_8133716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_8133716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133716 prefixEnd_8133716 := by exact prefixLift 8133716
  have htrace : WordTrace (prefixWord ++ tailWord_8133716) baseStart_8133716 baseEnd_8133716 := by
    simpa [prefixWord, tailWord_8133716, baseEnd_8133716] using wordTrace_append hprefix tailTrace_8133716
  have hstable : (prefixWord ++ tailWord_8133716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133716).length < 2 ^ (prefixWord ++ tailWord_8133716).sum := by decide
  have hdescent : baseEnd_8133716 < baseStart_8133716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133756 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_8133756 : Nat := 118140960795 + 8133756 * 2 ^ 59
def prefixEnd_8133756 : Nat := 4983230072969 + 3 ^ 40 * 8133756 * 2
def baseEnd_8133756 : Nat := 1392175451463861291981181

theorem tailTrace_8133756 : CollatzResearch.WordTrace tailWord_8133756 prefixEnd_8133756 1392175451463861291981181 := by
  unfold tailWord_8133756
  simp only [CollatzResearch.WordTrace]
  refine ⟨148331226560399310887614561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197774968747199081183486081 148331226560399310887614561)
  ·
    refine ⟨111248419920299483165710921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148331226560399310887614561 111248419920299483165710921)
    ·
      refine ⟨83436314940224612374283191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111248419920299483165710921 83436314940224612374283191)
      ·
        refine ⟨125154472410336918561424787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83436314940224612374283191 125154472410336918561424787)
        ·
          refine ⟨187731708615505377842137181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125154472410336918561424787 187731708615505377842137181)
          ·
            refine ⟨70399390730814516690801443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187731708615505377842137181 70399390730814516690801443)
            ·
              refine ⟨105599086096221775036202165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70399390730814516690801443 105599086096221775036202165)
              ·
                refine ⟨9899914321520791409643953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105599086096221775036202165 9899914321520791409643953)
                ·
                  refine ⟨7424935741140593557232965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9899914321520791409643953 7424935741140593557232965)
                  ·
                    refine ⟨1392175451463861291981181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7424935741140593557232965 1392175451463861291981181)
                    ·
                      rfl

theorem cell23_8133756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_8133756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133756 prefixEnd_8133756 := by exact prefixLift 8133756
  have htrace : WordTrace (prefixWord ++ tailWord_8133756) baseStart_8133756 baseEnd_8133756 := by
    simpa [prefixWord, tailWord_8133756, baseEnd_8133756] using wordTrace_append hprefix tailTrace_8133756
  have hstable : (prefixWord ++ tailWord_8133756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133756).length < 2 ^ (prefixWord ++ tailWord_8133756).sum := by decide
  have hdescent : baseEnd_8133756 < baseStart_8133756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133763 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 3, 2, 2]
def baseStart_8133763 : Nat := 118140960795 + 8133763 * 2 ^ 59
def prefixEnd_8133763 : Nat := 4983230072969 + 3 ^ 40 * 8133763 * 2
def baseEnd_8133763 : Nat := 4176529948756165348556011

theorem tailTrace_8133763 : CollatzResearch.WordTrace tailWord_8133763 prefixEnd_8133763 4176529948756165348556011 := by
  unfold tailWord_8133763
  simp only [CollatzResearch.WordTrace]
  refine ⟨296662708431773261970733943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197775138954515507980489295 296662708431773261970733943)
  ·
    refine ⟨444994062647659892956100915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296662708431773261970733943 444994062647659892956100915)
    ·
      refine ⟨667491093971489839434151373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444994062647659892956100915 667491093971489839434151373)
      ·
        refine ⟨250309160239308689787806765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667491093971489839434151373 250309160239308689787806765)
        ·
          refine ⟨93865935089740758670427537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250309160239308689787806765 93865935089740758670427537)
          ·
            refine ⟨70399451317305569002820653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93865935089740758670427537 70399451317305569002820653)
            ·
              refine ⟨26399794243989588376057745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70399451317305569002820653 26399794243989588376057745)
              ·
                refine ⟨19799845682992191282043309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26399794243989588376057745 19799845682992191282043309)
                ·
                  refine ⟨7424942131122071730766241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19799845682992191282043309 7424942131122071730766241)
                  ·
                    refine ⟨5568706598341553798074681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7424942131122071730766241 5568706598341553798074681)
                    ·
                      refine ⟨4176529948756165348556011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568706598341553798074681 4176529948756165348556011)
                      ·
                        rfl

theorem cell23_8133763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_8133763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133763 prefixEnd_8133763 := by exact prefixLift 8133763
  have htrace : WordTrace (prefixWord ++ tailWord_8133763) baseStart_8133763 baseEnd_8133763 := by
    simpa [prefixWord, tailWord_8133763, baseEnd_8133763] using wordTrace_append hprefix tailTrace_8133763
  have hstable : (prefixWord ++ tailWord_8133763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133763).length < 2 ^ (prefixWord ++ tailWord_8133763).sum := by decide
  have hdescent : baseEnd_8133763 < baseStart_8133763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133783 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_8133783 : Nat := 118140960795 + 8133783 * 2 ^ 59
def prefixEnd_8133783 : Nat := 4983230072969 + 3 ^ 40 * 8133783 * 2
def baseEnd_8133783 : Nat := 4176540218369255270305919

theorem tailTrace_8133783 : CollatzResearch.WordTrace tailWord_8133783 prefixEnd_8133783 4176540218369255270305919 := by
  unfold tailWord_8133783
  simp only [CollatzResearch.WordTrace]
  refine ⟨296663437891700805386462003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197775625261133870257641335 296663437891700805386462003)
  ·
    refine ⟨444995156837551208079693005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296663437891700805386462003 444995156837551208079693005)
    ·
      refine ⟨166873183814081703029884877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444995156837551208079693005 166873183814081703029884877)
      ·
        refine ⟨62577443930280638636206829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166873183814081703029884877 62577443930280638636206829)
        ·
          refine ⟨23466541473855239488577561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62577443930280638636206829 23466541473855239488577561)
          ·
            refine ⟨17599906105391429616433171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23466541473855239488577561 17599906105391429616433171)
            ·
              refine ⟨26399859158087144424649757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17599906105391429616433171 26399859158087144424649757)
              ·
                refine ⟨9899947184282679159243659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26399859158087144424649757 9899947184282679159243659)
                ·
                  refine ⟨14849920776424018738865489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899947184282679159243659 14849920776424018738865489)
                  ·
                    refine ⟨11137440582318014054149117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14849920776424018738865489 11137440582318014054149117)
                    ·
                      refine ⟨4176540218369255270305919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137440582318014054149117 4176540218369255270305919)
                      ·
                        rfl

theorem cell23_8133783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_8133783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133783 prefixEnd_8133783 := by exact prefixLift 8133783
  have htrace : WordTrace (prefixWord ++ tailWord_8133783) baseStart_8133783 baseEnd_8133783 := by
    simpa [prefixWord, tailWord_8133783, baseEnd_8133783] using wordTrace_append hprefix tailTrace_8133783
  have hstable : (prefixWord ++ tailWord_8133783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133783).length < 2 ^ (prefixWord ++ tailWord_8133783).sum := by decide
  have hdescent : baseEnd_8133783 < baseStart_8133783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133790 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_8133790 : Nat := 118140960795 + 8133790 * 2 ^ 59
def prefixEnd_8133790 : Nat := 4983230072969 + 3 ^ 40 * 8133790 * 2
def baseEnd_8133790 : Nat := 1392181270911278914306129

theorem tailTrace_8133790 : CollatzResearch.WordTrace tailWord_8133790 prefixEnd_8133790 1392181270911278914306129 := by
  unfold tailWord_8133790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082961650334430697745853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197775795468450297054644549 37082961650334430697745853)
  ·
    refine ⟨13906110618875411511654695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37082961650334430697745853 13906110618875411511654695)
    ·
      refine ⟨20859165928313117267482043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13906110618875411511654695 20859165928313117267482043)
      ·
        refine ⟨31288748892469675901223065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20859165928313117267482043 31288748892469675901223065)
        ·
          refine ⟨23466561669352256925917299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31288748892469675901223065 23466561669352256925917299)
          ·
            refine ⟨35199842504028385388875949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23466561669352256925917299 35199842504028385388875949)
            ·
              refine ⟨13199940939010644520828481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35199842504028385388875949 13199940939010644520828481)
              ·
                refine ⟨9899955704257983390621361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13199940939010644520828481 9899955704257983390621361)
                ·
                  refine ⟨7424966778193487542966021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9899955704257983390621361 7424966778193487542966021)
                  ·
                    refine ⟨1392181270911278914306129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7424966778193487542966021 1392181270911278914306129)
                    ·
                      rfl

theorem cell23_8133790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_8133790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133790 prefixEnd_8133790 := by exact prefixLift 8133790
  have htrace : WordTrace (prefixWord ++ tailWord_8133790) baseStart_8133790 baseEnd_8133790 := by
    simpa [prefixWord, tailWord_8133790, baseEnd_8133790] using wordTrace_append hprefix tailTrace_8133790
  have hstable : (prefixWord ++ tailWord_8133790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133790).length < 2 ^ (prefixWord ++ tailWord_8133790).sum := by decide
  have hdescent : baseEnd_8133790 < baseStart_8133790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133823 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 1, 3, 2]
def baseStart_8133823 : Nat := 118140960795 + 8133823 * 2 ^ 59
def prefixEnd_8133823 : Nat := 4983230072969 + 3 ^ 40 * 8133823 * 2
def baseEnd_8133823 : Nat := 4176560757595435113805735

theorem tailTrace_8133823 : CollatzResearch.WordTrace tailWord_8133823 prefixEnd_8133823 4176560757595435113805735 := by
  unfold tailWord_8133823
  simp only [CollatzResearch.WordTrace]
  refine ⟨296664896811555892217918123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197776597874370594811945415 296664896811555892217918123)
  ·
    refine ⟨444997345217333838326877185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296664896811555892217918123 444997345217333838326877185)
    ·
      refine ⟨333748008913000378745157889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444997345217333838326877185 333748008913000378745157889)
      ·
        refine ⟨250311006684750284058868417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333748008913000378745157889 250311006684750284058868417)
        ·
          refine ⟨187733255013562713044151313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250311006684750284058868417 187733255013562713044151313)
          ·
            refine ⟨140799941260172034783113485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187733255013562713044151313 140799941260172034783113485)
            ·
              refine ⟨52799977972564513043667557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140799941260172034783113485 52799977972564513043667557)
              ·
                refine ⟨9899995869855846195687667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52799977972564513043667557 9899995869855846195687667)
                ·
                  refine ⟨14849993804783769293531501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899995869855846195687667 14849993804783769293531501)
                  ·
                    refine ⟨5568747676793913485074313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14849993804783769293531501 5568747676793913485074313)
                    ·
                      refine ⟨4176560757595435113805735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568747676793913485074313 4176560757595435113805735)
                      ·
                        rfl

theorem cell23_8133823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_8133823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133823 prefixEnd_8133823 := by exact prefixLift 8133823
  have htrace : WordTrace (prefixWord ++ tailWord_8133823) baseStart_8133823 baseEnd_8133823 := by
    simpa [prefixWord, tailWord_8133823, baseEnd_8133823] using wordTrace_append hprefix tailTrace_8133823
  have hstable : (prefixWord ++ tailWord_8133823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133823).length < 2 ^ (prefixWord ++ tailWord_8133823).sum := by decide
  have hdescent : baseEnd_8133823 < baseStart_8133823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133874 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_8133874 : Nat := 118140960795 + 8133874 * 2 ^ 59
def prefixEnd_8133874 : Nat := 4983230072969 + 3 ^ 40 * 8133874 * 2
def baseEnd_8133874 : Nat := 4176586945108814414268001

theorem tailTrace_8133874 : CollatzResearch.WordTrace tailWord_8133874 prefixEnd_8133874 4176586945108814414268001 := by
  unfold tailWord_8133874
  simp only [CollatzResearch.WordTrace]
  refine ⟨74166689233592781982006169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197777837956247418618683117 74166689233592781982006169)
  ·
    refine ⟨55625016925194586486504627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74166689233592781982006169 55625016925194586486504627)
    ·
      refine ⟨83437525387791879729756941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55625016925194586486504627 83437525387791879729756941)
      ·
        refine ⟨31289072020421954898658853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83437525387791879729756941 31289072020421954898658853)
        ·
          refine ⟨5866701003829116543498535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31289072020421954898658853 5866701003829116543498535)
          ·
            refine ⟨8800051505743674815247803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866701003829116543498535 8800051505743674815247803)
            ·
              refine ⟨13200077258615512222871705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800051505743674815247803 13200077258615512222871705)
              ·
                refine ⟨9900057943961634167153779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200077258615512222871705 9900057943961634167153779)
                ·
                  refine ⟨14850086915942451250730669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900057943961634167153779 14850086915942451250730669)
                  ·
                    refine ⟨5568782593478419219024001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14850086915942451250730669 5568782593478419219024001)
                    ·
                      refine ⟨4176586945108814414268001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568782593478419219024001 4176586945108814414268001)
                      ·
                        rfl

theorem cell23_8133874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_8133874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133874 prefixEnd_8133874 := by exact prefixLift 8133874
  have htrace : WordTrace (prefixWord ++ tailWord_8133874) baseStart_8133874 baseEnd_8133874 := by
    simpa [prefixWord, tailWord_8133874, baseEnd_8133874] using wordTrace_append hprefix tailTrace_8133874
  have hstable : (prefixWord ++ tailWord_8133874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133874).length < 2 ^ (prefixWord ++ tailWord_8133874).sum := by decide
  have hdescent : baseEnd_8133874 < baseStart_8133874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133916 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_8133916 : Nat := 118140960795 + 8133916 * 2 ^ 59
def prefixEnd_8133916 : Nat := 4983230072969 + 3 ^ 40 * 8133916 * 2
def baseEnd_8133916 : Nat := 4176608511296303249942807

theorem tailTrace_8133916 : CollatzResearch.WordTrace tailWord_8133916 prefixEnd_8133916 4176608511296303249942807 := by
  unfold tailWord_8133916
  simp only [CollatzResearch.WordTrace]
  refine ⟨148334144400109484550526801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197778859200145979400702401 148334144400109484550526801)
  ·
    refine ⟨111250608300082113412895101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148334144400109484550526801 111250608300082113412895101)
    ·
      refine ⟨41718978112530792529835663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111250608300082113412895101 41718978112530792529835663)
      ·
        refine ⟨62578467168796188794753495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41718978112530792529835663 62578467168796188794753495)
        ·
          refine ⟨93867700753194283192130243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62578467168796188794753495 93867700753194283192130243)
          ·
            refine ⟨140801551129791424788195365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93867700753194283192130243 140801551129791424788195365)
            ·
              refine ⟨26400290836835892147786631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140801551129791424788195365 26400290836835892147786631)
              ·
                refine ⟨39600436255253838221679947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26400290836835892147786631 39600436255253838221679947)
                ·
                  refine ⟨59400654382880757332519921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39600436255253838221679947 59400654382880757332519921)
                  ·
                    refine ⟨44550490787160567999389941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59400654382880757332519921 44550490787160567999389941)
                    ·
                      refine ⟨4176608511296303249942807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44550490787160567999389941 4176608511296303249942807)
                      ·
                        rfl

theorem cell23_8133916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_8133916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133916 prefixEnd_8133916 := by exact prefixLift 8133916
  have htrace : WordTrace (prefixWord ++ tailWord_8133916) baseStart_8133916 baseEnd_8133916 := by
    simpa [prefixWord, tailWord_8133916, baseEnd_8133916] using wordTrace_append hprefix tailTrace_8133916
  have hstable : (prefixWord ++ tailWord_8133916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133916).length < 2 ^ (prefixWord ++ tailWord_8133916).sum := by decide
  have hdescent : baseEnd_8133916 < baseStart_8133916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133966 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_8133966 : Nat := 118140960795 + 8133966 * 2 ^ 59
def prefixEnd_8133966 : Nat := 4983230072969 + 3 ^ 40 * 8133966 * 2
def baseEnd_8133966 : Nat := 464070465036558672701953

theorem tailTrace_8133966 : CollatzResearch.WordTrace tailWord_8133966 prefixEnd_8133966 464070465036558672701953 := by
  unfold tailWord_8133966
  simp only [CollatzResearch.WordTrace]
  refine ⟨37083764056254728455046719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197780074966691885093582501 37083764056254728455046719)
  ·
    refine ⟨55625646084382092682570079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37083764056254728455046719 55625646084382092682570079)
    ·
      refine ⟨83438469126573139023855119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55625646084382092682570079 83438469126573139023855119)
      ·
        refine ⟨125157703689859708535782679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83438469126573139023855119 125157703689859708535782679)
        ·
          refine ⟨187736555534789562803674019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125157703689859708535782679 187736555534789562803674019)
          ·
            refine ⟨281604833302184344205511029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187736555534789562803674019 281604833302184344205511029)
            ·
              refine ⟨26400453122079782269266659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281604833302184344205511029 26400453122079782269266659)
              ·
                refine ⟨39600679683119673403899989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26400453122079782269266659 39600679683119673403899989)
                ·
                  refine ⟨464070465036558672701953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39600679683119673403899989 464070465036558672701953)
                  ·
                    rfl

theorem cell23_8133966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_8133966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133966 prefixEnd_8133966 := by exact prefixLift 8133966
  have htrace : WordTrace (prefixWord ++ tailWord_8133966) baseStart_8133966 baseEnd_8133966 := by
    simpa [prefixWord, tailWord_8133966, baseEnd_8133966] using wordTrace_append hprefix tailTrace_8133966
  have hstable : (prefixWord ++ tailWord_8133966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133966).length < 2 ^ (prefixWord ++ tailWord_8133966).sum := by decide
  have hdescent : baseEnd_8133966 < baseStart_8133966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8133993 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 3]
def baseStart_8133993 : Nat := 118140960795 + 8133993 * 2 ^ 59
def prefixEnd_8133993 : Nat := 4983230072969 + 3 ^ 40 * 8133993 * 2
def baseEnd_8133993 : Nat := 4176648049306699448679953

theorem tailTrace_8133993 : CollatzResearch.WordTrace tailWord_8133993 prefixEnd_8133993 4176648049306699448679953 := by
  unfold tailWord_8133993
  simp only [CollatzResearch.WordTrace]
  refine ⟨296671097220940011251606633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197780731480626674167737755 296671097220940011251606633)
  ·
    refine ⟨222503322915705008438704975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296671097220940011251606633 222503322915705008438704975)
    ·
      refine ⟨333754984373557512658057463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222503322915705008438704975 333754984373557512658057463)
      ·
        refine ⟨500632476560336268987086195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333754984373557512658057463 500632476560336268987086195)
        ·
          refine ⟨750948714840504403480629293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500632476560336268987086195 750948714840504403480629293)
          ·
            refine ⟨281605768065189151305235985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750948714840504403480629293 281605768065189151305235985)
            ·
              refine ⟨211204326048891863478926989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281605768065189151305235985 211204326048891863478926989)
              ·
                refine ⟨79201622268334448804597621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211204326048891863478926989 79201622268334448804597621)
                ·
                  refine ⟨7425152087656354575431027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79201622268334448804597621 7425152087656354575431027)
                  ·
                    refine ⟨11137728131484531863146541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425152087656354575431027 11137728131484531863146541)
                    ·
                      refine ⟨4176648049306699448679953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137728131484531863146541 4176648049306699448679953)
                      ·
                        rfl

theorem cell23_8133993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_8133993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8133993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8133993 prefixEnd_8133993 := by exact prefixLift 8133993
  have htrace : WordTrace (prefixWord ++ tailWord_8133993) baseStart_8133993 baseEnd_8133993 := by
    simpa [prefixWord, tailWord_8133993, baseEnd_8133993] using wordTrace_append hprefix tailTrace_8133993
  have hstable : (prefixWord ++ tailWord_8133993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8133993).length < 2 ^ (prefixWord ++ tailWord_8133993).sum := by decide
  have hdescent : baseEnd_8133993 < baseStart_8133993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8133993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134013 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_8134013 : Nat := 118140960795 + 8134013 * 2 ^ 59
def prefixEnd_8134013 : Nat := 4983230072969 + 3 ^ 40 * 8134013 * 2
def baseEnd_8134013 : Nat := 1392219439639929790143287

theorem tailTrace_8134013 : CollatzResearch.WordTrace tailWord_8134013 prefixEnd_8134013 1392219439639929790143287 := by
  unfold tailWord_8134013
  simp only [CollatzResearch.WordTrace]
  refine ⟨296671826680867554667334693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197781217787245036444889795 296671826680867554667334693)
  ·
    refine ⟨55625967502662666500125255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296671826680867554667334693 55625967502662666500125255)
    ·
      refine ⟨83438951253993999750187883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55625967502662666500125255 83438951253993999750187883)
      ·
        refine ⟨125158426880990999625281825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83438951253993999750187883 125158426880990999625281825)
        ·
          refine ⟨93868820160743249718961369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125158426880990999625281825 93868820160743249718961369)
          ·
            refine ⟨70401615120557437289221027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93868820160743249718961369 70401615120557437289221027)
            ·
              refine ⟨105602422680836155933831541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70401615120557437289221027 105602422680836155933831541)
              ·
                refine ⟨9900227126328389618796707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105602422680836155933831541 9900227126328389618796707)
                ·
                  refine ⟨14850340689492584428195061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900227126328389618796707 14850340689492584428195061)
                  ·
                    refine ⟨1392219439639929790143287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14850340689492584428195061 1392219439639929790143287)
                    ·
                      rfl

theorem cell23_8134013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_8134013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134013 prefixEnd_8134013 := by exact prefixLift 8134013
  have htrace : WordTrace (prefixWord ++ tailWord_8134013) baseStart_8134013 baseEnd_8134013 := by
    simpa [prefixWord, tailWord_8134013, baseEnd_8134013] using wordTrace_append hprefix tailTrace_8134013
  have hstable : (prefixWord ++ tailWord_8134013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134013).length < 2 ^ (prefixWord ++ tailWord_8134013).sum := by decide
  have hdescent : baseEnd_8134013 < baseStart_8134013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134014 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8134014 : Nat := 118140960795 + 8134014 * 2 ^ 59
def prefixEnd_8134014 : Nat := 4983230072969 + 3 ^ 40 * 8134014 * 2
def baseEnd_8134014 : Nat := 4176658832400443866517357

theorem tailTrace_8134014 : CollatzResearch.WordTrace tailWord_8134014 prefixEnd_8134014 4176658832400443866517357 := by
  unfold tailWord_8134014
  simp only [CollatzResearch.WordTrace]
  refine ⟨37083982894232991479765137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197781242102575954558747397 37083982894232991479765137)
  ·
    refine ⟨27812987170674743609823853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37083982894232991479765137 27812987170674743609823853)
    ·
      refine ⟨10429870189003028853683945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27812987170674743609823853 10429870189003028853683945)
      ·
        refine ⟨7822402641752271640262959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10429870189003028853683945 7822402641752271640262959)
        ·
          refine ⟨11733603962628407460394439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822402641752271640262959 11733603962628407460394439)
          ·
            refine ⟨17600405943942611190591659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11733603962628407460394439 17600405943942611190591659)
            ·
              refine ⟨26400608915913916785887489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17600405943942611190591659 26400608915913916785887489)
              ·
                refine ⟨19800456686935437589415617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26400608915913916785887489 19800456686935437589415617)
                ·
                  refine ⟨14850342515201578192061713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19800456686935437589415617 14850342515201578192061713)
                  ·
                    refine ⟨11137756886401183644046285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14850342515201578192061713 11137756886401183644046285)
                    ·
                      refine ⟨4176658832400443866517357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137756886401183644046285 4176658832400443866517357)
                      ·
                        rfl

theorem cell23_8134014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8134014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134014 prefixEnd_8134014 := by exact prefixLift 8134014
  have htrace : WordTrace (prefixWord ++ tailWord_8134014) baseStart_8134014 baseEnd_8134014 := by
    simpa [prefixWord, tailWord_8134014, baseEnd_8134014] using wordTrace_append hprefix tailTrace_8134014
  have hstable : (prefixWord ++ tailWord_8134014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134014).length < 2 ^ (prefixWord ++ tailWord_8134014).sum := by decide
  have hdescent : baseEnd_8134014 < baseStart_8134014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134020 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_8134020 : Nat := 118140960795 + 8134020 * 2 ^ 59
def prefixEnd_8134020 : Nat := 4983230072969 + 3 ^ 40 * 8134020 * 2
def baseEnd_8134020 : Nat := 4176661913284370843042329

theorem tailTrace_8134020 : CollatzResearch.WordTrace tailWord_8134020 prefixEnd_8134020 4176661913284370843042329 := by
  unfold tailWord_8134020
  simp only [CollatzResearch.WordTrace]
  refine ⟨148336040995921097431419757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197781387994561463241893009 148336040995921097431419757)
  ·
    refine ⟨55626015373470411536782409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148336040995921097431419757 55626015373470411536782409)
    ·
      refine ⟨41719511530102808652586807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55626015373470411536782409 41719511530102808652586807)
      ·
        refine ⟨62579267295154212978880211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41719511530102808652586807 62579267295154212978880211)
        ·
          refine ⟨93868900942731319468320317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62579267295154212978880211 93868900942731319468320317)
          ·
            refine ⟨35200837853524244800620119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93868900942731319468320317 35200837853524244800620119)
            ·
              refine ⟨52801256780286367200930179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35200837853524244800620119 52801256780286367200930179)
              ·
                refine ⟨79201885170429550801395269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52801256780286367200930179 79201885170429550801395269)
                ·
                  refine ⟨14850353469455540775261613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79201885170429550801395269 14850353469455540775261613)
                  ·
                    refine ⟨5568882551045827790723105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14850353469455540775261613 5568882551045827790723105)
                    ·
                      refine ⟨4176661913284370843042329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568882551045827790723105 4176661913284370843042329)
                      ·
                        rfl

theorem cell23_8134020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_8134020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134020 prefixEnd_8134020 := by exact prefixLift 8134020
  have htrace : WordTrace (prefixWord ++ tailWord_8134020) baseStart_8134020 baseEnd_8134020 := by
    simpa [prefixWord, tailWord_8134020, baseEnd_8134020] using wordTrace_append hprefix tailTrace_8134020
  have hstable : (prefixWord ++ tailWord_8134020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134020).length < 2 ^ (prefixWord ++ tailWord_8134020).sum := by decide
  have hdescent : baseEnd_8134020 < baseStart_8134020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134034 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_8134034 : Nat := 118140960795 + 8134034 * 2 ^ 59
def prefixEnd_8134034 : Nat := 4983230072969 + 3 ^ 40 * 8134034 * 2
def baseEnd_8134034 : Nat := 464074344668170420918585

theorem tailTrace_8134034 : CollatzResearch.WordTrace tailWord_8134034 prefixEnd_8134034 464074344668170420918585 := by
  unfold tailWord_8134034
  simp only [CollatzResearch.WordTrace]
  refine ⟨74168148153447868813462289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197781728409194316835899437 74168148153447868813462289)
  ·
    refine ⟨55626111115085901610096717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74168148153447868813462289 55626111115085901610096717)
    ·
      refine ⟨20859791668157213103786269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55626111115085901610096717 20859791668157213103786269)
      ·
        refine ⟨7822421875558954913919851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20859791668157213103786269 7822421875558954913919851)
        ·
          refine ⟨11733632813338432370879777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822421875558954913919851 11733632813338432370879777)
          ·
            refine ⟨8800224610003824278159833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11733632813338432370879777 8800224610003824278159833)
            ·
              refine ⟨6600168457502868208619875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8800224610003824278159833 6600168457502868208619875)
              ·
                refine ⟨9900252686254302312929813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600168457502868208619875 9900252686254302312929813)
                ·
                  refine ⟨464074344668170420918585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9900252686254302312929813 464074344668170420918585)
                  ·
                    rfl

theorem cell23_8134034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_8134034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134034 prefixEnd_8134034 := by exact prefixLift 8134034
  have htrace : WordTrace (prefixWord ++ tailWord_8134034) baseStart_8134034 baseEnd_8134034 := by
    simpa [prefixWord, tailWord_8134034, baseEnd_8134034] using wordTrace_append hprefix tailTrace_8134034
  have hstable : (prefixWord ++ tailWord_8134034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134034).length < 2 ^ (prefixWord ++ tailWord_8134034).sum := by decide
  have hdescent : baseEnd_8134034 < baseStart_8134034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134050 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_8134050 : Nat := 118140960795 + 8134050 * 2 ^ 59
def prefixEnd_8134050 : Nat := 4983230072969 + 3 ^ 40 * 8134050 * 2
def baseEnd_8134050 : Nat := 4176677317704005725667191

theorem tailTrace_8134050 : CollatzResearch.WordTrace tailWord_8134050 prefixEnd_8134050 4176677317704005725667191 := by
  unfold tailWord_8134050
  simp only [CollatzResearch.WordTrace]
  refine ⟨74168294045433377496607901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197782117454489006657621069 74168294045433377496607901)
  ·
    refine ⟨27813110267037516561227963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74168294045433377496607901 27813110267037516561227963)
    ·
      refine ⟨41719665400556274841841945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27813110267037516561227963 41719665400556274841841945)
      ·
        refine ⟨31289749050417206131381459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41719665400556274841841945 31289749050417206131381459)
        ·
          refine ⟨46934623575625809197072189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31289749050417206131381459 46934623575625809197072189)
          ·
            refine ⟨17600483840859678448902071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46934623575625809197072189 17600483840859678448902071)
            ·
              refine ⟨26400725761289517673353107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17600483840859678448902071 26400725761289517673353107)
              ·
                refine ⟨39601088641934276510029661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26400725761289517673353107 39601088641934276510029661)
                ·
                  refine ⟨14850408240725353691261123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39601088641934276510029661 14850408240725353691261123)
                  ·
                    refine ⟨22275612361088030536891685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14850408240725353691261123 22275612361088030536891685)
                    ·
                      refine ⟨4176677317704005725667191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22275612361088030536891685 4176677317704005725667191)
                      ·
                        rfl

theorem cell23_8134050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_8134050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134050 prefixEnd_8134050 := by exact prefixLift 8134050
  have htrace : WordTrace (prefixWord ++ tailWord_8134050) baseStart_8134050 baseEnd_8134050 := by
    simpa [prefixWord, tailWord_8134050, baseEnd_8134050] using wordTrace_append hprefix tailTrace_8134050
  have hstable : (prefixWord ++ tailWord_8134050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134050).length < 2 ^ (prefixWord ++ tailWord_8134050).sum := by decide
  have hdescent : baseEnd_8134050 < baseStart_8134050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134073 : List Nat := [1, 2, 1, 4, 5, 10]
def baseStart_8134073 : Nat := 118140960795 + 8134073 * 2 ^ 59
def prefixEnd_8134073 : Nat := 4983230072969 + 3 ^ 40 * 8134073 * 2
def baseEnd_8134073 : Nat := 17188021101889132245595

theorem tailTrace_8134073 : CollatzResearch.WordTrace tailWord_8134073 prefixEnd_8134073 17188021101889132245595 := by
  unfold tailWord_8134073
  simp only [CollatzResearch.WordTrace]
  refine ⟨296674015060650184914518873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197782676707100123276345915 296674015060650184914518873)
  ·
    refine ⟨222505511295487638685889155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296674015060650184914518873 222505511295487638685889155)
    ·
      refine ⟨333758266943231458028833733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222505511295487638685889155 333758266943231458028833733)
      ·
        refine ⟨62579675051855898380406325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333758266943231458028833733 62579675051855898380406325)
        ·
          refine ⟨5866844536111490473163093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62579675051855898380406325 5866844536111490473163093)
          ·
            refine ⟨17188021101889132245595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5866844536111490473163093 17188021101889132245595)
            ·
              rfl

theorem cell23_8134073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 10].length) (baseStart_8134073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134073 prefixEnd_8134073 := by exact prefixLift 8134073
  have htrace : WordTrace (prefixWord ++ tailWord_8134073) baseStart_8134073 baseEnd_8134073 := by
    simpa [prefixWord, tailWord_8134073, baseEnd_8134073] using wordTrace_append hprefix tailTrace_8134073
  have hstable : (prefixWord ++ tailWord_8134073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134073).length < 2 ^ (prefixWord ++ tailWord_8134073).sum := by decide
  have hdescent : baseEnd_8134073 < baseStart_8134073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134134 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_8134134 : Nat := 118140960795 + 8134134 * 2 ^ 59
def prefixEnd_8134134 : Nat := 4983230072969 + 3 ^ 40 * 8134134 * 2
def baseEnd_8134134 : Nat := 4176720450078983397016805

theorem tailTrace_8134134 : CollatzResearch.WordTrace tailWord_8134134 prefixEnd_8134134 4176720450078983397016805 := by
  unfold tailWord_8134134
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542264994589324520780591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197784159942286128221659637 18542264994589324520780591)
  ·
    refine ⟨27813397491883986781170887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18542264994589324520780591 27813397491883986781170887)
    ·
      refine ⟨41720096237825980171756331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27813397491883986781170887 41720096237825980171756331)
      ·
        refine ⟨62580144356738970257634497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41720096237825980171756331 62580144356738970257634497)
        ·
          refine ⟨46935108267554227693225873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62580144356738970257634497 46935108267554227693225873)
          ·
            refine ⟨35201331200665670769919405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46935108267554227693225873 35201331200665670769919405)
            ·
              refine ⟨13200499200249626538719777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35201331200665670769919405 13200499200249626538719777)
              ·
                refine ⟨9900374400187219904039833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200499200249626538719777 9900374400187219904039833)
                ·
                  refine ⟨7425280800140414928029875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9900374400187219904039833 7425280800140414928029875)
                  ·
                    refine ⟨11137921200210622392044813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425280800140414928029875 11137921200210622392044813)
                    ·
                      refine ⟨4176720450078983397016805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137921200210622392044813 4176720450078983397016805)
                      ·
                        rfl

theorem cell23_8134134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_8134134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134134 prefixEnd_8134134 := by exact prefixLift 8134134
  have htrace : WordTrace (prefixWord ++ tailWord_8134134) baseStart_8134134 baseEnd_8134134 := by
    simpa [prefixWord, tailWord_8134134, baseEnd_8134134] using wordTrace_append hprefix tailTrace_8134134
  have hstable : (prefixWord ++ tailWord_8134134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134134).length < 2 ^ (prefixWord ++ tailWord_8134134).sum := by decide
  have hdescent : baseEnd_8134134 < baseStart_8134134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134140 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_8134140 : Nat := 118140960795 + 8134140 * 2 ^ 59
def prefixEnd_8134140 : Nat := 4983230072969 + 3 ^ 40 * 8134140 * 2
def baseEnd_8134140 : Nat := 4176723530962910373541777

theorem tailTrace_8134140 : CollatzResearch.WordTrace tailWord_8134140 prefixEnd_8134140 4176723530962910373541777 := by
  unfold tailWord_8134140
  simp only [CollatzResearch.WordTrace]
  refine ⟨148338229375703727678603937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197784305834271636904805249 148338229375703727678603937)
  ·
    refine ⟨111253672031777795758952953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148338229375703727678603937 111253672031777795758952953)
    ·
      refine ⟨83440254023833346819214715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111253672031777795758952953 83440254023833346819214715)
      ·
        refine ⟨125160381035750020228822073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83440254023833346819214715 125160381035750020228822073)
        ·
          refine ⟨93870285776812515171616555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125160381035750020228822073 93870285776812515171616555)
          ·
            refine ⟨140805428665218772757424833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93870285776812515171616555 140805428665218772757424833)
            ·
              refine ⟨105604071498914079568068625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140805428665218772757424833 105604071498914079568068625)
              ·
                refine ⟨79203053624185559676051469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105604071498914079568068625 79203053624185559676051469)
                ·
                  refine ⟨29701145109069584878519301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79203053624185559676051469 29701145109069584878519301)
                  ·
                    refine ⟨5568964707950547164722369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29701145109069584878519301 5568964707950547164722369)
                    ·
                      refine ⟨4176723530962910373541777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5568964707950547164722369 4176723530962910373541777)
                      ·
                        rfl

theorem cell23_8134140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_8134140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134140 prefixEnd_8134140 := by exact prefixLift 8134140
  have htrace : WordTrace (prefixWord ++ tailWord_8134140) baseStart_8134140 baseEnd_8134140 := by
    simpa [prefixWord, tailWord_8134140, baseEnd_8134140] using wordTrace_append hprefix tailTrace_8134140
  have hstable : (prefixWord ++ tailWord_8134140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134140).length < 2 ^ (prefixWord ++ tailWord_8134140).sum := by decide
  have hdescent : baseEnd_8134140 < baseStart_8134140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134143 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_8134143 : Nat := 118140960795 + 8134143 * 2 ^ 59
def prefixEnd_8134143 : Nat := 4983230072969 + 3 ^ 40 * 8134143 * 2
def baseEnd_8134143 : Nat := 4176725071404873861804263

theorem tailTrace_8134143 : CollatzResearch.WordTrace tailWord_8134143 prefixEnd_8134143 4176725071404873861804263 := by
  unfold tailWord_8134143
  simp only [CollatzResearch.WordTrace]
  refine ⟨296676568170396586869567083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197784378780264391246378055 296676568170396586869567083)
  ·
    refine ⟨445014852255594880304350625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296676568170396586869567083 445014852255594880304350625)
    ·
      refine ⟨333761139191696160228262969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445014852255594880304350625 333761139191696160228262969)
      ·
        refine ⟨250320854393772120171197227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333761139191696160228262969 250320854393772120171197227)
        ·
          refine ⟨375481281590658180256795841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250320854393772120171197227 375481281590658180256795841)
          ·
            refine ⟨281610961192993635192596881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375481281590658180256795841 281610961192993635192596881)
            ·
              refine ⟨211208220894745226394447661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281610961192993635192596881 211208220894745226394447661)
              ·
                refine ⟨79203082835529459897917873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211208220894745226394447661 79203082835529459897917873)
                ·
                  refine ⟨59402312126647094923438405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79203082835529459897917873 59402312126647094923438405)
                  ·
                    refine ⟨11137933523746330298144701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59402312126647094923438405 11137933523746330298144701)
                    ·
                      refine ⟨4176725071404873861804263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11137933523746330298144701 4176725071404873861804263)
                      ·
                        rfl

theorem cell23_8134143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_8134143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134143 prefixEnd_8134143 := by exact prefixLift 8134143
  have htrace : WordTrace (prefixWord ++ tailWord_8134143) baseStart_8134143 baseEnd_8134143 := by
    simpa [prefixWord, tailWord_8134143, baseEnd_8134143] using wordTrace_append hprefix tailTrace_8134143
  have hstable : (prefixWord ++ tailWord_8134143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134143).length < 2 ^ (prefixWord ++ tailWord_8134143).sum := by decide
  have hdescent : baseEnd_8134143 < baseStart_8134143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134153 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_8134153 : Nat := 118140960795 + 8134153 * 2 ^ 59
def prefixEnd_8134153 : Nat := 4983230072969 + 3 ^ 40 * 8134153 * 2
def baseEnd_8134153 : Nat := 4176730206211418822679217

theorem tailTrace_8134153 : CollatzResearch.WordTrace tailWord_8134153 prefixEnd_8134153 4176730206211418822679217 := by
  unfold tailWord_8134153
  simp only [CollatzResearch.WordTrace]
  refine ⟨296676932900360358577431113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197784621933573572384954075 296676932900360358577431113)
  ·
    refine ⟨222507699675270268933073335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296676932900360358577431113 222507699675270268933073335)
    ·
      refine ⟨333761549512905403399610003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222507699675270268933073335 333761549512905403399610003)
      ·
        refine ⟨500642324269358105099415005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333761549512905403399610003 500642324269358105099415005)
        ·
          refine ⟨187740871601009289412280627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500642324269358105099415005 187740871601009289412280627)
          ·
            refine ⟨281611307401513934118420941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187740871601009289412280627 281611307401513934118420941)
            ·
              refine ⟨105604240275567725294407853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281611307401513934118420941 105604240275567725294407853)
              ·
                refine ⟨39601590103337896985402945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105604240275567725294407853 39601590103337896985402945)
                ·
                  refine ⟨29701192577503422739052209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39601590103337896985402945 29701192577503422739052209)
                  ·
                    refine ⟨22275894433127567054289157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29701192577503422739052209 22275894433127567054289157)
                    ·
                      refine ⟨4176730206211418822679217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22275894433127567054289157 4176730206211418822679217)
                      ·
                        rfl

theorem cell23_8134153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_8134153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134153 prefixEnd_8134153 := by exact prefixLift 8134153
  have htrace : WordTrace (prefixWord ++ tailWord_8134153) baseStart_8134153 baseEnd_8134153 := by
    simpa [prefixWord, tailWord_8134153, baseEnd_8134153] using wordTrace_append hprefix tailTrace_8134153
  have hstable : (prefixWord ++ tailWord_8134153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134153).length < 2 ^ (prefixWord ++ tailWord_8134153).sum := by decide
  have hdescent : baseEnd_8134153 < baseStart_8134153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134163 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 7]
def baseStart_8134163 : Nat := 118140960795 + 8134163 * 2 ^ 59
def prefixEnd_8134163 : Nat := 4983230072969 + 3 ^ 40 * 8134163 * 2
def baseEnd_8134163 : Nat := 464081704557551531506019

theorem tailTrace_8134163 : CollatzResearch.WordTrace tailWord_8134163 prefixEnd_8134163 464081704557551531506019 := by
  unfold tailWord_8134163
  simp only [CollatzResearch.WordTrace]
  refine ⟨296677297630324130285295143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197784865086882753523530095 296677297630324130285295143)
  ·
    refine ⟨445015946445486195427942715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296677297630324130285295143 445015946445486195427942715)
    ·
      refine ⟨667523919668229293141914073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445015946445486195427942715 667523919668229293141914073)
      ·
        refine ⟨500642939751171969856435555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667523919668229293141914073 500642939751171969856435555)
        ·
          refine ⟨750964409626757954784653333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500642939751171969856435555 750964409626757954784653333)
          ·
            refine ⟨35201456701254279130530625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 750964409626757954784653333 35201456701254279130530625)
            ·
              refine ⟨26401092525940709347897969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35201456701254279130530625 26401092525940709347897969)
              ·
                refine ⟨19800819394455532010923477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26401092525940709347897969 19800819394455532010923477)
                ·
                  refine ⟨464081704557551531506019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19800819394455532010923477 464081704557551531506019)
                  ·
                    rfl

theorem cell23_8134163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 7].length) (baseStart_8134163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134163 prefixEnd_8134163 := by exact prefixLift 8134163
  have htrace : WordTrace (prefixWord ++ tailWord_8134163) baseStart_8134163 baseEnd_8134163 := by
    simpa [prefixWord, tailWord_8134163, baseEnd_8134163] using wordTrace_append hprefix tailTrace_8134163
  have hstable : (prefixWord ++ tailWord_8134163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134163).length < 2 ^ (prefixWord ++ tailWord_8134163).sum := by decide
  have hdescent : baseEnd_8134163 < baseStart_8134163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134307 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 4, 3, 2]
def baseStart_8134307 : Nat := 118140960795 + 8134307 * 2 ^ 59
def prefixEnd_8134307 : Nat := 4983230072969 + 3 ^ 40 * 8134307 * 2
def baseEnd_8134307 : Nat := 4176809282232211220153509

theorem tailTrace_8134307 : CollatzResearch.WordTrace tailWord_8134307 prefixEnd_8134307 4176809282232211220153509 := by
  unfold tailWord_8134307
  simp only [CollatzResearch.WordTrace]
  refine ⟨296682549741802442878537175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197788366494534961919024783 296682549741802442878537175)
  ·
    refine ⟨445023824612703664317805763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296682549741802442878537175 445023824612703664317805763)
    ·
      refine ⟨667535736919055496476708645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445023824612703664317805763 667535736919055496476708645)
      ·
        refine ⟨125162950672322905589382871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 667535736919055496476708645 125162950672322905589382871)
        ·
          refine ⟨187744426008484358384074307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125162950672322905589382871 187744426008484358384074307)
          ·
            refine ⟨281616639012726537576111461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187744426008484358384074307 281616639012726537576111461)
            ·
              refine ⟨52803119814886225795520899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281616639012726537576111461 52803119814886225795520899)
              ·
                refine ⟨79204679722329338693281349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52803119814886225795520899 79204679722329338693281349)
                ·
                  refine ⟨14850877447936751004990253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79204679722329338693281349 14850877447936751004990253)
                  ·
                    refine ⟨5569079042976281626871345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14850877447936751004990253 5569079042976281626871345)
                    ·
                      refine ⟨4176809282232211220153509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569079042976281626871345 4176809282232211220153509)
                      ·
                        rfl

theorem cell23_8134307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_8134307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134307 prefixEnd_8134307 := by exact prefixLift 8134307
  have htrace : WordTrace (prefixWord ++ tailWord_8134307) baseStart_8134307 baseEnd_8134307 := by
    simpa [prefixWord, tailWord_8134307, baseEnd_8134307] using wordTrace_append hprefix tailTrace_8134307
  have hstable : (prefixWord ++ tailWord_8134307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134307).length < 2 ^ (prefixWord ++ tailWord_8134307).sum := by decide
  have hdescent : baseEnd_8134307 < baseStart_8134307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134320 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_8134320 : Nat := 118140960795 + 8134320 * 2 ^ 59
def prefixEnd_8134320 : Nat := 4983230072969 + 3 ^ 40 * 8134320 * 2
def baseEnd_8134320 : Nat := 4176815957480719669290949

theorem tailTrace_8134320 : CollatzResearch.WordTrace tailWord_8134320 prefixEnd_8134320 4176815957480719669290949 := by
  unfold tailWord_8134320
  simp only [CollatzResearch.WordTrace]
  refine ⟨148341511945377673049380207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197788682593836897399173609 148341511945377673049380207)
  ·
    refine ⟨222512267918066509574070311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148341511945377673049380207 222512267918066509574070311)
    ·
      refine ⟨333768401877099764361105467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222512267918066509574070311 333768401877099764361105467)
      ·
        refine ⟨500652602815649646541658201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333768401877099764361105467 500652602815649646541658201)
        ·
          refine ⟨375489452111737234906243651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500652602815649646541658201 375489452111737234906243651)
          ·
            refine ⟨563234178167605852359365477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375489452111737234906243651 563234178167605852359365477)
            ·
              refine ⟨105606408406426097317381027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 563234178167605852359365477 105606408406426097317381027)
              ·
                refine ⟨158409612609639145976071541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105606408406426097317381027 158409612609639145976071541)
                ·
                  refine ⟨14850901182153669935256707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158409612609639145976071541 14850901182153669935256707)
                  ·
                    refine ⟨22276351773230504902885061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14850901182153669935256707 22276351773230504902885061)
                    ·
                      refine ⟨4176815957480719669290949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22276351773230504902885061 4176815957480719669290949)
                      ·
                        rfl

theorem cell23_8134320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_8134320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134320 prefixEnd_8134320 := by exact prefixLift 8134320
  have htrace : WordTrace (prefixWord ++ tailWord_8134320) baseStart_8134320 baseEnd_8134320 := by
    simpa [prefixWord, tailWord_8134320, baseEnd_8134320] using wordTrace_append hprefix tailTrace_8134320
  have hstable : (prefixWord ++ tailWord_8134320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134320).length < 2 ^ (prefixWord ++ tailWord_8134320).sum := by decide
  have hdescent : baseEnd_8134320 < baseStart_8134320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134334 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_8134334 : Nat := 118140960795 + 8134334 * 2 ^ 59
def prefixEnd_8134334 : Nat := 4983230072969 + 3 ^ 40 * 8134334 * 2
def baseEnd_8134334 : Nat := 1392274382069960871505295

theorem tailTrace_8134334 : CollatzResearch.WordTrace tailWord_8134334 prefixEnd_8134334 1392274382069960871505295 := by
  unfold tailWord_8134334
  simp only [CollatzResearch.WordTrace]
  refine ⟨37085441814088078311221257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197789023008469750993180037 37085441814088078311221257)
  ·
    refine ⟨27814081360566058733415943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37085441814088078311221257 27814081360566058733415943)
    ·
      refine ⟨41721122040849088100123915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27814081360566058733415943 41721122040849088100123915)
      ·
        refine ⟨62581683061273632150185873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41721122040849088100123915 62581683061273632150185873)
        ·
          refine ⟨46936262295955224112639405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62581683061273632150185873 46936262295955224112639405)
          ·
            refine ⟨17601098360983209042239777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46936262295955224112639405 17601098360983209042239777)
            ·
              refine ⟨13200823770737406781679833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17601098360983209042239777 13200823770737406781679833)
              ·
                refine ⟨9900617828053055086259875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200823770737406781679833 9900617828053055086259875)
                ·
                  refine ⟨14850926742079582629389813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900617828053055086259875 14850926742079582629389813)
                  ·
                    refine ⟨1392274382069960871505295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14850926742079582629389813 1392274382069960871505295)
                    ·
                      rfl

theorem cell23_8134334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_8134334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134334 prefixEnd_8134334 := by exact prefixLift 8134334
  have htrace : WordTrace (prefixWord ++ tailWord_8134334) baseStart_8134334 baseEnd_8134334 := by
    simpa [prefixWord, tailWord_8134334, baseEnd_8134334] using wordTrace_append hprefix tailTrace_8134334
  have hstable : (prefixWord ++ tailWord_8134334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134334).length < 2 ^ (prefixWord ++ tailWord_8134334).sum := by decide
  have hdescent : baseEnd_8134334 < baseStart_8134334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134354 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_8134354 : Nat := 118140960795 + 8134354 * 2 ^ 59
def prefixEnd_8134354 : Nat := 4983230072969 + 3 ^ 40 * 8134354 * 2
def baseEnd_8134354 : Nat := 4176833415822972536265793

theorem tailTrace_8134354 : CollatzResearch.WordTrace tailWord_8134354 prefixEnd_8134354 4176833415822972536265793 := by
  unfold tailWord_8134354
  simp only [CollatzResearch.WordTrace]
  refine ⟨74171065993158042476374529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197789509315088113270332077 74171065993158042476374529)
  ·
    refine ⟨55628299494868531857280897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74171065993158042476374529 55628299494868531857280897)
    ·
      refine ⟨41721224621151398892960673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55628299494868531857280897 41721224621151398892960673)
      ·
        refine ⟨31290918465863549169720505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41721224621151398892960673 31290918465863549169720505)
        ·
          refine ⟨23468188849397661877290379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31290918465863549169720505 23468188849397661877290379)
          ·
            refine ⟨35202283274096492815935569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23468188849397661877290379 35202283274096492815935569)
            ·
              refine ⟨26401712455572369611951677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35202283274096492815935569 26401712455572369611951677)
              ·
                refine ⟨9900642170839638604481879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26401712455572369611951677 9900642170839638604481879)
                ·
                  refine ⟨14850963256259457906722819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900642170839638604481879 14850963256259457906722819)
                  ·
                    refine ⟨22276444884389186860084229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14850963256259457906722819 22276444884389186860084229)
                    ·
                      refine ⟨4176833415822972536265793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22276444884389186860084229 4176833415822972536265793)
                      ·
                        rfl

theorem cell23_8134354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_8134354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134354 prefixEnd_8134354 := by exact prefixLift 8134354
  have htrace : WordTrace (prefixWord ++ tailWord_8134354) baseStart_8134354 baseEnd_8134354 := by
    simpa [prefixWord, tailWord_8134354, baseEnd_8134354] using wordTrace_append hprefix tailTrace_8134354
  have hstable : (prefixWord ++ tailWord_8134354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134354).length < 2 ^ (prefixWord ++ tailWord_8134354).sum := by decide
  have hdescent : baseEnd_8134354 < baseStart_8134354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134365 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_8134365 : Nat := 118140960795 + 8134365 * 2 ^ 59
def prefixEnd_8134365 : Nat := 4983230072969 + 3 ^ 40 * 8134365 * 2
def baseEnd_8134365 : Nat := 4176839064110171993228243

theorem tailTrace_8134365 : CollatzResearch.WordTrace tailWord_8134365 prefixEnd_8134365 4176839064110171993228243 := by
  unfold tailWord_8134365
  simp only [CollatzResearch.WordTrace]
  refine ⟨296684665175592318784148549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197789776783728212522765699 296684665175592318784148549)
  ·
    refine ⟨55628374720423559772027853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296684665175592318784148549 55628374720423559772027853)
    ·
      refine ⟨20860640520158834914510445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55628374720423559772027853 20860640520158834914510445)
      ·
        refine ⟨7822740195059563092941417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20860640520158834914510445 7822740195059563092941417)
        ·
          refine ⟨5867055146294672319706063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7822740195059563092941417 5867055146294672319706063)
          ·
            refine ⟨8800582719442008479559095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867055146294672319706063 8800582719442008479559095)
            ·
              refine ⟨13200874079163012719338643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800582719442008479559095 13200874079163012719338643)
              ·
                refine ⟨19801311118744519079007965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13200874079163012719338643 19801311118744519079007965)
                ·
                  refine ⟨7425491669529194654627987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19801311118744519079007965 7425491669529194654627987)
                  ·
                    refine ⟨11138237504293791981941981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425491669529194654627987 11138237504293791981941981)
                    ·
                      refine ⟨4176839064110171993228243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138237504293791981941981 4176839064110171993228243)
                      ·
                        rfl

theorem cell23_8134365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_8134365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134365 prefixEnd_8134365 := by exact prefixLift 8134365
  have htrace : WordTrace (prefixWord ++ tailWord_8134365) baseStart_8134365 baseEnd_8134365 := by
    simpa [prefixWord, tailWord_8134365, baseEnd_8134365] using wordTrace_append hprefix tailTrace_8134365
  have hstable : (prefixWord ++ tailWord_8134365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134365).length < 2 ^ (prefixWord ++ tailWord_8134365).sum := by decide
  have hdescent : baseEnd_8134365 < baseStart_8134365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134381 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_8134381 : Nat := 118140960795 + 8134381 * 2 ^ 59
def prefixEnd_8134381 : Nat := 4983230072969 + 3 ^ 40 * 8134381 * 2
def baseEnd_8134381 : Nat := 1392282426600214643542723

theorem tailTrace_8134381 : CollatzResearch.WordTrace tailWord_8134381 prefixEnd_8134381 1392282426600214643542723 := by
  unfold tailWord_8134381
  simp only [CollatzResearch.WordTrace]
  refine ⟨296685248743534353516730997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197790165829022902344487331 296685248743534353516730997)
  ·
    refine ⟨27814242069706345642193531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296685248743534353516730997 27814242069706345642193531)
    ·
      refine ⟨41721363104559518463290297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27814242069706345642193531 41721363104559518463290297)
      ·
        refine ⟨31291022328419638847467723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41721363104559518463290297 31291022328419638847467723)
        ·
          refine ⟨46936533492629458271201585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31291022328419638847467723 46936533492629458271201585)
          ·
            refine ⟨35202400119472093703401189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46936533492629458271201585 35202400119472093703401189)
            ·
              refine ⟨6600450022401017569387723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35202400119472093703401189 6600450022401017569387723)
              ·
                refine ⟨9900675033601526354081585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600450022401017569387723 9900675033601526354081585)
                ·
                  refine ⟨7425506275201144765561189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9900675033601526354081585 7425506275201144765561189)
                  ·
                    refine ⟨1392282426600214643542723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425506275201144765561189 1392282426600214643542723)
                    ·
                      rfl

theorem cell23_8134381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_8134381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134381 prefixEnd_8134381 := by exact prefixLift 8134381
  have htrace : WordTrace (prefixWord ++ tailWord_8134381) baseStart_8134381 baseEnd_8134381 := by
    simpa [prefixWord, tailWord_8134381, baseEnd_8134381] using wordTrace_append hprefix tailTrace_8134381
  have hstable : (prefixWord ++ tailWord_8134381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134381).length < 2 ^ (prefixWord ++ tailWord_8134381).sum := by decide
  have hdescent : baseEnd_8134381 < baseStart_8134381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134388 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_8134388 : Nat := 118140960795 + 8134388 * 2 ^ 59
def prefixEnd_8134388 : Nat := 4983230072969 + 3 ^ 40 * 8134388 * 2
def baseEnd_8134388 : Nat := 4176850874165225403240637

theorem tailTrace_8134388 : CollatzResearch.WordTrace tailWord_8134388 prefixEnd_8134388 4176850874165225403240637 := by
  unfold tailWord_8134388
  simp only [CollatzResearch.WordTrace]
  refine ⟨148342752027254496856117909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197790336036339329141490545 148342752027254496856117909)
  ·
    refine ⟨6953566501277554540130527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148342752027254496856117909 6953566501277554540130527)
    ·
      refine ⟨10430349751916331810195791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953566501277554540130527 10430349751916331810195791)
      ·
        refine ⟨15645524627874497715293687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430349751916331810195791 15645524627874497715293687)
        ·
          refine ⟨23468286941811746572940531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15645524627874497715293687 23468286941811746572940531)
          ·
            refine ⟨35202430412717619859410797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23468286941811746572940531 35202430412717619859410797)
            ·
              refine ⟨13200911404769107447279049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35202430412717619859410797 13200911404769107447279049)
              ·
                refine ⟨9900683553576830585459287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200911404769107447279049 9900683553576830585459287)
                ·
                  refine ⟨14851025330365245878188931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900683553576830585459287 14851025330365245878188931)
                  ·
                    refine ⟨22276537995547868817283397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14851025330365245878188931 22276537995547868817283397)
                    ·
                      refine ⟨4176850874165225403240637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22276537995547868817283397 4176850874165225403240637)
                      ·
                        rfl

theorem cell23_8134388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_8134388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134388 prefixEnd_8134388 := by exact prefixLift 8134388
  have htrace : WordTrace (prefixWord ++ tailWord_8134388) baseStart_8134388 baseEnd_8134388 := by
    simpa [prefixWord, tailWord_8134388, baseEnd_8134388] using wordTrace_append hprefix tailTrace_8134388
  have hstable : (prefixWord ++ tailWord_8134388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134388).length < 2 ^ (prefixWord ++ tailWord_8134388).sum := by decide
  have hdescent : baseEnd_8134388 < baseStart_8134388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134404 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_8134404 : Nat := 118140960795 + 8134404 * 2 ^ 59
def prefixEnd_8134404 : Nat := 4983230072969 + 3 ^ 40 * 8134404 * 2
def baseEnd_8134404 : Nat := 4176859089855697340640563

theorem tailTrace_8134404 : CollatzResearch.WordTrace tailWord_8134404 prefixEnd_8134404 4176859089855697340640563 := by
  unfold tailWord_8134404
  simp only [CollatzResearch.WordTrace]
  refine ⟨148343043811225514222409133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197790725081634018963212177 148343043811225514222409133)
  ·
    refine ⟨55628641429209567833403425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148343043811225514222409133 55628641429209567833403425)
    ·
      refine ⟨41721481071907175875052569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55628641429209567833403425 41721481071907175875052569)
      ·
        refine ⟨31291110803930381906289427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41721481071907175875052569 31291110803930381906289427)
        ·
          refine ⟨46936666205895572859434141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31291110803930381906289427 46936666205895572859434141)
          ·
            refine ⟨17601249827210839822287803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46936666205895572859434141 17601249827210839822287803)
            ·
              refine ⟨26401874740816259733431705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17601249827210839822287803 26401874740816259733431705)
              ·
                refine ⟨19801406055612194800073779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26401874740816259733431705 19801406055612194800073779)
                ·
                  refine ⟨29702109083418292200110669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19801406055612194800073779 29702109083418292200110669)
                  ·
                    refine ⟨11138290906281859575041501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29702109083418292200110669 11138290906281859575041501)
                    ·
                      refine ⟨4176859089855697340640563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138290906281859575041501 4176859089855697340640563)
                      ·
                        rfl

theorem cell23_8134404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_8134404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134404 prefixEnd_8134404 := by exact prefixLift 8134404
  have htrace : WordTrace (prefixWord ++ tailWord_8134404) baseStart_8134404 baseEnd_8134404 := by
    simpa [prefixWord, tailWord_8134404, baseEnd_8134404] using wordTrace_append hprefix tailTrace_8134404
  have hstable : (prefixWord ++ tailWord_8134404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134404).length < 2 ^ (prefixWord ++ tailWord_8134404).sum := by decide
  have hdescent : baseEnd_8134404 < baseStart_8134404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134421 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_8134421 : Nat := 118140960795 + 8134421 * 2 ^ 59
def prefixEnd_8134421 : Nat := 4983230072969 + 3 ^ 40 * 8134421 * 2
def baseEnd_8134421 : Nat := 4176867819026823774127985

theorem tailTrace_8134421 : CollatzResearch.WordTrace tailWord_8134421 prefixEnd_8134421 4176867819026823774127985 := by
  unfold tailWord_8134421
  simp only [CollatzResearch.WordTrace]
  refine ⟨296686707663389440348187117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197791138442259626898791411 296686707663389440348187117)
  ·
    refine ⟨111257515373771040130570169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296686707663389440348187117 111257515373771040130570169)
    ·
      refine ⟨83443136530328280097927627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111257515373771040130570169 83443136530328280097927627)
      ·
        refine ⟨125164704795492420146891441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83443136530328280097927627 125164704795492420146891441)
        ·
          refine ⟨93873528596619315110168581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125164704795492420146891441 93873528596619315110168581)
          ·
            refine ⟨17601286611866121583156609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93873528596619315110168581 17601286611866121583156609)
            ·
              refine ⟨13200964958899591187367457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17601286611866121583156609 13200964958899591187367457)
              ·
                refine ⟨9900723719174693390525593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200964958899591187367457 9900723719174693390525593)
                ·
                  refine ⟨7425542789381020042894195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9900723719174693390525593 7425542789381020042894195)
                  ·
                    refine ⟨11138314184071530064341293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425542789381020042894195 11138314184071530064341293)
                    ·
                      refine ⟨4176867819026823774127985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138314184071530064341293 4176867819026823774127985)
                      ·
                        rfl

theorem cell23_8134421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_8134421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134421 prefixEnd_8134421 := by exact prefixLift 8134421
  have htrace : WordTrace (prefixWord ++ tailWord_8134421) baseStart_8134421 baseEnd_8134421 := by
    simpa [prefixWord, tailWord_8134421, baseEnd_8134421] using wordTrace_append hprefix tailTrace_8134421
  have hstable : (prefixWord ++ tailWord_8134421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134421).length < 2 ^ (prefixWord ++ tailWord_8134421).sum := by decide
  have hdescent : baseEnd_8134421 < baseStart_8134421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134437 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_8134437 : Nat := 118140960795 + 8134437 * 2 ^ 59
def prefixEnd_8134437 : Nat := 4983230072969 + 3 ^ 40 * 8134437 * 2
def baseEnd_8134437 : Nat := 1392292011572431903842637

theorem tailTrace_8134437 : CollatzResearch.WordTrace tailWord_8134437 prefixEnd_8134437 1392292011572431903842637 := by
  unfold tailWord_8134437
  simp only [CollatzResearch.WordTrace]
  refine ⟨296687291231331475080769565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197791527487554316720513043 296687291231331475080769565)
  ·
    refine ⟨111257734211749303155288587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296687291231331475080769565 111257734211749303155288587)
    ·
      refine ⟨166886601317623954732932881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111257734211749303155288587 166886601317623954732932881)
      ·
        refine ⟨125164950988217966049699661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166886601317623954732932881 125164950988217966049699661)
        ·
          refine ⟨46936856620581737268637373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125164950988217966049699661 46936856620581737268637373)
          ·
            refine ⟨17601321232718151475739015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46936856620581737268637373 17601321232718151475739015)
            ·
              refine ⟨26401981849077227213608523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17601321232718151475739015 26401981849077227213608523)
              ·
                refine ⟨39602972773615840820412785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26401981849077227213608523 39602972773615840820412785)
                ·
                  refine ⟨29702229580211880615309589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39602972773615840820412785 29702229580211880615309589)
                  ·
                    refine ⟨1392292011572431903842637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29702229580211880615309589 1392292011572431903842637)
                    ·
                      rfl

theorem cell23_8134437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_8134437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134437 prefixEnd_8134437 := by exact prefixLift 8134437
  have htrace : WordTrace (prefixWord ++ tailWord_8134437) baseStart_8134437 baseEnd_8134437 := by
    simpa [prefixWord, tailWord_8134437, baseEnd_8134437] using wordTrace_append hprefix tailTrace_8134437
  have hstable : (prefixWord ++ tailWord_8134437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134437).length < 2 ^ (prefixWord ++ tailWord_8134437).sum := by decide
  have hdescent : baseEnd_8134437 < baseStart_8134437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134444 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 1, 4, 2]
def baseStart_8134444 : Nat := 118140960795 + 8134444 * 2 ^ 59
def prefixEnd_8134444 : Nat := 4983230072969 + 3 ^ 40 * 8134444 * 2
def baseEnd_8134444 : Nat := 4176879629081877184140379

theorem tailTrace_8134444 : CollatzResearch.WordTrace tailWord_8134444 prefixEnd_8134444 4176879629081877184140379 := by
  unfold tailWord_8134444
  simp only [CollatzResearch.WordTrace]
  refine ⟨148343773271153057638137193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197791697694870743517516257 148343773271153057638137193)
  ·
    refine ⟨111257829953364793228602895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148343773271153057638137193 111257829953364793228602895)
    ·
      refine ⟨166886744930047189842904343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111257829953364793228602895 166886744930047189842904343)
      ·
        refine ⟨250330117395070784764356515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166886744930047189842904343 250330117395070784764356515)
        ·
          refine ⟨375495176092606177146534773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250330117395070784764356515 375495176092606177146534773)
          ·
            refine ⟨35202672758681829107487635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375495176092606177146534773 35202672758681829107487635)
            ·
              refine ⟨52804009138022743661231453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35202672758681829107487635 52804009138022743661231453)
              ·
                refine ⟨19801503426758528872961795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52804009138022743661231453 19801503426758528872961795)
                ·
                  refine ⟨29702255140137793309442693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19801503426758528872961795 29702255140137793309442693)
                  ·
                    refine ⟨5569172838775836245520505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29702255140137793309442693 5569172838775836245520505)
                    ·
                      refine ⟨4176879629081877184140379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569172838775836245520505 4176879629081877184140379)
                      ·
                        rfl

theorem cell23_8134444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_8134444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134444 prefixEnd_8134444 := by exact prefixLift 8134444
  have htrace : WordTrace (prefixWord ++ tailWord_8134444) baseStart_8134444 baseEnd_8134444 := by
    simpa [prefixWord, tailWord_8134444, baseEnd_8134444] using wordTrace_append hprefix tailTrace_8134444
  have hstable : (prefixWord ++ tailWord_8134444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134444).length < 2 ^ (prefixWord ++ tailWord_8134444).sum := by decide
  have hdescent : baseEnd_8134444 < baseStart_8134444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134461 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_8134461 : Nat := 118140960795 + 8134461 * 2 ^ 59
def prefixEnd_8134461 : Nat := 4983230072969 + 3 ^ 40 * 8134461 * 2
def baseEnd_8134461 : Nat := 4176888358253003617627801

theorem tailTrace_8134461 : CollatzResearch.WordTrace tailWord_8134461 prefixEnd_8134461 4176888358253003617627801 := by
  unfold tailWord_8134461
  simp only [CollatzResearch.WordTrace]
  refine ⟨296688166583244527179643237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197792111055496351453095491 296688166583244527179643237)
  ·
    refine ⟨55629031234358348846183107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296688166583244527179643237 55629031234358348846183107)
    ·
      refine ⟨83443546851537523269274661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55629031234358348846183107 83443546851537523269274661)
      ·
        refine ⟨15645665034663285612988999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83443546851537523269274661 15645665034663285612988999)
        ·
          refine ⟨23468497551994928419483499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15645665034663285612988999 23468497551994928419483499)
          ·
            refine ⟨35202746327992392629225249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23468497551994928419483499 35202746327992392629225249)
            ·
              refine ⟨26402059745994294471918937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35202746327992392629225249 26402059745994294471918937)
              ·
                refine ⟨19801544809495720853939203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26402059745994294471918937 19801544809495720853939203)
                ·
                  refine ⟨29702317214243581280908805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19801544809495720853939203 29702317214243581280908805)
                  ·
                    refine ⟨5569184477670671490170401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29702317214243581280908805 5569184477670671490170401)
                    ·
                      refine ⟨4176888358253003617627801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569184477670671490170401 4176888358253003617627801)
                      ·
                        rfl

theorem cell23_8134461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_8134461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134461 prefixEnd_8134461 := by exact prefixLift 8134461
  have htrace : WordTrace (prefixWord ++ tailWord_8134461) baseStart_8134461 baseEnd_8134461 := by
    simpa [prefixWord, tailWord_8134461, baseEnd_8134461] using wordTrace_append hprefix tailTrace_8134461
  have hstable : (prefixWord ++ tailWord_8134461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134461).length < 2 ^ (prefixWord ++ tailWord_8134461).sum := by decide
  have hdescent : baseEnd_8134461 < baseStart_8134461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134484 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 7]
def baseStart_8134484 : Nat := 118140960795 + 8134484 * 2 ^ 59
def prefixEnd_8134484 : Nat := 4983230072969 + 3 ^ 40 * 8134484 * 2
def baseEnd_8134484 : Nat := 464100018700895225293355

theorem tailTrace_8134484 : CollatzResearch.WordTrace tailWord_8134484 prefixEnd_8134484 464100018700895225293355 := by
  unfold tailWord_8134484
  simp only [CollatzResearch.WordTrace]
  refine ⟨148344502731080601053865253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197792670308107468071820337 148344502731080601053865253)
  ·
    refine ⟨27814594262077612697599735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148344502731080601053865253 27814594262077612697599735)
    ·
      refine ⟨41721891393116419046399603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27814594262077612697599735 41721891393116419046399603)
      ·
        refine ⟨62582837089674628569599405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41721891393116419046399603 62582837089674628569599405)
        ·
          refine ⟨23468563908627985713599777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62582837089674628569599405 23468563908627985713599777)
          ·
            refine ⟨17601422931470989285199833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23468563908627985713599777 17601422931470989285199833)
            ·
              refine ⟨13201067198603241963899875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17601422931470989285199833 13201067198603241963899875)
              ·
                refine ⟨19801600797904862945849813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13201067198603241963899875 19801600797904862945849813)
                ·
                  refine ⟨464100018700895225293355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19801600797904862945849813 464100018700895225293355)
                  ·
                    rfl

theorem cell23_8134484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_8134484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134484 prefixEnd_8134484 := by exact prefixLift 8134484
  have htrace : WordTrace (prefixWord ++ tailWord_8134484) baseStart_8134484 baseEnd_8134484 := by
    simpa [prefixWord, tailWord_8134484, baseEnd_8134484] using wordTrace_append hprefix tailTrace_8134484
  have hstable : (prefixWord ++ tailWord_8134484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134484).length < 2 ^ (prefixWord ++ tailWord_8134484).sum := by decide
  have hdescent : baseEnd_8134484 < baseStart_8134484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134587 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 5, 5]
def baseStart_8134587 : Nat := 118140960795 + 8134587 * 2 ^ 59
def prefixEnd_8134587 : Nat := 4983230072969 + 3 ^ 40 * 8134587 * 2
def baseEnd_8134587 : Nat := 1392317685605156708217407

theorem tailTrace_8134587 : CollatzResearch.WordTrace tailWord_8134587 prefixEnd_8134587 1392317685605156708217407 := by
  unfold tailWord_8134587
  simp only [CollatzResearch.WordTrace]
  refine ⟨296692762180788050698730015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197795174787192033799153343 296692762180788050698730015)
  ·
    refine ⟨445039143271182076048095023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296692762180788050698730015 445039143271182076048095023)
    ·
      refine ⟨667558714906773114072142535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445039143271182076048095023 667558714906773114072142535)
      ·
        refine ⟨1001338072360159671108213803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667558714906773114072142535 1001338072360159671108213803)
        ·
          refine ⟨1502007108540239506662320705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001338072360159671108213803 1502007108540239506662320705)
          ·
            refine ⟨1126505331405179629996740529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502007108540239506662320705 1126505331405179629996740529)
            ·
              refine ⟨844878998553884722497555397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126505331405179629996740529 844878998553884722497555397)
              ·
                refine ⟨158414812228853385468291637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844878998553884722497555397 158414812228853385468291637)
                ·
                  refine ⟨14851388646455004887652341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158414812228853385468291637 14851388646455004887652341)
                  ·
                    refine ⟨1392317685605156708217407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14851388646455004887652341 1392317685605156708217407)
                    ·
                      rfl

theorem cell23_8134587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 5].length) (baseStart_8134587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134587 prefixEnd_8134587 := by exact prefixLift 8134587
  have htrace : WordTrace (prefixWord ++ tailWord_8134587) baseStart_8134587 baseEnd_8134587 := by
    simpa [prefixWord, tailWord_8134587, baseEnd_8134587] using wordTrace_append hprefix tailTrace_8134587
  have hstable : (prefixWord ++ tailWord_8134587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134587).length < 2 ^ (prefixWord ++ tailWord_8134587).sum := by decide
  have hdescent : baseEnd_8134587 < baseStart_8134587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134604 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_8134604 : Nat := 118140960795 + 8134604 * 2 ^ 59
def prefixEnd_8134604 : Nat := 4983230072969 + 3 ^ 40 * 8134604 * 2
def baseEnd_8134604 : Nat := 1392320595328865519379881

theorem tailTrace_8134604 : CollatzResearch.WordTrace tailWord_8134604 prefixEnd_8134604 1392320595328865519379881 := by
  unfold tailWord_8134604
  simp only [CollatzResearch.WordTrace]
  refine ⟨148346691110863231301049433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197795588147817641734732577 148346691110863231301049433)
  ·
    refine ⟨111260018333147423475787075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148346691110863231301049433 111260018333147423475787075)
    ·
      refine ⟨166890027499721135213680613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111260018333147423475787075 166890027499721135213680613)
      ·
        refine ⟨31291880156197712852565115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166890027499721135213680613 31291880156197712852565115)
        ·
          refine ⟨46937820234296569278847673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31291880156197712852565115 46937820234296569278847673)
          ·
            refine ⟨35203365175722426959135755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46937820234296569278847673 35203365175722426959135755)
            ·
              refine ⟨52805047763583640438703633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35203365175722426959135755 52805047763583640438703633)
              ·
                refine ⟨39603785822687730329027725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52805047763583640438703633 39603785822687730329027725)
                ·
                  refine ⟨14851419683507898873385397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39603785822687730329027725 14851419683507898873385397)
                  ·
                    refine ⟨1392320595328865519379881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14851419683507898873385397 1392320595328865519379881)
                    ·
                      rfl

theorem cell23_8134604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_8134604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134604 prefixEnd_8134604 := by exact prefixLift 8134604
  have htrace : WordTrace (prefixWord ++ tailWord_8134604) baseStart_8134604 baseEnd_8134604 := by
    simpa [prefixWord, tailWord_8134604, baseEnd_8134604] using wordTrace_append hprefix tailTrace_8134604
  have hstable : (prefixWord ++ tailWord_8134604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134604).length < 2 ^ (prefixWord ++ tailWord_8134604).sum := by decide
  have hdescent : baseEnd_8134604 < baseStart_8134604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134618 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_8134618 : Nat := 118140960795 + 8134618 * 2 ^ 59
def prefixEnd_8134618 : Nat := 4983230072969 + 3 ^ 40 * 8134618 * 2
def baseEnd_8134618 : Nat := 4176968974715759503364579

theorem tailTrace_8134618 : CollatzResearch.WordTrace tailWord_8134618 prefixEnd_8134618 4176968974715759503364579 := by
  unfold tailWord_8134618
  simp only [CollatzResearch.WordTrace]
  refine ⟨74173473210918935748277127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197795928562450495328739005 74173473210918935748277127)
  ·
    refine ⟨111260209816378403622415691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74173473210918935748277127 111260209816378403622415691)
    ·
      refine ⟨166890314724567605433623537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111260209816378403622415691 166890314724567605433623537)
      ·
        refine ⟨125167736043425704075217653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166890314724567605433623537 125167736043425704075217653)
        ·
          refine ⟨11734475254071159757051655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125167736043425704075217653 11734475254071159757051655)
          ·
            refine ⟨17601712881106739635577483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11734475254071159757051655 17601712881106739635577483)
            ·
              refine ⟨26402569321660109453366225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17601712881106739635577483 26402569321660109453366225)
              ·
                refine ⟨19801926991245082090024669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26402569321660109453366225 19801926991245082090024669)
                ·
                  refine ⟨7425722621716905783759251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19801926991245082090024669 7425722621716905783759251)
                  ·
                    refine ⟨11138583932575358675638877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425722621716905783759251 11138583932575358675638877)
                    ·
                      refine ⟨4176968974715759503364579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138583932575358675638877 4176968974715759503364579)
                      ·
                        rfl

theorem cell23_8134618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_8134618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134618 prefixEnd_8134618 := by exact prefixLift 8134618
  have htrace : WordTrace (prefixWord ++ tailWord_8134618) baseStart_8134618 baseEnd_8134618 := by
    simpa [prefixWord, tailWord_8134618, baseEnd_8134618] using wordTrace_append hprefix tailTrace_8134618
  have hstable : (prefixWord ++ tailWord_8134618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134618).length < 2 ^ (prefixWord ++ tailWord_8134618).sum := by decide
  have hdescent : baseEnd_8134618 < baseStart_8134618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134634 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_8134634 : Nat := 118140960795 + 8134634 * 2 ^ 59
def prefixEnd_8134634 : Nat := 4983230072969 + 3 ^ 40 * 8134634 * 2
def baseEnd_8134634 : Nat := 1392325730135410480254835

theorem tailTrace_8134634 : CollatzResearch.WordTrace tailWord_8134634 prefixEnd_8134634 1392325730135410480254835 := by
  unfold tailWord_8134634
  simp only [CollatzResearch.WordTrace]
  refine ⟨74173619102904444431422739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197796317607745185150460637 74173619102904444431422739)
  ·
    refine ⟨111260428654356666647134109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74173619102904444431422739 111260428654356666647134109)
    ·
      refine ⟨41722660745383749992675291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111260428654356666647134109 41722660745383749992675291)
      ·
        refine ⟨62583991118075624989012937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41722660745383749992675291 62583991118075624989012937)
        ·
          refine ⟨46937993338556718741759703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62583991118075624989012937 46937993338556718741759703)
          ·
            refine ⟨70406990007835078112639555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46937993338556718741759703 70406990007835078112639555)
            ·
              refine ⟨105610485011752617168959333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70406990007835078112639555 105610485011752617168959333)
              ·
                refine ⟨19801965939703615719179875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105610485011752617168959333 19801965939703615719179875)
                ·
                  refine ⟨29702948909555423578769813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19801965939703615719179875 29702948909555423578769813)
                  ·
                    refine ⟨1392325730135410480254835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29702948909555423578769813 1392325730135410480254835)
                    ·
                      rfl

theorem cell23_8134634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_8134634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134634 prefixEnd_8134634 := by exact prefixLift 8134634
  have htrace : WordTrace (prefixWord ++ tailWord_8134634) baseStart_8134634 baseEnd_8134634 := by
    simpa [prefixWord, tailWord_8134634, baseEnd_8134634] using wordTrace_append hprefix tailTrace_8134634
  have hstable : (prefixWord ++ tailWord_8134634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134634).length < 2 ^ (prefixWord ++ tailWord_8134634).sum := by decide
  have hdescent : baseEnd_8134634 < baseStart_8134634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134638 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_8134638 : Nat := 118140960795 + 8134638 * 2 ^ 59
def prefixEnd_8134638 : Nat := 4983230072969 + 3 ^ 40 * 8134638 * 2
def baseEnd_8134638 : Nat := 1392326414776283141704829

theorem tailTrace_8134638 : CollatzResearch.WordTrace tailWord_8134638 prefixEnd_8134638 1392326414776283141704829 := by
  unfold tailWord_8134638
  simp only [CollatzResearch.WordTrace]
  refine ⟨37086827787950410801104571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197796414869068857605891045 37086827787950410801104571)
  ·
    refine ⟨55630241681925616201656857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37086827787950410801104571 55630241681925616201656857)
    ·
      refine ⟨41722681261444212151242643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55630241681925616201656857 41722681261444212151242643)
      ·
        refine ⟨62584021892166318226863965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41722681261444212151242643 62584021892166318226863965)
        ·
          refine ⟨23469008209562369335073987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62584021892166318226863965 23469008209562369335073987)
          ·
            refine ⟨35203512314343554002610981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23469008209562369335073987 35203512314343554002610981)
            ·
              refine ⟨6600658558939416375489559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35203512314343554002610981 6600658558939416375489559)
              ·
                refine ⟨9900987838409124563234339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600658558939416375489559 9900987838409124563234339)
                ·
                  refine ⟨14851481757613686844851509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900987838409124563234339 14851481757613686844851509)
                  ·
                    refine ⟨1392326414776283141704829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14851481757613686844851509 1392326414776283141704829)
                    ·
                      rfl

theorem cell23_8134638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_8134638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134638 prefixEnd_8134638 := by exact prefixLift 8134638
  have htrace : WordTrace (prefixWord ++ tailWord_8134638) baseStart_8134638 baseEnd_8134638 := by
    simpa [prefixWord, tailWord_8134638, baseEnd_8134638] using wordTrace_append hprefix tailTrace_8134638
  have hstable : (prefixWord ++ tailWord_8134638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134638).length < 2 ^ (prefixWord ++ tailWord_8134638).sum := by decide
  have hdescent : baseEnd_8134638 < baseStart_8134638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134651 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 2, 4]
def baseStart_8134651 : Nat := 118140960795 + 8134651 * 2 ^ 59
def prefixEnd_8134651 : Nat := 4983230072969 + 3 ^ 40 * 8134651 * 2
def baseEnd_8134651 : Nat := 1392328639859119291417309

theorem tailTrace_8134651 : CollatzResearch.WordTrace tailWord_8134651 prefixEnd_8134651 1392328639859119291417309 := by
  unfold tailWord_8134651
  simp only [CollatzResearch.WordTrace]
  refine ⟨296695096452556189629059807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197796730968370793086039871 296695096452556189629059807)
  ·
    refine ⟨445042644678834284443589711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296695096452556189629059807 445042644678834284443589711)
    ·
      refine ⟨667563967018251426665384567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445042644678834284443589711 667563967018251426665384567)
      ·
        refine ⟨1001345950527377139998076851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667563967018251426665384567 1001345950527377139998076851)
        ·
          refine ⟨1502018925791065709997115277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001345950527377139998076851 1502018925791065709997115277)
          ·
            refine ⟨563257097171649641248918229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1502018925791065709997115277 563257097171649641248918229)
            ·
              refine ⟨13201338214960538466771521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 563257097171649641248918229 13201338214960538466771521)
              ·
                refine ⟨9901003661220403850078641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13201338214960538466771521 9901003661220403850078641)
                ·
                  refine ⟨7425752745915302887558981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901003661220403850078641 7425752745915302887558981)
                  ·
                    refine ⟨1392328639859119291417309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425752745915302887558981 1392328639859119291417309)
                    ·
                      rfl

theorem cell23_8134651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 4].length) (baseStart_8134651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134651 prefixEnd_8134651 := by exact prefixLift 8134651
  have htrace : WordTrace (prefixWord ++ tailWord_8134651) baseStart_8134651 baseEnd_8134651 := by
    simpa [prefixWord, tailWord_8134651, baseEnd_8134651] using wordTrace_append hprefix tailTrace_8134651
  have hstable : (prefixWord ++ tailWord_8134651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134651).length < 2 ^ (prefixWord ++ tailWord_8134651).sum := by decide
  have hdescent : baseEnd_8134651 < baseStart_8134651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134668 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_8134668 : Nat := 118140960795 + 8134668 * 2 ^ 59
def prefixEnd_8134668 : Nat := 4983230072969 + 3 ^ 40 * 8134668 * 2
def baseEnd_8134668 : Nat := 1392331549582828102579783

theorem tailTrace_8134668 : CollatzResearch.WordTrace tailWord_8134668 prefixEnd_8134668 1392331549582828102579783 := by
  unfold tailWord_8134668
  simp only [CollatzResearch.WordTrace]
  refine ⟨148347858246747300766214329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197797144328996401021619105 148347858246747300766214329)
  ·
    refine ⟨111260893685060475574660747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148347858246747300766214329 111260893685060475574660747)
    ·
      refine ⟨166891340527590713361991121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111260893685060475574660747 166891340527590713361991121)
      ·
        refine ⟨125168505395693035021493341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166891340527590713361991121 125168505395693035021493341)
        ·
          refine ⟨46938189523384888133060003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125168505395693035021493341 46938189523384888133060003)
          ·
            refine ⟨70407284285077332199590005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46938189523384888133060003 70407284285077332199590005)
            ·
              refine ⟨6600682901725999893711563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70407284285077332199590005 6600682901725999893711563)
              ·
                refine ⟨9901024352588999840567345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600682901725999893711563 9901024352588999840567345)
                ·
                  refine ⟨7425768264441749880425509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901024352588999840567345 7425768264441749880425509)
                  ·
                    refine ⟨1392331549582828102579783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425768264441749880425509 1392331549582828102579783)
                    ·
                      rfl

theorem cell23_8134668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_8134668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134668 prefixEnd_8134668 := by exact prefixLift 8134668
  have htrace : WordTrace (prefixWord ++ tailWord_8134668) baseStart_8134668 baseEnd_8134668 := by
    simpa [prefixWord, tailWord_8134668, baseEnd_8134668] using wordTrace_append hprefix tailTrace_8134668
  have hstable : (prefixWord ++ tailWord_8134668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134668).length < 2 ^ (prefixWord ++ tailWord_8134668).sum := by decide
  have hdescent : baseEnd_8134668 < baseStart_8134668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134691 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 3]
def baseStart_8134691 : Nat := 118140960795 + 8134691 * 2 ^ 59
def prefixEnd_8134691 : Nat := 4983230072969 + 3 ^ 40 * 8134691 * 2
def baseEnd_8134691 : Nat := 4177006458803537717751743

theorem tailTrace_8134691 : CollatzResearch.WordTrace tailWord_8134691 prefixEnd_8134691 4177006458803537717751743 := by
  unfold tailWord_8134691
  simp only [CollatzResearch.WordTrace]
  refine ⟨296696555372411276460515927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197797703581607517640343951 296696555372411276460515927)
  ·
    refine ⟨445044833058616914690773891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296696555372411276460515927 445044833058616914690773891)
    ·
      refine ⟨667567249587925372036160837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445044833058616914690773891 667567249587925372036160837)
      ·
        refine ⟨125168859297736007256780157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 667567249587925372036160837 125168859297736007256780157)
        ·
          refine ⟨46938322236651002721292559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125168859297736007256780157 46938322236651002721292559)
          ·
            refine ⟨70407483354976504081938839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46938322236651002721292559 70407483354976504081938839)
            ·
              refine ⟨105611225032464756122908259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70407483354976504081938839 105611225032464756122908259)
              ·
                refine ⟨158416837548697134184362389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105611225032464756122908259 158416837548697134184362389)
                ·
                  refine ⟨7425789260095178164891987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158416837548697134184362389 7425789260095178164891987)
                  ·
                    refine ⟨11138683890142767247337981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425789260095178164891987 11138683890142767247337981)
                    ·
                      refine ⟨4177006458803537717751743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138683890142767247337981 4177006458803537717751743)
                      ·
                        rfl

theorem cell23_8134691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_8134691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134691 prefixEnd_8134691 := by exact prefixLift 8134691
  have htrace : WordTrace (prefixWord ++ tailWord_8134691) baseStart_8134691 baseEnd_8134691 := by
    simpa [prefixWord, tailWord_8134691, baseEnd_8134691] using wordTrace_append hprefix tailTrace_8134691
  have hstable : (prefixWord ++ tailWord_8134691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134691).length < 2 ^ (prefixWord ++ tailWord_8134691).sum := by decide
  have hdescent : baseEnd_8134691 < baseStart_8134691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134714 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_8134714 : Nat := 118140960795 + 8134714 * 2 ^ 59
def prefixEnd_8134714 : Nat := 4983230072969 + 3 ^ 40 * 8134714 * 2
def baseEnd_8134714 : Nat := 4177018268858591127764137

theorem tailTrace_8134714 : CollatzResearch.WordTrace tailWord_8134714 prefixEnd_8134714 4177018268858591127764137 := by
  unfold tailWord_8134714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74174348562831987847150799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197798262834218634259068797 74174348562831987847150799)
  ·
    refine ⟨111261522844247981770726199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74174348562831987847150799 111261522844247981770726199)
    ·
      refine ⟨166892284266371972656089299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111261522844247981770726199 166892284266371972656089299)
      ·
        refine ⟨250338426399557958984133949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166892284266371972656089299 250338426399557958984133949)
        ·
          refine ⟨93876909899834234619050231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250338426399557958984133949 93876909899834234619050231)
          ·
            refine ⟨140815364849751351928575347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93876909899834234619050231 140815364849751351928575347)
            ·
              refine ⟨211223047274627027892863021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140815364849751351928575347 211223047274627027892863021)
              ·
                refine ⟨79208642727985135459823633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211223047274627027892863021 79208642727985135459823633)
                ·
                  refine ⟨59406482045988851594867725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79208642727985135459823633 59406482045988851594867725)
                  ·
                    refine ⟨22277430767245819348075397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59406482045988851594867725 22277430767245819348075397)
                    ·
                      refine ⟨4177018268858591127764137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22277430767245819348075397 4177018268858591127764137)
                      ·
                        rfl

theorem cell23_8134714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_8134714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134714 prefixEnd_8134714 := by exact prefixLift 8134714
  have htrace : WordTrace (prefixWord ++ tailWord_8134714) baseStart_8134714 baseEnd_8134714 := by
    simpa [prefixWord, tailWord_8134714, baseEnd_8134714] using wordTrace_append hprefix tailTrace_8134714
  have hstable : (prefixWord ++ tailWord_8134714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134714).length < 2 ^ (prefixWord ++ tailWord_8134714).sum := by decide
  have hdescent : baseEnd_8134714 < baseStart_8134714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134748 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_8134748 : Nat := 118140960795 + 8134748 * 2 ^ 59
def prefixEnd_8134748 : Nat := 4983230072969 + 3 ^ 40 * 8134748 * 2
def baseEnd_8134748 : Nat := 4177035727200843994738981

theorem tailTrace_8134748 : CollatzResearch.WordTrace tailWord_8134748 prefixEnd_8134748 4177035727200843994738981 := by
  unfold tailWord_8134748
  simp only [CollatzResearch.WordTrace]
  refine ⟨148349317166602387597670449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197799089555469850130227265 148349317166602387597670449)
  ·
    refine ⟨111261987874951790698252837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148349317166602387597670449 111261987874951790698252837)
    ·
      refine ⟨20861622726553460755922407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111261987874951790698252837 20861622726553460755922407)
      ·
        refine ⟨31292434089830191133883611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20861622726553460755922407 31292434089830191133883611)
        ·
          refine ⟨46938651134745286700825417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31292434089830191133883611 46938651134745286700825417)
          ·
            refine ⟨35203988351058965025619063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46938651134745286700825417 35203988351058965025619063)
            ·
              refine ⟨52805982526588447538428595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35203988351058965025619063 52805982526588447538428595)
              ·
                refine ⟨79208973789882671307642893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52805982526588447538428595 79208973789882671307642893)
                ·
                  refine ⟨29703365171206001740366085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79208973789882671307642893 29703365171206001740366085)
                  ·
                    refine ⟨5569380969601125326318641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29703365171206001740366085 5569380969601125326318641)
                    ·
                      refine ⟨4177035727200843994738981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569380969601125326318641 4177035727200843994738981)
                      ·
                        rfl

theorem cell23_8134748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_8134748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134748 prefixEnd_8134748 := by exact prefixLift 8134748
  have htrace : WordTrace (prefixWord ++ tailWord_8134748) baseStart_8134748 baseEnd_8134748 := by
    simpa [prefixWord, tailWord_8134748, baseEnd_8134748] using wordTrace_append hprefix tailTrace_8134748
  have hstable : (prefixWord ++ tailWord_8134748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134748).length < 2 ^ (prefixWord ++ tailWord_8134748).sum := by decide
  have hdescent : baseEnd_8134748 < baseStart_8134748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134781 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_8134781 : Nat := 118140960795 + 8134781 * 2 ^ 59
def prefixEnd_8134781 : Nat := 4983230072969 + 3 ^ 40 * 8134781 * 2
def baseEnd_8134781 : Nat := 4177052672062442365626329

theorem tailTrace_8134781 : CollatzResearch.WordTrace tailWord_8134781 prefixEnd_8134781 4177052672062442365626329 := by
  unfold tailWord_8134781
  simp only [CollatzResearch.WordTrace]
  refine ⟨296699837942085221831292197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197799891961390147887528131 296699837942085221831292197)
  ·
    refine ⟨55631219614140979093367287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296699837942085221831292197 55631219614140979093367287)
    ·
      refine ⟨83446829421211468640050931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55631219614140979093367287 83446829421211468640050931)
      ·
        refine ⟨125170244131817202960076397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83446829421211468640050931 125170244131817202960076397)
        ·
          refine ⟨46938841549431451110028649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125170244131817202960076397 46938841549431451110028649)
          ·
            refine ⟨35204131162073588332521487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46938841549431451110028649 35204131162073588332521487)
            ·
              refine ⟨52806196743110382498782231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35204131162073588332521487 52806196743110382498782231)
              ·
                refine ⟨79209295114665573748173347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52806196743110382498782231 79209295114665573748173347)
                ·
                  refine ⟨118813942671998360622260021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79209295114665573748173347 118813942671998360622260021)
                  ·
                    refine ⟨11138807125499846308336877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118813942671998360622260021 11138807125499846308336877)
                    ·
                      refine ⟨4177052672062442365626329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138807125499846308336877 4177052672062442365626329)
                      ·
                        rfl

theorem cell23_8134781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_8134781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134781 prefixEnd_8134781 := by exact prefixLift 8134781
  have htrace : WordTrace (prefixWord ++ tailWord_8134781) baseStart_8134781 baseEnd_8134781 := by
    simpa [prefixWord, tailWord_8134781, baseEnd_8134781] using wordTrace_append hprefix tailTrace_8134781
  have hstable : (prefixWord ++ tailWord_8134781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134781).length < 2 ^ (prefixWord ++ tailWord_8134781).sum := by decide
  have hdescent : baseEnd_8134781 < baseStart_8134781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134784 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_8134784 : Nat := 118140960795 + 8134784 * 2 ^ 59
def prefixEnd_8134784 : Nat := 4983230072969 + 3 ^ 40 * 8134784 * 2
def baseEnd_8134784 : Nat := 1392351404168135284629605

theorem tailTrace_8134784 : CollatzResearch.WordTrace tailWord_8134784 prefixEnd_8134784 1392351404168135284629605 := by
  unfold tailWord_8134784
  simp only [CollatzResearch.WordTrace]
  refine ⟨148349973680537176671825703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197799964907382902229100937 148349973680537176671825703)
  ·
    refine ⟨222524960520805765007738555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148349973680537176671825703 222524960520805765007738555)
    ·
      refine ⟨333787440781208647511607833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222524960520805765007738555 333787440781208647511607833)
      ·
        refine ⟨250340580585906485633705875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333787440781208647511607833 250340580585906485633705875)
        ·
          refine ⟨375510870878859728450558813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250340580585906485633705875 375510870878859728450558813)
          ·
            refine ⟨140816576579572398168959555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375510870878859728450558813 140816576579572398168959555)
            ·
              refine ⟨211224864869358597253439333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140816576579572398168959555 211224864869358597253439333)
              ·
                refine ⟨39604662163004736985019875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211224864869358597253439333 39604662163004736985019875)
                ·
                  refine ⟨59406993244507105477529813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39604662163004736985019875 59406993244507105477529813)
                  ·
                    refine ⟨1392351404168135284629605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59406993244507105477529813 1392351404168135284629605)
                    ·
                      rfl

theorem cell23_8134784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_8134784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134784 prefixEnd_8134784 := by exact prefixLift 8134784
  have htrace : WordTrace (prefixWord ++ tailWord_8134784) baseStart_8134784 baseEnd_8134784 := by
    simpa [prefixWord, tailWord_8134784, baseEnd_8134784] using wordTrace_append hprefix tailTrace_8134784
  have hstable : (prefixWord ++ tailWord_8134784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134784).length < 2 ^ (prefixWord ++ tailWord_8134784).sum := by decide
  have hdescent : baseEnd_8134784 < baseStart_8134784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134821 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_8134821 : Nat := 118140960795 + 8134821 * 2 ^ 59
def prefixEnd_8134821 : Nat := 4983230072969 + 3 ^ 40 * 8134821 * 2
def baseEnd_8134821 : Nat := 4177073211288622209126145

theorem tailTrace_8134821 : CollatzResearch.WordTrace tailWord_8134821 prefixEnd_8134821 4177073211288622209126145 := by
  unfold tailWord_8134821
  simp only [CollatzResearch.WordTrace]
  refine ⟨296701296861940308662748317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197800864574626872441832211 296701296861940308662748317)
  ·
    refine ⟨111262986323227615748530619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296701296861940308662748317 111262986323227615748530619)
    ·
      refine ⟨166894479484841423622795929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111262986323227615748530619 166894479484841423622795929)
      ·
        refine ⟨125170859613631067717096947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166894479484841423622795929 125170859613631067717096947)
        ·
          refine ⟨187756289420446601575645421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125170859613631067717096947 187756289420446601575645421)
          ·
            refine ⟨70408608532667475590867033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187756289420446601575645421 70408608532667475590867033)
            ·
              refine ⟨52806456399500606693150275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70408608532667475590867033 52806456399500606693150275)
              ·
                refine ⟨79209684599250910039725413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52806456399500606693150275 79209684599250910039725413)
                ·
                  refine ⟨14851815862359545632448515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79209684599250910039725413 14851815862359545632448515)
                  ·
                    refine ⟨22277723793539318448672773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14851815862359545632448515 22277723793539318448672773)
                    ·
                      refine ⟨4177073211288622209126145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22277723793539318448672773 4177073211288622209126145)
                      ·
                        rfl

theorem cell23_8134821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_8134821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134821 prefixEnd_8134821 := by exact prefixLift 8134821
  have htrace : WordTrace (prefixWord ++ tailWord_8134821) baseStart_8134821 baseEnd_8134821 := by
    simpa [prefixWord, tailWord_8134821, baseEnd_8134821] using wordTrace_append hprefix tailTrace_8134821
  have hstable : (prefixWord ++ tailWord_8134821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134821).length < 2 ^ (prefixWord ++ tailWord_8134821).sum := by decide
  have hdescent : baseEnd_8134821 < baseStart_8134821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134841 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_8134841 : Nat := 118140960795 + 8134841 * 2 ^ 59
def prefixEnd_8134841 : Nat := 4983230072969 + 3 ^ 40 * 8134841 * 2
def baseEnd_8134841 : Nat := 4177083480901712130876053

theorem tailTrace_8134841 : CollatzResearch.WordTrace tailWord_8134841 prefixEnd_8134841 4177083480901712130876053 := by
  unfold tailWord_8134841
  simp only [CollatzResearch.WordTrace]
  refine ⟨296702026321867852078476377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197801350881245234718984251 296702026321867852078476377)
  ·
    refine ⟨222526519741400889058857283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296702026321867852078476377 222526519741400889058857283)
    ·
      refine ⟨333789779612101333588285925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222526519741400889058857283 333789779612101333588285925)
      ·
        refine ⟨62585583677269000047803611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333789779612101333588285925 62585583677269000047803611)
        ·
          refine ⟨93878375515903500071705417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62585583677269000047803611 93878375515903500071705417)
          ·
            refine ⟨70408781636927625053779063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93878375515903500071705417 70408781636927625053779063)
            ·
              refine ⟨105613172455391437580668595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70408781636927625053779063 105613172455391437580668595)
              ·
                refine ⟨158419758683087156371002893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105613172455391437580668595 158419758683087156371002893)
                ·
                  refine ⟨59407409506157683639126085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158419758683087156371002893 59407409506157683639126085)
                  ·
                    refine ⟨11138889282404565682336141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59407409506157683639126085 11138889282404565682336141)
                    ·
                      refine ⟨4177083480901712130876053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138889282404565682336141 4177083480901712130876053)
                      ·
                        rfl

theorem cell23_8134841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_8134841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134841 prefixEnd_8134841 := by exact prefixLift 8134841
  have htrace : WordTrace (prefixWord ++ tailWord_8134841) baseStart_8134841 baseEnd_8134841 := by
    simpa [prefixWord, tailWord_8134841, baseEnd_8134841] using wordTrace_append hprefix tailTrace_8134841
  have hstable : (prefixWord ++ tailWord_8134841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134841).length < 2 ^ (prefixWord ++ tailWord_8134841).sum := by decide
  have hdescent : baseEnd_8134841 < baseStart_8134841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134848 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 3, 4]
def baseStart_8134848 : Nat := 118140960795 + 8134848 * 2 ^ 59
def prefixEnd_8134848 : Nat := 4983230072969 + 3 ^ 40 * 8134848 * 2
def baseEnd_8134848 : Nat := 1392362358422097867829507

theorem tailTrace_8134848 : CollatzResearch.WordTrace tailWord_8134848 prefixEnd_8134848 1392362358422097867829507 := by
  unfold tailWord_8134848
  simp only [CollatzResearch.WordTrace]
  refine ⟨148351140816421246136990599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197801521088561661515987465 148351140816421246136990599)
  ·
    refine ⟨222526711224631869205485899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148351140816421246136990599 222526711224631869205485899)
    ·
      refine ⟨333790066836947803808228849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222526711224631869205485899 333790066836947803808228849)
      ·
        refine ⟨250342550127710852856171637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333790066836947803808228849 250342550127710852856171637)
        ·
          refine ⟨23469614074472892455266091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250342550127710852856171637 23469614074472892455266091)
          ·
            refine ⟨35204421111709338682899137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23469614074472892455266091 35204421111709338682899137)
            ·
              refine ⟨26403315833782004012174353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35204421111709338682899137 26403315833782004012174353)
              ·
                refine ⟨19802486875336503009130765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26403315833782004012174353 19802486875336503009130765)
                ·
                  refine ⟨7425932578251188628424037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19802486875336503009130765 7425932578251188628424037)
                  ·
                    refine ⟨1392362358422097867829507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425932578251188628424037 1392362358422097867829507)
                    ·
                      rfl

theorem cell23_8134848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_8134848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134848 prefixEnd_8134848 := by exact prefixLift 8134848
  have htrace : WordTrace (prefixWord ++ tailWord_8134848) baseStart_8134848 baseEnd_8134848 := by
    simpa [prefixWord, tailWord_8134848, baseEnd_8134848] using wordTrace_append hprefix tailTrace_8134848
  have hstable : (prefixWord ++ tailWord_8134848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134848).length < 2 ^ (prefixWord ++ tailWord_8134848).sum := by decide
  have hdescent : baseEnd_8134848 < baseStart_8134848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134858 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_8134858 : Nat := 118140960795 + 8134858 * 2 ^ 59
def prefixEnd_8134858 : Nat := 4983230072969 + 3 ^ 40 * 8134858 * 2
def baseEnd_8134858 : Nat := 4177092210072838564363475

theorem tailTrace_8134858 : CollatzResearch.WordTrace tailWord_8134858 prefixEnd_8134858 4177092210072838564363475 := by
  unfold tailWord_8134858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74175661590701565995461307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197801764241870842654563485 74175661590701565995461307)
  ·
    refine ⟨111263492386052348993191961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74175661590701565995461307 111263492386052348993191961)
    ·
      refine ⟨83447619289539261744893971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111263492386052348993191961 83447619289539261744893971)
      ·
        refine ⟨125171428934308892617340957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83447619289539261744893971 125171428934308892617340957)
        ·
          refine ⟨46939285850365834731502859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125171428934308892617340957 46939285850365834731502859)
          ·
            refine ⟨70408928775548752097254289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46939285850365834731502859 70408928775548752097254289)
            ·
              refine ⟨52806696581661564072940717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70408928775548752097254289 52806696581661564072940717)
              ·
                refine ⟨19802511218123086527352769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52806696581661564072940717 19802511218123086527352769)
                ·
                  refine ⟨14851883413592314895514577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19802511218123086527352769 14851883413592314895514577)
                  ·
                    refine ⟨11138912560194236171635933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14851883413592314895514577 11138912560194236171635933)
                    ·
                      refine ⟨4177092210072838564363475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11138912560194236171635933 4177092210072838564363475)
                      ·
                        rfl

theorem cell23_8134858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_8134858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134858 prefixEnd_8134858 := by exact prefixLift 8134858
  have htrace : WordTrace (prefixWord ++ tailWord_8134858) baseStart_8134858 baseEnd_8134858 := by
    simpa [prefixWord, tailWord_8134858, baseEnd_8134858] using wordTrace_append hprefix tailTrace_8134858
  have hstable : (prefixWord ++ tailWord_8134858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134858).length < 2 ^ (prefixWord ++ tailWord_8134858).sum := by decide
  have hdescent : baseEnd_8134858 < baseStart_8134858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134865 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 1, 4]
def baseStart_8134865 : Nat := 118140960795 + 8134865 * 2 ^ 59
def prefixEnd_8134865 : Nat := 4983230072969 + 3 ^ 40 * 8134865 * 2
def baseEnd_8134865 : Nat := 1392365268145806678991981

theorem tailTrace_8134865 : CollatzResearch.WordTrace tailWord_8134865 prefixEnd_8134865 1392365268145806678991981 := by
  unfold tailWord_8134865
  simp only [CollatzResearch.WordTrace]
  refine ⟨296702901673780904177350049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197801934449187269451566699 296702901673780904177350049)
  ·
    refine ⟨222527176255335678133012537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296702901673780904177350049 222527176255335678133012537)
    ·
      refine ⟨166895382191501758599759403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222527176255335678133012537 166895382191501758599759403)
      ·
        refine ⟨250343073287252637899639105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166895382191501758599759403 250343073287252637899639105)
        ·
          refine ⟨187757304965439478424729329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250343073287252637899639105 187757304965439478424729329)
          ·
            refine ⟨140817978724079608818546997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187757304965439478424729329 140817978724079608818546997)
            ·
              refine ⟨13201685505382463326738781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140817978724079608818546997 13201685505382463326738781)
              ·
                refine ⟨4950632064518423747527043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13201685505382463326738781 4950632064518423747527043)
                ·
                  refine ⟨7425948096777635621290565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950632064518423747527043 7425948096777635621290565)
                  ·
                    refine ⟨1392365268145806678991981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425948096777635621290565 1392365268145806678991981)
                    ·
                      rfl

theorem cell23_8134865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_8134865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134865 prefixEnd_8134865 := by exact prefixLift 8134865
  have htrace : WordTrace (prefixWord ++ tailWord_8134865) baseStart_8134865 baseEnd_8134865 := by
    simpa [prefixWord, tailWord_8134865, baseEnd_8134865] using wordTrace_append hprefix tailTrace_8134865
  have hstable : (prefixWord ++ tailWord_8134865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134865).length < 2 ^ (prefixWord ++ tailWord_8134865).sum := by decide
  have hdescent : baseEnd_8134865 < baseStart_8134865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134891 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 3, 5]
def baseStart_8134891 : Nat := 118140960795 + 8134891 * 2 ^ 59
def prefixEnd_8134891 : Nat := 4983230072969 + 3 ^ 40 * 8134891 * 2
def baseEnd_8134891 : Nat := 1392369718311478978416941

theorem tailTrace_8134891 : CollatzResearch.WordTrace tailWord_8134891 prefixEnd_8134891 1392369718311478978416941 := by
  unfold tailWord_8134891
  simp only [CollatzResearch.WordTrace]
  refine ⟨296703849971686710617796527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197802566647791140411864351 296703849971686710617796527)
  ·
    refine ⟨445055774957530065926694791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296703849971686710617796527 445055774957530065926694791)
    ·
      refine ⟨667583662436295098890042187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445055774957530065926694791 667583662436295098890042187)
      ·
        refine ⟨1001375493654442648335063281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667583662436295098890042187 1001375493654442648335063281)
        ·
          refine ⟨751031620240831986251297461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001375493654442648335063281 751031620240831986251297461)
          ·
            refine ⟨70409214397577998711059137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 751031620240831986251297461 70409214397577998711059137)
            ·
              refine ⟨52806910798183499033294353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70409214397577998711059137 52806910798183499033294353)
              ·
                refine ⟨39605183098637624274970765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52806910798183499033294353 39605183098637624274970765)
                ·
                  refine ⟨14851943661989109103114037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39605183098637624274970765 14851943661989109103114037)
                  ·
                    refine ⟨1392369718311478978416941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14851943661989109103114037 1392369718311478978416941)
                    ·
                      rfl

theorem cell23_8134891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 5].length) (baseStart_8134891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134891 prefixEnd_8134891 := by exact prefixLift 8134891
  have htrace : WordTrace (prefixWord ++ tailWord_8134891) baseStart_8134891 baseEnd_8134891 := by
    simpa [prefixWord, tailWord_8134891, baseEnd_8134891] using wordTrace_append hprefix tailTrace_8134891
  have hstable : (prefixWord ++ tailWord_8134891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134891).length < 2 ^ (prefixWord ++ tailWord_8134891).sum := by decide
  have hdescent : baseEnd_8134891 < baseStart_8134891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134895 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 6]
def baseStart_8134895 : Nat := 118140960795 + 8134895 * 2 ^ 59
def prefixEnd_8134895 : Nat := 4983230072969 + 3 ^ 40 * 8134895 * 2
def baseEnd_8134895 : Nat := 464123467650783879955645

theorem tailTrace_8134895 : CollatzResearch.WordTrace tailWord_8134895 prefixEnd_8134895 464123467650783879955645 := by
  unfold tailWord_8134895
  simp only [CollatzResearch.WordTrace]
  refine ⟨296703995863672219300942139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197802663909114812867294759 296703995863672219300942139)
  ·
    refine ⟨445055993795508328951413209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296703995863672219300942139 445055993795508328951413209)
    ·
      refine ⟨333791995346631246713559907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445055993795508328951413209 333791995346631246713559907)
      ·
        refine ⟨500687993019946870070339861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333791995346631246713559907 500687993019946870070339861)
        ·
          refine ⟨23469749672810009534547181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 500687993019946870070339861 23469749672810009534547181)
          ·
            refine ⟨8801156127303753575455193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23469749672810009534547181 8801156127303753575455193)
            ·
              refine ⟨6600867095477815181591395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8801156127303753575455193 6600867095477815181591395)
              ·
                refine ⟨9901300643216722772387093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600867095477815181591395 9901300643216722772387093)
                ·
                  refine ⟨464123467650783879955645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9901300643216722772387093 464123467650783879955645)
                  ·
                    rfl

theorem cell23_8134895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 6].length) (baseStart_8134895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134895 prefixEnd_8134895 := by exact prefixLift 8134895
  have htrace : WordTrace (prefixWord ++ tailWord_8134895) baseStart_8134895 baseEnd_8134895 := by
    simpa [prefixWord, tailWord_8134895, baseEnd_8134895] using wordTrace_append hprefix tailTrace_8134895
  have hstable : (prefixWord ++ tailWord_8134895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134895).length < 2 ^ (prefixWord ++ tailWord_8134895).sum := by decide
  have hdescent : baseEnd_8134895 < baseStart_8134895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134908 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_8134908 : Nat := 118140960795 + 8134908 * 2 ^ 59
def prefixEnd_8134908 : Nat := 4983230072969 + 3 ^ 40 * 8134908 * 2
def baseEnd_8134908 : Nat := 1392372628035187789579415

theorem tailTrace_8134908 : CollatzResearch.WordTrace tailWord_8134908 prefixEnd_8134908 1392372628035187789579415 := by
  unfold tailWord_8134908
  simp only [CollatzResearch.WordTrace]
  refine ⟨148352235006312561260582689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197802980008416748347443585 148352235006312561260582689)
  ·
    refine ⟨111264176254734420945437017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148352235006312561260582689 111264176254734420945437017)
    ·
      refine ⟨83448132191050815709077763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111264176254734420945437017 83448132191050815709077763)
      ·
        refine ⟨125172198286576223563616645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83448132191050815709077763 125172198286576223563616645)
        ·
          refine ⟨23469787178733041918178121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125172198286576223563616645 23469787178733041918178121)
          ·
            refine ⟨17602340384049781438633591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23469787178733041918178121 17602340384049781438633591)
            ·
              refine ⟨26403510576074672157950387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17602340384049781438633591 26403510576074672157950387)
              ·
                refine ⟨39605265864112008236925581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26403510576074672157950387 39605265864112008236925581)
                ·
                  refine ⟨14851974699042003088847093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39605265864112008236925581 14851974699042003088847093)
                  ·
                    refine ⟨1392372628035187789579415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14851974699042003088847093 1392372628035187789579415)
                    ·
                      rfl

theorem cell23_8134908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_8134908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134908 prefixEnd_8134908 := by exact prefixLift 8134908
  have htrace : WordTrace (prefixWord ++ tailWord_8134908) baseStart_8134908 baseEnd_8134908 := by
    simpa [prefixWord, tailWord_8134908, baseEnd_8134908] using wordTrace_append hprefix tailTrace_8134908
  have hstable : (prefixWord ++ tailWord_8134908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134908).length < 2 ^ (prefixWord ++ tailWord_8134908).sum := by decide
  have hdescent : baseEnd_8134908 < baseStart_8134908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134915 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 2, 3, 2]
def baseStart_8134915 : Nat := 118140960795 + 8134915 * 2 ^ 59
def prefixEnd_8134915 : Nat := 4983230072969 + 3 ^ 40 * 8134915 * 2
def baseEnd_8134915 : Nat := 4177121478470144841350713

theorem tailTrace_8134915 : CollatzResearch.WordTrace tailWord_8134915 prefixEnd_8134915 4177121478470144841350713 := by
  unfold tailWord_8134915
  simp only [CollatzResearch.WordTrace]
  refine ⟨296704725323599762716670199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197803150215733175144446799 296704725323599762716670199)
  ·
    refine ⟨445057087985399644075005299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296704725323599762716670199 445057087985399644075005299)
    ·
      refine ⟨667585631978099466112507949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445057087985399644075005299 667585631978099466112507949)
      ·
        refine ⟨250344611991787299792190481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667585631978099466112507949 250344611991787299792190481)
        ·
          refine ⟨187758458993840474844142861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250344611991787299792190481 187758458993840474844142861)
          ·
            refine ⟨70409422122690178066553573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187758458993840474844142861 70409422122690178066553573)
            ·
              refine ⟨13201766648004408387478795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70409422122690178066553573 13201766648004408387478795)
              ·
                refine ⟨19802649972006612581218193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13201766648004408387478795 19802649972006612581218193)
                ·
                  refine ⟨14851987479004959435913645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19802649972006612581218193 14851987479004959435913645)
                  ·
                    refine ⟨5569495304626859788467617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14851987479004959435913645 5569495304626859788467617)
                    ·
                      refine ⟨4177121478470144841350713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569495304626859788467617 4177121478470144841350713)
                      ·
                        rfl

theorem cell23_8134915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_8134915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134915 prefixEnd_8134915 := by exact prefixLift 8134915
  have htrace : WordTrace (prefixWord ++ tailWord_8134915) baseStart_8134915 baseEnd_8134915 := by
    simpa [prefixWord, tailWord_8134915, baseEnd_8134915] using wordTrace_append hprefix tailTrace_8134915
  have hstable : (prefixWord ++ tailWord_8134915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134915).length < 2 ^ (prefixWord ++ tailWord_8134915).sum := by decide
  have hdescent : baseEnd_8134915 < baseStart_8134915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134921 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_8134921 : Nat := 118140960795 + 8134921 * 2 ^ 59
def prefixEnd_8134921 : Nat := 4983230072969 + 3 ^ 40 * 8134921 * 2
def baseEnd_8134921 : Nat := 1392374853118023939291895

theorem tailTrace_8134921 : CollatzResearch.WordTrace tailWord_8134921 prefixEnd_8134921 1392374853118023939291895 := by
  unfold tailWord_8134921
  simp only [CollatzResearch.WordTrace]
  refine ⟨296704944161578025741388617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197803296107718683827592411 296704944161578025741388617)
  ·
    refine ⟨222528708121183519306041463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296704944161578025741388617 222528708121183519306041463)
    ·
      refine ⟨333793062181775278959062195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222528708121183519306041463 333793062181775278959062195)
      ·
        refine ⟨500689593272662918438593293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333793062181775278959062195 500689593272662918438593293)
        ·
          refine ⟨187758597477248594414472485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500689593272662918438593293 187758597477248594414472485)
          ·
            refine ⟨35204737026984111452713591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187758597477248594414472485 35204737026984111452713591)
            ·
              refine ⟨52807105540476167179070387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35204737026984111452713591 52807105540476167179070387)
              ·
                refine ⟨79210658310714250768605581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52807105540476167179070387 79210658310714250768605581)
                ·
                  refine ⟨29703996866517844038227093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79210658310714250768605581 29703996866517844038227093)
                  ·
                    refine ⟨1392374853118023939291895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29703996866517844038227093 1392374853118023939291895)
                    ·
                      rfl

theorem cell23_8134921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_8134921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134921 prefixEnd_8134921 := by exact prefixLift 8134921
  have htrace : WordTrace (prefixWord ++ tailWord_8134921) baseStart_8134921 baseEnd_8134921 := by
    simpa [prefixWord, tailWord_8134921, baseEnd_8134921] using wordTrace_append hprefix tailTrace_8134921
  have hstable : (prefixWord ++ tailWord_8134921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134921).length < 2 ^ (prefixWord ++ tailWord_8134921).sum := by decide
  have hdescent : baseEnd_8134921 < baseStart_8134921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134965 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_8134965 : Nat := 118140960795 + 8134965 * 2 ^ 59
def prefixEnd_8134965 : Nat := 4983230072969 + 3 ^ 40 * 8134965 * 2
def baseEnd_8134965 : Nat := 4177147152502869645725483

theorem tailTrace_8134965 : CollatzResearch.WordTrace tailWord_8134965 prefixEnd_8134965 4177147152502869645725483 := by
  unfold tailWord_8134965
  simp only [CollatzResearch.WordTrace]
  refine ⟨296706548973418621255990349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197804365982279080837326899 296706548973418621255990349)
  ·
    refine ⟨111264955865031982970996381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296706548973418621255990349 111264955865031982970996381)
    ·
      refine ⟨41724358449386993614123643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111264955865031982970996381 41724358449386993614123643)
      ·
        refine ⟨62586537674080490421185465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41724358449386993614123643 62586537674080490421185465)
        ·
          refine ⟨46939903255560367815889099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62586537674080490421185465 46939903255560367815889099)
          ·
            refine ⟨70409854883340551723833649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46939903255560367815889099 70409854883340551723833649)
            ·
              refine ⟨52807391162505413792875237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70409854883340551723833649 52807391162505413792875237)
              ·
                refine ⟨9901385842969765086164107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52807391162505413792875237 9901385842969765086164107)
                ·
                  refine ⟨14852078764454647629246161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9901385842969765086164107 14852078764454647629246161)
                  ·
                    refine ⟨11139059073340985721934621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14852078764454647629246161 11139059073340985721934621)
                    ·
                      refine ⟨4177147152502869645725483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139059073340985721934621 4177147152502869645725483)
                      ·
                        rfl

theorem cell23_8134965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_8134965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134965 prefixEnd_8134965 := by exact prefixLift 8134965
  have htrace : WordTrace (prefixWord ++ tailWord_8134965) baseStart_8134965 baseEnd_8134965 := by
    simpa [prefixWord, tailWord_8134965, baseEnd_8134965] using wordTrace_append hprefix tailTrace_8134965
  have hstable : (prefixWord ++ tailWord_8134965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134965).length < 2 ^ (prefixWord ++ tailWord_8134965).sum := by decide
  have hdescent : baseEnd_8134965 < baseStart_8134965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134991 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_8134991 : Nat := 118140960795 + 8134991 * 2 ^ 59
def prefixEnd_8134991 : Nat := 4983230072969 + 3 ^ 40 * 8134991 * 2
def baseEnd_8134991 : Nat := 4177160502999886544000363

theorem tailTrace_8134991 : CollatzResearch.WordTrace tailWord_8134991 prefixEnd_8134991 4177160502999886544000363 := by
  unfold tailWord_8134991
  simp only [CollatzResearch.WordTrace]
  refine ⟨296707497271324427696436827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197804998180882951797624551 296707497271324427696436827)
  ·
    refine ⟨445061245906986641544655241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296707497271324427696436827 445061245906986641544655241)
    ·
      refine ⟨333795934430239981158491431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445061245906986641544655241 333795934430239981158491431)
      ·
        refine ⟨500693901645359971737737147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333795934430239981158491431 500693901645359971737737147)
        ·
          refine ⟨751040852468039957606605721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500693901645359971737737147 751040852468039957606605721)
          ·
            refine ⟨563280639351029968204954291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751040852468039957606605721 563280639351029968204954291)
            ·
              refine ⟨844920959026544952307431437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563280639351029968204954291 844920959026544952307431437)
              ·
                refine ⟨316845359634954357115286789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 844920959026544952307431437 316845359634954357115286789)
                ·
                  refine ⟨59408504931553941959116273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316845359634954357115286789 59408504931553941959116273)
                  ·
                    refine ⟨44556378698665456469337205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59408504931553941959116273 44556378698665456469337205)
                    ·
                      refine ⟨4177160502999886544000363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44556378698665456469337205 4177160502999886544000363)
                      ·
                        rfl

theorem cell23_8134991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_8134991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134991 prefixEnd_8134991 := by exact prefixLift 8134991
  have htrace : WordTrace (prefixWord ++ tailWord_8134991) baseStart_8134991 baseEnd_8134991 := by
    simpa [prefixWord, tailWord_8134991, baseEnd_8134991] using wordTrace_append hprefix tailTrace_8134991
  have hstable : (prefixWord ++ tailWord_8134991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134991).length < 2 ^ (prefixWord ++ tailWord_8134991).sum := by decide
  have hdescent : baseEnd_8134991 < baseStart_8134991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134995 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 3]
def baseStart_8134995 : Nat := 118140960795 + 8134995 * 2 ^ 59
def prefixEnd_8134995 : Nat := 4983230072969 + 3 ^ 40 * 8134995 * 2
def baseEnd_8134995 : Nat := 4177162556922504528350345

theorem tailTrace_8134995 : CollatzResearch.WordTrace tailWord_8134995 prefixEnd_8134995 4177162556922504528350345 := by
  unfold tailWord_8134995
  simp only [CollatzResearch.WordTrace]
  refine ⟨296707643163309936379582439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197805095442206624253054959 296707643163309936379582439)
  ·
    refine ⟨445061464744964904569373659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296707643163309936379582439 445061464744964904569373659)
    ·
      refine ⟨667592197117447356854060489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445061464744964904569373659 667592197117447356854060489)
      ·
        refine ⟨500694147838085517640545367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667592197117447356854060489 500694147838085517640545367)
        ·
          refine ⟨751041221757128276460818051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500694147838085517640545367 751041221757128276460818051)
          ·
            refine ⟨1126561832635692414691227077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751041221757128276460818051 1126561832635692414691227077)
            ·
              refine ⟨211230343619192327754605077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1126561832635692414691227077 211230343619192327754605077)
              ·
                refine ⟨9901422357149640363497113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211230343619192327754605077 9901422357149640363497113)
                ·
                  refine ⟨7426066767862230272622835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901422357149640363497113 7426066767862230272622835)
                  ·
                    refine ⟨11139100151793345408934253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7426066767862230272622835 11139100151793345408934253)
                    ·
                      refine ⟨4177162556922504528350345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139100151793345408934253 4177162556922504528350345)
                      ·
                        rfl

theorem cell23_8134995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_8134995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8134995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8134995 prefixEnd_8134995 := by exact prefixLift 8134995
  have htrace : WordTrace (prefixWord ++ tailWord_8134995) baseStart_8134995 baseEnd_8134995 := by
    simpa [prefixWord, tailWord_8134995, baseEnd_8134995] using wordTrace_append hprefix tailTrace_8134995
  have hstable : (prefixWord ++ tailWord_8134995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134995).length < 2 ^ (prefixWord ++ tailWord_8134995).sum := by decide
  have hdescent : baseEnd_8134995 < baseStart_8134995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135030 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_8135030 : Nat := 118140960795 + 8135030 * 2 ^ 59
def prefixEnd_8135030 : Nat := 4983230072969 + 3 ^ 40 * 8135030 * 2
def baseEnd_8135030 : Nat := 4177180528745411891412685

theorem tailTrace_8135030 : CollatzResearch.WordTrace tailWord_8135030 prefixEnd_8135030 4177180528745411891412685 := by
  unfold tailWord_8135030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544307482386446084819159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197805946478788758238071029 18544307482386446084819159)
  ·
    refine ⟨27816461223579669127228739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18544307482386446084819159 27816461223579669127228739)
    ·
      refine ⟨41724691835369503690843109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27816461223579669127228739 41724691835369503690843109)
      ·
        refine ⟨7823379719131781942033083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41724691835369503690843109 7823379719131781942033083)
        ·
          refine ⟨11735069578697672913049625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823379719131781942033083 11735069578697672913049625)
          ·
            refine ⟨8801302184023254684787219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11735069578697672913049625 8801302184023254684787219)
            ·
              refine ⟨13201953276034882027180829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801302184023254684787219 13201953276034882027180829)
              ·
                refine ⟨4950732478513080760192811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13201953276034882027180829 4950732478513080760192811)
                ·
                  refine ⟨7426098717769621140289217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950732478513080760192811 7426098717769621140289217)
                  ·
                    refine ⟨5569574038327215855216913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426098717769621140289217 5569574038327215855216913)
                    ·
                      refine ⟨4177180528745411891412685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569574038327215855216913 4177180528745411891412685)
                      ·
                        rfl

theorem cell23_8135030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_8135030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135030 prefixEnd_8135030 := by exact prefixLift 8135030
  have htrace : WordTrace (prefixWord ++ tailWord_8135030) baseStart_8135030 baseEnd_8135030 := by
    simpa [prefixWord, tailWord_8135030, baseEnd_8135030] using wordTrace_append hprefix tailTrace_8135030
  have hstable : (prefixWord ++ tailWord_8135030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135030).length < 2 ^ (prefixWord ++ tailWord_8135030).sum := by decide
  have hdescent : baseEnd_8135030 < baseStart_8135030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135052 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 4, 2, 2]
def baseStart_8135052 : Nat := 118140960795 + 8135052 * 2 ^ 59
def prefixEnd_8135052 : Nat := 4983230072969 + 3 ^ 40 * 8135052 * 2
def baseEnd_8135052 : Nat := 4177191825319810805337583

theorem tailTrace_8135052 : CollatzResearch.WordTrace tailWord_8135052 prefixEnd_8135052 4177191825319810805337583 := by
  unfold tailWord_8135052
  simp only [CollatzResearch.WordTrace]
  refine ⟨148354861062051717557203705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197806481416068956742938273 148354861062051717557203705)
  ·
    refine ⟨111266145796538788167902779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148354861062051717557203705 111266145796538788167902779)
    ·
      refine ⟨166899218694808182251854169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111266145796538788167902779 166899218694808182251854169)
      ·
        refine ⟨125174414021106136688890627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166899218694808182251854169 125174414021106136688890627)
        ·
          refine ⟨187761621031659205033335941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125174414021106136688890627 187761621031659205033335941)
          ·
            refine ⟨35205303943436100943750489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187761621031659205033335941 35205303943436100943750489)
            ·
              refine ⟨26403977957577075707812867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35205303943436100943750489 26403977957577075707812867)
              ·
                refine ⟨39605966936365613561719301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26403977957577075707812867 39605966936365613561719301)
                ·
                  refine ⟨7426118800568552542822369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39605966936365613561719301 7426118800568552542822369)
                  ·
                    refine ⟨5569589100426414407116777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426118800568552542822369 5569589100426414407116777)
                    ·
                      refine ⟨4177191825319810805337583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569589100426414407116777 4177191825319810805337583)
                      ·
                        rfl

theorem cell23_8135052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_8135052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135052 prefixEnd_8135052 := by exact prefixLift 8135052
  have htrace : WordTrace (prefixWord ++ tailWord_8135052) baseStart_8135052 baseEnd_8135052 := by
    simpa [prefixWord, tailWord_8135052, baseEnd_8135052] using wordTrace_append hprefix tailTrace_8135052
  have hstable : (prefixWord ++ tailWord_8135052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135052).length < 2 ^ (prefixWord ++ tailWord_8135052).sum := by decide
  have hdescent : baseEnd_8135052 < baseStart_8135052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135073 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_8135073 : Nat := 118140960795 + 8135073 * 2 ^ 59
def prefixEnd_8135073 : Nat := 4983230072969 + 3 ^ 40 * 8135073 * 2
def baseEnd_8135073 : Nat := 4177202608413555223174987

theorem tailTrace_8135073 : CollatzResearch.WordTrace tailWord_8135073 prefixEnd_8135073 4177202608413555223174987 := by
  unfold tailWord_8135073
  simp only [CollatzResearch.WordTrace]
  refine ⟨296710488057027355700921873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197806992038018237133947915 296710488057027355700921873)
  ·
    refine ⟨222532866042770516775691405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296710488057027355700921873 222532866042770516775691405)
    ·
      refine ⟨83449824766038943790884277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222532866042770516775691405 83449824766038943790884277)
      ·
        refine ⟨7823421071816150980395401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83449824766038943790884277 7823421071816150980395401)
        ·
          refine ⟨5867565803862113235296551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7823421071816150980395401 5867565803862113235296551)
          ·
            refine ⟨8801348705793169852944827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867565803862113235296551 8801348705793169852944827)
            ·
              refine ⟨13202023058689754779417241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801348705793169852944827 13202023058689754779417241)
              ·
                refine ⟨9901517294017316084562931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13202023058689754779417241 9901517294017316084562931)
                ·
                  refine ⟨14852275941025974126844397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9901517294017316084562931 14852275941025974126844397)
                  ·
                    refine ⟨5569603477884740297566649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14852275941025974126844397 5569603477884740297566649)
                    ·
                      refine ⟨4177202608413555223174987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569603477884740297566649 4177202608413555223174987)
                      ·
                        rfl

theorem cell23_8135073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_8135073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135073 prefixEnd_8135073 := by exact prefixLift 8135073
  have htrace : WordTrace (prefixWord ++ tailWord_8135073) baseStart_8135073 baseEnd_8135073 := by
    simpa [prefixWord, tailWord_8135073, baseEnd_8135073] using wordTrace_append hprefix tailTrace_8135073
  have hstable : (prefixWord ++ tailWord_8135073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135073).length < 2 ^ (prefixWord ++ tailWord_8135073).sum := by decide
  have hdescent : baseEnd_8135073 < baseStart_8135073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135118 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_8135118 : Nat := 118140960795 + 8135118 * 2 ^ 59
def prefixEnd_8135118 : Nat := 4983230072969 + 3 ^ 40 * 8135118 * 2
def baseEnd_8135118 : Nat := 1392408571681002515704093

theorem tailTrace_8135118 : CollatzResearch.WordTrace tailWord_8135118 prefixEnd_8135118 1392408571681002515704093 := by
  unfold tailWord_8135118
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089016167733041048288751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197808086227909552257540005 37089016167733041048288751)
  ·
    refine ⟨55633524251599561572433127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37089016167733041048288751 55633524251599561572433127)
    ·
      refine ⟨83450286377399342358649691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55633524251599561572433127 83450286377399342358649691)
      ·
        refine ⟨125175429566099013537974537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83450286377399342358649691 125175429566099013537974537)
        ·
          refine ⟨93881572174574260153480903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125175429566099013537974537 93881572174574260153480903)
          ·
            refine ⟨140822358261861390230221355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93881572174574260153480903 140822358261861390230221355)
            ·
              refine ⟨211233537392792085345332033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140822358261861390230221355 211233537392792085345332033)
              ·
                refine ⟨158425153044594064008999025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211233537392792085345332033 158425153044594064008999025)
                ·
                  refine ⟨118818864783445548006749269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158425153044594064008999025 118818864783445548006749269)
                  ·
                    refine ⟨1392408571681002515704093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118818864783445548006749269 1392408571681002515704093)
                    ·
                      rfl

theorem cell23_8135118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_8135118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135118 prefixEnd_8135118 := by exact prefixLift 8135118
  have htrace : WordTrace (prefixWord ++ tailWord_8135118) baseStart_8135118 baseEnd_8135118 := by
    simpa [prefixWord, tailWord_8135118, baseEnd_8135118] using wordTrace_append hprefix tailTrace_8135118
  have hstable : (prefixWord ++ tailWord_8135118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135118).length < 2 ^ (prefixWord ++ tailWord_8135118).sum := by decide
  have hdescent : baseEnd_8135118 < baseStart_8135118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135135 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 5, 4]
def baseStart_8135135 : Nat := 118140960795 + 8135135 * 2 ^ 59
def prefixEnd_8135135 : Nat := 4983230072969 + 3 ^ 40 * 8135135 * 2
def baseEnd_8135135 : Nat := 1392411481404711326866567

theorem tailTrace_8135135 : CollatzResearch.WordTrace tailWord_8135135 prefixEnd_8135135 1392411481404711326866567 := by
  unfold tailWord_8135135
  simp only [CollatzResearch.WordTrace]
  refine ⟨296712749382802740289678859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197808499588535160193119239 296712749382802740289678859)
  ·
    refine ⟨445069124074204110434518289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296712749382802740289678859 445069124074204110434518289)
    ·
      refine ⟨333801843055653082825888717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445069124074204110434518289 333801843055653082825888717)
      ·
        refine ⟨125175691145869906059708269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333801843055653082825888717 125175691145869906059708269)
        ·
          refine ⟨46940884179701214772390601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125175691145869906059708269 46940884179701214772390601)
          ·
            refine ⟨35205663134775911079292951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46940884179701214772390601 35205663134775911079292951)
            ·
              refine ⟨52808494702163866618939427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35205663134775911079292951 52808494702163866618939427)
              ·
                refine ⟨79212742053245799928409141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52808494702163866618939427 79212742053245799928409141)
                ·
                  refine ⟨7426194567491793743288357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79212742053245799928409141 7426194567491793743288357)
                  ·
                    refine ⟨1392411481404711326866567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426194567491793743288357 1392411481404711326866567)
                    ·
                      rfl

theorem cell23_8135135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_8135135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135135 prefixEnd_8135135 := by exact prefixLift 8135135
  have htrace : WordTrace (prefixWord ++ tailWord_8135135) baseStart_8135135 baseEnd_8135135 := by
    simpa [prefixWord, tailWord_8135135, baseEnd_8135135] using wordTrace_append hprefix tailTrace_8135135
  have hstable : (prefixWord ++ tailWord_8135135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135135).length < 2 ^ (prefixWord ++ tailWord_8135135).sum := by decide
  have hdescent : baseEnd_8135135 < baseStart_8135135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135139 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 2, 5]
def baseStart_8135139 : Nat := 118140960795 + 8135139 * 2 ^ 59
def prefixEnd_8135139 : Nat := 4983230072969 + 3 ^ 40 * 8135139 * 2
def baseEnd_8135139 : Nat := 1392412166045583988316561

theorem tailTrace_8135139 : CollatzResearch.WordTrace tailWord_8135139 prefixEnd_8135139 1392412166045583988316561 := by
  unfold tailWord_8135139
  simp only [CollatzResearch.WordTrace]
  refine ⟨296712895274788248972824471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197808596849858832648549647 296712895274788248972824471)
  ·
    refine ⟨445069342912182373459236707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296712895274788248972824471 445069342912182373459236707)
    ·
      refine ⟨667604014368273560188855061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445069342912182373459236707 667604014368273560188855061)
      ·
        refine ⟨31293938173512823133852581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 667604014368273560188855061 31293938173512823133852581)
        ·
          refine ⟨5867613407533654337597359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31293938173512823133852581 5867613407533654337597359)
          ·
            refine ⟨8801420111300481506396039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867613407533654337597359 8801420111300481506396039)
            ·
              refine ⟨13202130166950722259594059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801420111300481506396039 13202130166950722259594059)
              ·
                refine ⟨19803195250426083389391089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13202130166950722259594059 19803195250426083389391089)
                ·
                  refine ⟨14852396437819562542043317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19803195250426083389391089 14852396437819562542043317)
                  ·
                    refine ⟨1392412166045583988316561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14852396437819562542043317 1392412166045583988316561)
                    ·
                      rfl

theorem cell23_8135139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 5].length) (baseStart_8135139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135139 prefixEnd_8135139 := by exact prefixLift 8135139
  have htrace : WordTrace (prefixWord ++ tailWord_8135139) baseStart_8135139 baseEnd_8135139 := by
    simpa [prefixWord, tailWord_8135139, baseEnd_8135139] using wordTrace_append hprefix tailTrace_8135139
  have hstable : (prefixWord ++ tailWord_8135139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135139).length < 2 ^ (prefixWord ++ tailWord_8135139).sum := by decide
  have hdescent : baseEnd_8135139 < baseStart_8135139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135145 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_8135145 : Nat := 118140960795 + 8135145 * 2 ^ 59
def prefixEnd_8135145 : Nat := 4983230072969 + 3 ^ 40 * 8135145 * 2
def baseEnd_8135145 : Nat := 4177239579020678941474655

theorem tailTrace_8135145 : CollatzResearch.WordTrace tailWord_8135145 prefixEnd_8135145 4177239579020678941474655 := by
  unfold tailWord_8135145
  simp only [CollatzResearch.WordTrace]
  refine ⟨296713114112766511997542889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197808742741844341331695259 296713114112766511997542889)
  ·
    refine ⟨222534835584574883998157167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296713114112766511997542889 222534835584574883998157167)
    ·
      refine ⟨333802253376862325997235751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222534835584574883998157167 333802253376862325997235751)
      ·
        refine ⟨500703380065293488995853627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333802253376862325997235751 500703380065293488995853627)
        ·
          refine ⟨751055070097940233493780441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500703380065293488995853627 751055070097940233493780441)
          ·
            refine ⟨563291302573455175120335331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751055070097940233493780441 563291302573455175120335331)
            ·
              refine ⟨844936953860182762680502997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563291302573455175120335331 844936953860182762680502997)
              ·
                refine ⟨19803209856098033500324289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 844936953860182762680502997 19803209856098033500324289)
                ·
                  refine ⟨14852407392073525125243217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19803209856098033500324289 14852407392073525125243217)
                  ·
                    refine ⟨11139305544055143843932413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14852407392073525125243217 11139305544055143843932413)
                    ·
                      refine ⟨4177239579020678941474655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139305544055143843932413 4177239579020678941474655)
                      ·
                        rfl

theorem cell23_8135145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_8135145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135145 prefixEnd_8135145 := by exact prefixLift 8135145
  have htrace : WordTrace (prefixWord ++ tailWord_8135145) baseStart_8135145 baseEnd_8135145 := by
    simpa [prefixWord, tailWord_8135145, baseEnd_8135145] using wordTrace_append hprefix tailTrace_8135145
  have hstable : (prefixWord ++ tailWord_8135145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135145).length < 2 ^ (prefixWord ++ tailWord_8135145).sum := by decide
  have hdescent : baseEnd_8135145 < baseStart_8135145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135148 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 8]
def baseStart_8135148 : Nat := 118140960795 + 8135148 * 2 ^ 59
def prefixEnd_8135148 : Nat := 4983230072969 + 3 ^ 40 * 8135148 * 2
def baseEnd_8135148 : Nat := 464137902162515825526349

theorem tailTrace_8135148 : CollatzResearch.WordTrace tailWord_8135148 prefixEnd_8135148 464137902162515825526349 := by
  unfold tailWord_8135148
  simp only [CollatzResearch.WordTrace]
  refine ⟨148356611765877821754951049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197808815687837095673268065 148356611765877821754951049)
  ·
    refine ⟨111267458824408366316213287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148356611765877821754951049 111267458824408366316213287)
    ·
      refine ⟨166901188236612549474319931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111267458824408366316213287 166901188236612549474319931)
      ·
        refine ⟨250351782354918824211479897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166901188236612549474319931 250351782354918824211479897)
        ·
          refine ⟨187763836766189118158609923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250351782354918824211479897 187763836766189118158609923)
          ·
            refine ⟨281645755149283677237914885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187763836766189118158609923 281645755149283677237914885)
            ·
              refine ⟨52808579090490689482109041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281645755149283677237914885 52808579090490689482109041)
              ·
                refine ⟨39606434317868017111581781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52808579090490689482109041 39606434317868017111581781)
                ·
                  refine ⟨464137902162515825526349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39606434317868017111581781 464137902162515825526349)
                  ·
                    rfl

theorem cell23_8135148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_8135148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135148 prefixEnd_8135148 := by exact prefixLift 8135148
  have htrace : WordTrace (prefixWord ++ tailWord_8135148) baseStart_8135148 baseEnd_8135148 := by
    simpa [prefixWord, tailWord_8135148, baseEnd_8135148] using wordTrace_append hprefix tailTrace_8135148
  have hstable : (prefixWord ++ tailWord_8135148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135148).length < 2 ^ (prefixWord ++ tailWord_8135148).sum := by decide
  have hdescent : baseEnd_8135148 < baseStart_8135148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135169 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 1, 4]
def baseStart_8135169 : Nat := 118140960795 + 8135169 * 2 ^ 59
def prefixEnd_8135169 : Nat := 4983230072969 + 3 ^ 40 * 8135169 * 2
def baseEnd_8135169 : Nat := 1392417300852128949191515

theorem tailTrace_8135169 : CollatzResearch.WordTrace tailWord_8135169 prefixEnd_8135169 1392417300852128949191515 := by
  unfold tailWord_8135169
  simp only [CollatzResearch.WordTrace]
  refine ⟨296713989464679564096416561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197809326309786376064277707 296713989464679564096416561)
  ·
    refine ⟨222535492098509673072312421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296713989464679564096416561 222535492098509673072312421)
    ·
      refine ⟨41725404768470563701058579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222535492098509673072312421 41725404768470563701058579)
      ·
        refine ⟨62588107152705845551587869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41725404768470563701058579 62588107152705845551587869)
        ·
          refine ⟨23470540182264692081845451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62588107152705845551587869 23470540182264692081845451)
          ·
            refine ⟨35205810273397038122768177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23470540182264692081845451 35205810273397038122768177)
            ·
              refine ⟨26404357705047778592076133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35205810273397038122768177 26404357705047778592076133)
              ·
                refine ⟨4950817069696458486014275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26404357705047778592076133 4950817069696458486014275)
                ·
                  refine ⟨7426225604544687729021413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950817069696458486014275 7426225604544687729021413)
                  ·
                    refine ⟨1392417300852128949191515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426225604544687729021413 1392417300852128949191515)
                    ·
                      rfl

theorem cell23_8135169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_8135169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135169 prefixEnd_8135169 := by exact prefixLift 8135169
  have htrace : WordTrace (prefixWord ++ tailWord_8135169) baseStart_8135169 baseEnd_8135169 := by
    simpa [prefixWord, tailWord_8135169, baseEnd_8135169] using wordTrace_append hprefix tailTrace_8135169
  have hstable : (prefixWord ++ tailWord_8135169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135169).length < 2 ^ (prefixWord ++ tailWord_8135169).sum := by decide
  have hdescent : baseEnd_8135169 < baseStart_8135169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135213 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8135213 : Nat := 118140960795 + 8135213 * 2 ^ 59
def prefixEnd_8135213 : Nat := 4983230072969 + 3 ^ 40 * 8135213 * 2
def baseEnd_8135213 : Nat := 4177274495705184675424343

theorem tailTrace_8135213 : CollatzResearch.WordTrace tailWord_8135213 prefixEnd_8135213 4177274495705184675424343 := by
  unfold tailWord_8135213
  simp only [CollatzResearch.WordTrace]
  refine ⟨296715594276520159611018293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197810396184346773074012195 296715594276520159611018293)
  ·
    refine ⟨27817086963423764963532965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296715594276520159611018293 27817086963423764963532965)
    ·
      refine ⟨5215703805641955930662431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27817086963423764963532965 5215703805641955930662431)
      ·
        refine ⟨7823555708462933895993647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215703805641955930662431 7823555708462933895993647)
        ·
          refine ⟨11735333562694400843990471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823555708462933895993647 11735333562694400843990471)
          ·
            refine ⟨17603000344041601265985707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735333562694400843990471 17603000344041601265985707)
            ·
              refine ⟨26404500516062401898978561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17603000344041601265985707 26404500516062401898978561)
              ·
                refine ⟨19803375387046801424233921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26404500516062401898978561 19803375387046801424233921)
                ·
                  refine ⟨14852531540285101068175441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19803375387046801424233921 14852531540285101068175441)
                  ·
                    refine ⟨11139398655213825801131581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14852531540285101068175441 11139398655213825801131581)
                    ·
                      refine ⟨4177274495705184675424343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139398655213825801131581 4177274495705184675424343)
                      ·
                        rfl

theorem cell23_8135213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8135213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135213 prefixEnd_8135213 := by exact prefixLift 8135213
  have htrace : WordTrace (prefixWord ++ tailWord_8135213) baseStart_8135213 baseEnd_8135213 := by
    simpa [prefixWord, tailWord_8135213, baseEnd_8135213] using wordTrace_append hprefix tailTrace_8135213
  have hstable : (prefixWord ++ tailWord_8135213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135213).length < 2 ^ (prefixWord ++ tailWord_8135213).sum := by decide
  have hdescent : baseEnd_8135213 < baseStart_8135213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135220 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_8135220 : Nat := 118140960795 + 8135220 * 2 ^ 59
def prefixEnd_8135220 : Nat := 4983230072969 + 3 ^ 40 * 8135220 * 2
def baseEnd_8135220 : Nat := 1392426030023255382678937

theorem tailTrace_8135220 : CollatzResearch.WordTrace tailWord_8135220 prefixEnd_8135220 1392426030023255382678937 := by
  unfold tailWord_8135220
  simp only [CollatzResearch.WordTrace]
  refine ⟨148357924793747399903261557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197810566391663199871015409 148357924793747399903261557)
  ·
    refine ⟨13908555449413818740930771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148357924793747399903261557 13908555449413818740930771)
    ·
      refine ⟨20862833174120728111396157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13908555449413818740930771 20862833174120728111396157)
      ·
        refine ⟨7823562440295273041773559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20862833174120728111396157 7823562440295273041773559)
        ·
          refine ⟨11735343660442909562660339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823562440295273041773559 11735343660442909562660339)
          ·
            refine ⟨17603015490664364343990509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735343660442909562660339 17603015490664364343990509)
            ·
              refine ⟨6601130808999136628996441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17603015490664364343990509 6601130808999136628996441)
              ·
                refine ⟨4950848106749352471747331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601130808999136628996441 4950848106749352471747331)
                ·
                  refine ⟨7426272160124028707620997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950848106749352471747331 7426272160124028707620997)
                  ·
                    refine ⟨1392426030023255382678937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426272160124028707620997 1392426030023255382678937)
                    ·
                      rfl

theorem cell23_8135220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_8135220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135220 prefixEnd_8135220 := by exact prefixLift 8135220
  have htrace : WordTrace (prefixWord ++ tailWord_8135220) baseStart_8135220 baseEnd_8135220 := by
    simpa [prefixWord, tailWord_8135220, baseEnd_8135220] using wordTrace_append hprefix tailTrace_8135220
  have hstable : (prefixWord ++ tailWord_8135220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135220).length < 2 ^ (prefixWord ++ tailWord_8135220).sum := by decide
  have hdescent : baseEnd_8135220 < baseStart_8135220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135249 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_8135249 : Nat := 118140960795 + 8135249 * 2 ^ 59
def prefixEnd_8135249 : Nat := 4983230072969 + 3 ^ 40 * 8135249 * 2
def baseEnd_8135249 : Nat := 4177292981008746534574177

theorem tailTrace_8135249 : CollatzResearch.WordTrace tailWord_8135249 prefixEnd_8135249 4177292981008746534574177 := by
  unfold tailWord_8135249
  simp only [CollatzResearch.WordTrace]
  refine ⟨296716907304389737759328801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197811271536259825172885867 296716907304389737759328801)
  ·
    refine ⟨222537680478292303319496601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296716907304389737759328801 222537680478292303319496601)
    ·
      refine ⟨166903260358719227489622451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222537680478292303319496601 166903260358719227489622451)
      ·
        refine ⟨250354890538078841234433677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166903260358719227489622451 250354890538078841234433677)
        ·
          refine ⟨93883083951779565462912629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250354890538078841234433677 93883083951779565462912629)
          ·
            refine ⟨8801539120479334262148059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93883083951779565462912629 8801539120479334262148059)
            ·
              refine ⟨13202308680719001393222089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801539120479334262148059 13202308680719001393222089)
              ·
                refine ⟨9901731510539251044916567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13202308680719001393222089 9901731510539251044916567)
                ·
                  refine ⟨14852597265808876567374851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9901731510539251044916567 14852597265808876567374851)
                  ·
                    refine ⟨22278895898713314851062277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14852597265808876567374851 22278895898713314851062277)
                    ·
                      refine ⟨4177292981008746534574177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22278895898713314851062277 4177292981008746534574177)
                      ·
                        rfl

theorem cell23_8135249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_8135249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135249 prefixEnd_8135249 := by exact prefixLift 8135249
  have htrace : WordTrace (prefixWord ++ tailWord_8135249) baseStart_8135249 baseEnd_8135249 := by
    simpa [prefixWord, tailWord_8135249, baseEnd_8135249] using wordTrace_append hprefix tailTrace_8135249
  have hstable : (prefixWord ++ tailWord_8135249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135249).length < 2 ^ (prefixWord ++ tailWord_8135249).sum := by decide
  have hdescent : baseEnd_8135249 < baseStart_8135249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135269 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_8135269 : Nat := 118140960795 + 8135269 * 2 ^ 59
def prefixEnd_8135269 : Nat := 4983230072969 + 3 ^ 40 * 8135269 * 2
def baseEnd_8135269 : Nat := 4177303250621836456324085

theorem tailTrace_8135269 : CollatzResearch.WordTrace tailWord_8135269 prefixEnd_8135269 4177303250621836456324085 := by
  unfold tailWord_8135269
  simp only [CollatzResearch.WordTrace]
  refine ⟨296717636764317281175056861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197811757842878187450037907 296717636764317281175056861)
  ·
    refine ⟨111269113786618980440646323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296717636764317281175056861 111269113786618980440646323)
    ·
      refine ⟨166903670679928470660969485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111269113786618980440646323 166903670679928470660969485)
      ·
        refine ⟨62588876504973176497863557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166903670679928470660969485 62588876504973176497863557)
        ·
          refine ⟨11735414344682470593349417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62588876504973176497863557 11735414344682470593349417)
          ·
            refine ⟨8801560758511852945012063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11735414344682470593349417 8801560758511852945012063)
            ·
              refine ⟨13202341137767779417518095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801560758511852945012063 13202341137767779417518095)
              ·
                refine ⟨19803511706651669126277143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13202341137767779417518095 19803511706651669126277143)
                ·
                  refine ⟨29705267559977503689415715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19803511706651669126277143 29705267559977503689415715)
                  ·
                    refine ⟨44557901339966255534123573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29705267559977503689415715 44557901339966255534123573)
                    ·
                      refine ⟨4177303250621836456324085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44557901339966255534123573 4177303250621836456324085)
                      ·
                        rfl

theorem cell23_8135269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_8135269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135269 prefixEnd_8135269 := by exact prefixLift 8135269
  have htrace : WordTrace (prefixWord ++ tailWord_8135269) baseStart_8135269 baseEnd_8135269 := by
    simpa [prefixWord, tailWord_8135269, baseEnd_8135269] using wordTrace_append hprefix tailTrace_8135269
  have hstable : (prefixWord ++ tailWord_8135269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135269).length < 2 ^ (prefixWord ++ tailWord_8135269).sum := by decide
  have hdescent : baseEnd_8135269 < baseStart_8135269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135272 : List Nat := [2, 1, 4, 3, 3, 10]
def baseStart_8135272 : Nat := 118140960795 + 8135272 * 2 ^ 59
def prefixEnd_8135272 : Nat := 4983230072969 + 3 ^ 40 * 8135272 * 2
def baseEnd_8135272 : Nat := 17190554695735802241097

theorem tailTrace_8135272 : CollatzResearch.WordTrace tailWord_8135272 prefixEnd_8135272 17190554695735802241097 := by
  unfold tailWord_8135272
  simp only [CollatzResearch.WordTrace]
  refine ⟨148358873091653206343708035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197811830788870941791610713 148358873091653206343708035)
  ·
    refine ⟨222538309637479809515562053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148358873091653206343708035 222538309637479809515562053)
    ·
      refine ⟨41725933057027464284167885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222538309637479809515562053 41725933057027464284167885)
      ·
        refine ⟨15647224896385299106562957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41725933057027464284167885 15647224896385299106562957)
        ·
          refine ⟨5867709336144487164961109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15647224896385299106562957 5867709336144487164961109)
          ·
            refine ⟨17190554695735802241097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5867709336144487164961109 17190554695735802241097)
            ·
              rfl

theorem cell23_8135272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 10].length) (baseStart_8135272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135272 prefixEnd_8135272 := by exact prefixLift 8135272
  have htrace : WordTrace (prefixWord ++ tailWord_8135272) baseStart_8135272 baseEnd_8135272 := by
    simpa [prefixWord, tailWord_8135272, baseEnd_8135272] using wordTrace_append hprefix tailTrace_8135272
  have hstable : (prefixWord ++ tailWord_8135272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135272).length < 2 ^ (prefixWord ++ tailWord_8135272).sum := by decide
  have hdescent : baseEnd_8135272 < baseStart_8135272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135299 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 3]
def baseStart_8135299 : Nat := 118140960795 + 8135299 * 2 ^ 59
def prefixEnd_8135299 : Nat := 4983230072969 + 3 ^ 40 * 8135299 * 2
def baseEnd_8135299 : Nat := 4177318655041471338948947

theorem tailTrace_8135299 : CollatzResearch.WordTrace tailWord_8135299 prefixEnd_8135299 4177318655041471338948947 := by
  unfold tailWord_8135299
  simp only [CollatzResearch.WordTrace]
  refine ⟨296718730954208596298648951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197812487302805730865765967 296718730954208596298648951)
  ·
    refine ⟨445078096431312894447973427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296718730954208596298648951 445078096431312894447973427)
    ·
      refine ⟨667617144646969341671960141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445078096431312894447973427 667617144646969341671960141)
      ·
        refine ⟨250356429242613503126985053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667617144646969341671960141 250356429242613503126985053)
        ·
          refine ⟨93883660965980063672619395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250356429242613503126985053 93883660965980063672619395)
          ·
            refine ⟨140825491448970095508929093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93883660965980063672619395 140825491448970095508929093)
            ·
              refine ⟨26404779646681892907924205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140825491448970095508929093 26404779646681892907924205)
              ·
                refine ⟨9901792367505709840471577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26404779646681892907924205 9901792367505709840471577)
                ·
                  refine ⟨7426344275629282380353683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901792367505709840471577 7426344275629282380353683)
                  ·
                    refine ⟨11139516413443923570530525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7426344275629282380353683 11139516413443923570530525)
                    ·
                      refine ⟨4177318655041471338948947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139516413443923570530525 4177318655041471338948947)
                      ·
                        rfl

theorem cell23_8135299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_8135299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135299 prefixEnd_8135299 := by exact prefixLift 8135299
  have htrace : WordTrace (prefixWord ++ tailWord_8135299) baseStart_8135299 baseEnd_8135299 := by
    simpa [prefixWord, tailWord_8135299, baseEnd_8135299] using wordTrace_append hprefix tailTrace_8135299
  have hstable : (prefixWord ++ tailWord_8135299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135299).length < 2 ^ (prefixWord ++ tailWord_8135299).sum := by decide
  have hdescent : baseEnd_8135299 < baseStart_8135299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135305 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_8135305 : Nat := 118140960795 + 8135305 * 2 ^ 59
def prefixEnd_8135305 : Nat := 4983230072969 + 3 ^ 40 * 8135305 * 2
def baseEnd_8135305 : Nat := 4177321735925398315473919

theorem tailTrace_8135305 : CollatzResearch.WordTrace tailWord_8135305 prefixEnd_8135305 4177321735925398315473919 := by
  unfold tailWord_8135305
  simp only [CollatzResearch.WordTrace]
  refine ⟨296718949792186859323367369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197812633194791239548911579 296718949792186859323367369)
  ·
    refine ⟨222539212344140144492525527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296718949792186859323367369 222539212344140144492525527)
    ·
      refine ⟨333808818516210216738788291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222539212344140144492525527 333808818516210216738788291)
      ·
        refine ⟨500713227774315325108182437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333808818516210216738788291 500713227774315325108182437)
        ·
          refine ⟨93883730207684123457784207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500713227774315325108182437 93883730207684123457784207)
          ·
            refine ⟨140825595311526185186676311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93883730207684123457784207 140825595311526185186676311)
            ·
              refine ⟨211238392967289277780014467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140825595311526185186676311 211238392967289277780014467)
              ·
                refine ⟨316857589450933916670021701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211238392967289277780014467 316857589450933916670021701)
                ·
                  refine ⟨59410798022050109375629069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316857589450933916670021701 59410798022050109375629069)
                  ·
                    refine ⟨22279049258268791015860901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59410798022050109375629069 22279049258268791015860901)
                    ·
                      refine ⟨4177321735925398315473919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22279049258268791015860901 4177321735925398315473919)
                      ·
                        rfl

theorem cell23_8135305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_8135305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135305 prefixEnd_8135305 := by exact prefixLift 8135305
  have htrace : WordTrace (prefixWord ++ tailWord_8135305) baseStart_8135305 baseEnd_8135305 := by
    simpa [prefixWord, tailWord_8135305, baseEnd_8135305] using wordTrace_append hprefix tailTrace_8135305
  have hstable : (prefixWord ++ tailWord_8135305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135305).length < 2 ^ (prefixWord ++ tailWord_8135305).sum := by decide
  have hdescent : baseEnd_8135305 < baseStart_8135305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135350 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_8135350 : Nat := 118140960795 + 8135350 * 2 ^ 59
def prefixEnd_8135350 : Nat := 4983230072969 + 3 ^ 40 * 8135350 * 2
def baseEnd_8135350 : Nat := 4177344842554850639411213

theorem tailTrace_8135350 : CollatzResearch.WordTrace tailWord_8135350 prefixEnd_8135350 4177344842554850639411213 := by
  unfold tailWord_8135350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545036942313989500547219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197813727384682554672503669 18545036942313989500547219)
  ·
    refine ⟨27817555413470984250820829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18545036942313989500547219 27817555413470984250820829)
    ·
      refine ⟨10431583280051619094057811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27817555413470984250820829 10431583280051619094057811)
      ·
        refine ⟨15647374920077428641086717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431583280051619094057811 15647374920077428641086717)
        ·
          refine ⟨5867765595029035740407519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15647374920077428641086717 5867765595029035740407519)
          ·
            refine ⟨8801648392543553610611279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867765595029035740407519 8801648392543553610611279)
            ·
              refine ⟨13202472588815330415916919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801648392543553610611279 13202472588815330415916919)
              ·
                refine ⟨19803708883222995623875379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13202472588815330415916919 19803708883222995623875379)
                ·
                  refine ⟨29705563324834493435813069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19803708883222995623875379 29705563324834493435813069)
                  ·
                    refine ⟨11139586246812935038429901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29705563324834493435813069 11139586246812935038429901)
                    ·
                      refine ⟨4177344842554850639411213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139586246812935038429901 4177344842554850639411213)
                      ·
                        rfl

theorem cell23_8135350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_8135350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135350 prefixEnd_8135350 := by exact prefixLift 8135350
  have htrace : WordTrace (prefixWord ++ tailWord_8135350) baseStart_8135350 baseEnd_8135350 := by
    simpa [prefixWord, tailWord_8135350, baseEnd_8135350] using wordTrace_append hprefix tailTrace_8135350
  have hstable : (prefixWord ++ tailWord_8135350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135350).length < 2 ^ (prefixWord ++ tailWord_8135350).sum := by decide
  have hdescent : baseEnd_8135350 < baseStart_8135350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135396 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 5]
def baseStart_8135396 : Nat := 118140960795 + 8135396 * 2 ^ 59
def prefixEnd_8135396 : Nat := 4983230072969 + 3 ^ 40 * 8135396 * 2
def baseEnd_8135396 : Nat := 464152051407217495492889

theorem tailTrace_8135396 : CollatzResearch.WordTrace tailWord_8135396 prefixEnd_8135396 464152051407217495492889 := by
  unfold tailWord_8135396
  simp only [CollatzResearch.WordTrace]
  refine ⟨148361134417428590932465021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197814845889904787909953361 148361134417428590932465021)
  ·
    refine ⟨55635425406535721599674383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148361134417428590932465021 55635425406535721599674383)
    ·
      refine ⟨83453138109803582399511575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55635425406535721599674383 83453138109803582399511575)
      ·
        refine ⟨125179707164705373599267363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83453138109803582399511575 125179707164705373599267363)
        ·
          refine ⟨187769560747058060398901045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125179707164705373599267363 187769560747058060398901045)
          ·
            refine ⟨17603396320036693162396973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187769560747058060398901045 17603396320036693162396973)
            ·
              refine ⟨6601273620013759935898865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17603396320036693162396973 6601273620013759935898865)
              ·
                refine ⟨4950955215010319951924149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601273620013759935898865 4950955215010319951924149)
                ·
                  refine ⟨464152051407217495492889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950955215010319951924149 464152051407217495492889)
                  ·
                    rfl

theorem cell23_8135396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_8135396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135396 prefixEnd_8135396 := by exact prefixLift 8135396
  have htrace : WordTrace (prefixWord ++ tailWord_8135396) baseStart_8135396 baseEnd_8135396 := by
    simpa [prefixWord, tailWord_8135396, baseEnd_8135396] using wordTrace_append hprefix tailTrace_8135396
  have hstable : (prefixWord ++ tailWord_8135396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135396).length < 2 ^ (prefixWord ++ tailWord_8135396).sum := by decide
  have hdescent : baseEnd_8135396 < baseStart_8135396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135426 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_8135426 : Nat := 118140960795 + 8135426 * 2 ^ 59
def prefixEnd_8135426 : Nat := 4983230072969 + 3 ^ 40 * 8135426 * 2
def baseEnd_8135426 : Nat := 1392461289028197447353621

theorem tailTrace_8135426 : CollatzResearch.WordTrace tailWord_8135426 prefixEnd_8135426 1392461289028197447353621 := by
  unfold tailWord_8135426
  simp only [CollatzResearch.WordTrace]
  refine ⟨74180840756187124247130533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197815575349832331325681421 74180840756187124247130533)
  ·
    refine ⟨13908907641785085796336975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74180840756187124247130533 13908907641785085796336975)
    ·
      refine ⟨20863361462677628694505463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13908907641785085796336975 20863361462677628694505463)
      ·
        refine ⟨31295042194016443041758195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20863361462677628694505463 31295042194016443041758195)
        ·
          refine ⟨46942563291024664562637293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31295042194016443041758195 46942563291024664562637293)
          ·
            refine ⟨17603461234134249210988985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46942563291024664562637293 17603461234134249210988985)
            ·
              refine ⟨13202595925600686908241739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17603461234134249210988985 13202595925600686908241739)
              ·
                refine ⟨19803893888401030362362609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13202595925600686908241739 19803893888401030362362609)
                ·
                  refine ⟨14852920416300772771771957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19803893888401030362362609 14852920416300772771771957)
                  ·
                    refine ⟨1392461289028197447353621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14852920416300772771771957 1392461289028197447353621)
                    ·
                      rfl

theorem cell23_8135426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_8135426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135426 prefixEnd_8135426 := by exact prefixLift 8135426
  have htrace : WordTrace (prefixWord ++ tailWord_8135426) baseStart_8135426 baseEnd_8135426 := by
    simpa [prefixWord, tailWord_8135426, baseEnd_8135426] using wordTrace_append hprefix tailTrace_8135426
  have hstable : (prefixWord ++ tailWord_8135426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135426).length < 2 ^ (prefixWord ++ tailWord_8135426).sum := by decide
  have hdescent : baseEnd_8135426 < baseStart_8135426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135506 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_8135506 : Nat := 118140960795 + 8135506 * 2 ^ 59
def prefixEnd_8135506 : Nat := 4983230072969 + 3 ^ 40 * 8135506 * 2
def baseEnd_8135506 : Nat := 4177424945536952029060495

theorem tailTrace_8135506 : CollatzResearch.WordTrace tailWord_8135506 prefixEnd_8135506 4177424945536952029060495 := by
  unfold tailWord_8135506
  simp only [CollatzResearch.WordTrace]
  refine ⟨74181570216114667662858593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197817520576305780434289581 74181570216114667662858593)
  ·
    refine ⟨55636177662086000747143945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74181570216114667662858593 55636177662086000747143945)
    ·
      refine ⟨41727133246564500560357959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55636177662086000747143945 41727133246564500560357959)
      ·
        refine ⟨62590699869846750840536939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41727133246564500560357959 62590699869846750840536939)
        ·
          refine ⟨93886049804770126260805409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62590699869846750840536939 93886049804770126260805409)
          ·
            refine ⟨70414537353577594695604057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93886049804770126260805409 70414537353577594695604057)
            ·
              refine ⟨52810903015183196021703043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70414537353577594695604057 52810903015183196021703043)
              ·
                refine ⟨79216354522774794032554565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52810903015183196021703043 79216354522774794032554565)
                ·
                  refine ⟨14853066473020273881103981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79216354522774794032554565 14853066473020273881103981)
                  ·
                    refine ⟨5569899927382602705413993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14853066473020273881103981 5569899927382602705413993)
                    ·
                      refine ⟨4177424945536952029060495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569899927382602705413993 4177424945536952029060495)
                      ·
                        rfl

theorem cell23_8135506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_8135506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135506 prefixEnd_8135506 := by exact prefixLift 8135506
  have htrace : WordTrace (prefixWord ++ tailWord_8135506) baseStart_8135506 baseEnd_8135506 := by
    simpa [prefixWord, tailWord_8135506, baseEnd_8135506] using wordTrace_append hprefix tailTrace_8135506
  have hstable : (prefixWord ++ tailWord_8135506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135506).length < 2 ^ (prefixWord ++ tailWord_8135506).sum := by decide
  have hdescent : baseEnd_8135506 < baseStart_8135506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135512 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_8135512 : Nat := 118140960795 + 8135512 * 2 ^ 59
def prefixEnd_8135512 : Nat := 4983230072969 + 3 ^ 40 * 8135512 * 2
def baseEnd_8135512 : Nat := 1392476008806959668528489

theorem tailTrace_8135512 : CollatzResearch.WordTrace tailWord_8135512 prefixEnd_8135512 1392476008806959668528489 := by
  unfold tailWord_8135512
  simp only [CollatzResearch.WordTrace]
  refine ⟨148363249851218466838076395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197817666468291289117435193 148363249851218466838076395)
  ·
    refine ⟨222544874776827700257114593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148363249851218466838076395 222544874776827700257114593)
    ·
      refine ⟨166908656082620775192835945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222544874776827700257114593 166908656082620775192835945)
      ·
        refine ⟨125181492061965581394626959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166908656082620775192835945 125181492061965581394626959)
        ·
          refine ⟨187772238092948372091940439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125181492061965581394626959 187772238092948372091940439)
          ·
            refine ⟨281658357139422558137910659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187772238092948372091940439 281658357139422558137910659)
            ·
              refine ⟨422487535709133837206865989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281658357139422558137910659 422487535709133837206865989)
              ·
                refine ⟨79216412945462594476287373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422487535709133837206865989 79216412945462594476287373)
                ·
                  refine ⟨29706154854548472928607765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79216412945462594476287373 29706154854548472928607765)
                  ·
                    refine ⟨1392476008806959668528489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29706154854548472928607765 1392476008806959668528489)
                    ·
                      rfl

theorem cell23_8135512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_8135512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135512 prefixEnd_8135512 := by exact prefixLift 8135512
  have htrace : WordTrace (prefixWord ++ tailWord_8135512) baseStart_8135512 baseEnd_8135512 := by
    simpa [prefixWord, tailWord_8135512, baseEnd_8135512] using wordTrace_append hprefix tailTrace_8135512
  have hstable : (prefixWord ++ tailWord_8135512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135512).length < 2 ^ (prefixWord ++ tailWord_8135512).sum := by decide
  have hdescent : baseEnd_8135512 < baseStart_8135512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135513 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 1, 1, 3]
def baseStart_8135513 : Nat := 118140960795 + 8135513 * 2 ^ 59
def prefixEnd_8135513 : Nat := 4983230072969 + 3 ^ 40 * 8135513 * 2
def baseEnd_8135513 : Nat := 4177428539901533501672963

theorem tailTrace_8135513 : CollatzResearch.WordTrace tailWord_8135513 prefixEnd_8135513 4177428539901533501672963 := by
  unfold tailWord_8135513
  simp only [CollatzResearch.WordTrace]
  refine ⟨296726536175433310846939193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197817690783622207231292795 296726536175433310846939193)
  ·
    refine ⟨222544902131574983135204395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296726536175433310846939193 222544902131574983135204395)
    ·
      refine ⟨333817353197362474702806593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222544902131574983135204395 333817353197362474702806593)
      ·
        refine ⟨250363014898021856027104945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333817353197362474702806593 250363014898021856027104945)
        ·
          refine ⟨187772261173516392020328709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250363014898021856027104945 187772261173516392020328709)
          ·
            refine ⟨35207298970034323503811633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187772261173516392020328709 35207298970034323503811633)
            ·
              refine ⟨26405474227525742627858725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35207298970034323503811633 26405474227525742627858725)
              ·
                refine ⟨4951026417661076742723511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26405474227525742627858725 4951026417661076742723511)
                ·
                  refine ⟨7426539626491615114085267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951026417661076742723511 7426539626491615114085267)
                  ·
                    refine ⟨11139809439737422671127901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7426539626491615114085267 11139809439737422671127901)
                    ·
                      refine ⟨4177428539901533501672963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139809439737422671127901 4177428539901533501672963)
                      ·
                        rfl

theorem cell23_8135513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_8135513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135513 prefixEnd_8135513 := by exact prefixLift 8135513
  have htrace : WordTrace (prefixWord ++ tailWord_8135513) baseStart_8135513 baseEnd_8135513 := by
    simpa [prefixWord, tailWord_8135513, baseEnd_8135513] using wordTrace_append hprefix tailTrace_8135513
  have hstable : (prefixWord ++ tailWord_8135513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135513).length < 2 ^ (prefixWord ++ tailWord_8135513).sum := by decide
  have hdescent : baseEnd_8135513 < baseStart_8135513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135539 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 3]
def baseStart_8135539 : Nat := 118140960795 + 8135539 * 2 ^ 59
def prefixEnd_8135539 : Nat := 4983230072969 + 3 ^ 40 * 8135539 * 2
def baseEnd_8135539 : Nat := 4177441890398550399947843

theorem tailTrace_8135539 : CollatzResearch.WordTrace tailWord_8135539 prefixEnd_8135539 4177441890398550399947843 := by
  unfold tailWord_8135539
  simp only [CollatzResearch.WordTrace]
  refine ⟨296727484473339117287385671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197818322982226078191590447 296727484473339117287385671)
  ·
    refine ⟨445091226710008675931078507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296727484473339117287385671 445091226710008675931078507)
    ·
      refine ⟨667636840065013013896617761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445091226710008675931078507 667636840065013013896617761)
      ·
        refine ⟨500727630048759760422463321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667636840065013013896617761 500727630048759760422463321)
        ·
          refine ⟨375545722536569820316847491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500727630048759760422463321 375545722536569820316847491)
          ·
            refine ⟨563318583804854730475271237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375545722536569820316847491 563318583804854730475271237)
            ·
              refine ⟨105622234463410261964113357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 563318583804854730475271237 105622234463410261964113357)
              ·
                refine ⟨39608337923778848236542509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105622234463410261964113357 39608337923778848236542509)
                ·
                  refine ⟨14853126721417068088703441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39608337923778848236542509 14853126721417068088703441)
                  ·
                    refine ⟨11139845041062801066527581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14853126721417068088703441 11139845041062801066527581)
                    ·
                      refine ⟨4177441890398550399947843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11139845041062801066527581 4177441890398550399947843)
                      ·
                        rfl

theorem cell23_8135539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_8135539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135539 prefixEnd_8135539 := by exact prefixLift 8135539
  have htrace : WordTrace (prefixWord ++ tailWord_8135539) baseStart_8135539 baseEnd_8135539 := by
    simpa [prefixWord, tailWord_8135539, baseEnd_8135539] using wordTrace_append hprefix tailTrace_8135539
  have hstable : (prefixWord ++ tailWord_8135539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135539).length < 2 ^ (prefixWord ++ tailWord_8135539).sum := by decide
  have hdescent : baseEnd_8135539 < baseStart_8135539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135549 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_8135549 : Nat := 118140960795 + 8135549 * 2 ^ 59
def prefixEnd_8135549 : Nat := 4983230072969 + 3 ^ 40 * 8135549 * 2
def baseEnd_8135549 : Nat := 4177447025205095360822797

theorem tailTrace_8135549 : CollatzResearch.WordTrace tailWord_8135549 prefixEnd_8135549 4177447025205095360822797 := by
  unfold tailWord_8135549
  simp only [CollatzResearch.WordTrace]
  refine ⟨296727849203302888995249701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197818566135535259330166467 296727849203302888995249701)
  ·
    refine ⟨55636471725619291686609319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296727849203302888995249701 55636471725619291686609319)
    ·
      refine ⟨83454707588428937529913979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55636471725619291686609319 83454707588428937529913979)
      ·
        refine ⟨125182061382643406294870969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83454707588428937529913979 125182061382643406294870969)
        ·
          refine ⟨93886546036982554721153227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125182061382643406294870969 93886546036982554721153227)
          ·
            refine ⟨140829819055473832081729841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93886546036982554721153227 140829819055473832081729841)
            ·
              refine ⟨105622364291605374061297381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140829819055473832081729841 105622364291605374061297381)
              ·
                refine ⟨19804193304676007636493259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105622364291605374061297381 19804193304676007636493259)
                ·
                  refine ⟨29706289957014011454739889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19804193304676007636493259 29706289957014011454739889)
                  ·
                    refine ⟨22279717467760508591054917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29706289957014011454739889 22279717467760508591054917)
                    ·
                      refine ⟨4177447025205095360822797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22279717467760508591054917 4177447025205095360822797)
                      ·
                        rfl

theorem cell23_8135549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_8135549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135549 prefixEnd_8135549 := by exact prefixLift 8135549
  have htrace : WordTrace (prefixWord ++ tailWord_8135549) baseStart_8135549 baseEnd_8135549 := by
    simpa [prefixWord, tailWord_8135549, baseEnd_8135549] using wordTrace_append hprefix tailTrace_8135549
  have hstable : (prefixWord ++ tailWord_8135549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135549).length < 2 ^ (prefixWord ++ tailWord_8135549).sum := by decide
  have hdescent : baseEnd_8135549 < baseStart_8135549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135559 : List Nat := [1, 1, 4, 2, 3, 3, 9]
def baseStart_8135559 : Nat := 118140960795 + 8135559 * 2 ^ 59
def prefixEnd_8135559 : Nat := 4983230072969 + 3 ^ 40 * 8135559 * 2
def baseEnd_8135559 : Nat := 51573483456933831132071

theorem tailTrace_8135559 : CollatzResearch.WordTrace tailWord_8135559 prefixEnd_8135559 51573483456933831132071 := by
  unfold tailWord_8135559
  simp only [CollatzResearch.WordTrace]
  refine ⟨296728213933266660703113731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197818809288844440468742487 296728213933266660703113731)
  ·
    refine ⟨445092320899899991054670597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296728213933266660703113731 445092320899899991054670597)
    ·
      refine ⟨83454810168731248322750737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445092320899899991054670597 83454810168731248322750737)
      ·
        refine ⟨62591107626548436242063053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83454810168731248322750737 62591107626548436242063053)
        ·
          refine ⟨23471665359955663590773645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62591107626548436242063053 23471665359955663590773645)
          ·
            refine ⟨8801874509983373846540117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23471665359955663590773645 8801874509983373846540117)
            ·
              refine ⟨51573483456933831132071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8801874509983373846540117 51573483456933831132071)
              ·
                rfl

theorem cell23_8135559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 9].length) (baseStart_8135559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135559 prefixEnd_8135559 := by exact prefixLift 8135559
  have htrace : WordTrace (prefixWord ++ tailWord_8135559) baseStart_8135559 baseEnd_8135559 := by
    simpa [prefixWord, tailWord_8135559, baseEnd_8135559] using wordTrace_append hprefix tailTrace_8135559
  have hstable : (prefixWord ++ tailWord_8135559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135559).length < 2 ^ (prefixWord ++ tailWord_8135559).sum := by decide
  have hdescent : baseEnd_8135559 < baseStart_8135559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135596 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 3, 3, 2]
def baseStart_8135596 : Nat := 118140960795 + 8135596 * 2 ^ 59
def prefixEnd_8135596 : Nat := 4983230072969 + 3 ^ 40 * 8135596 * 2
def baseEnd_8135596 : Nat := 4177471158795856676935081

theorem tailTrace_8135596 : CollatzResearch.WordTrace tailWord_8135596 prefixEnd_8135596 4177471158795856676935081 := by
  unfold tailWord_8135596
  simp only [CollatzResearch.WordTrace]
  refine ⟨148364781717066308011105321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197819708956088410681473761 148364781717066308011105321)
  ·
    refine ⟨111273586287799731008328991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148364781717066308011105321 111273586287799731008328991)
    ·
      refine ⟨166910379431699596512493487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111273586287799731008328991 166910379431699596512493487)
      ·
        refine ⟨250365569147549394768740231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166910379431699596512493487 250365569147549394768740231)
        ·
          refine ⟨375548353721324092153110347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250365569147549394768740231 375548353721324092153110347)
          ·
            refine ⟨563322530581986138229665521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375548353721324092153110347 563322530581986138229665521)
            ·
              refine ⟨422491897936489603672249141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563322530581986138229665521 422491897936489603672249141)
              ·
                refine ⟨39608615431545900344273357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422491897936489603672249141 39608615431545900344273357)
                ·
                  refine ⟨14853230786829712629102509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39608615431545900344273357 14853230786829712629102509)
                  ·
                    refine ⟨5569961545061142235913441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14853230786829712629102509 5569961545061142235913441)
                    ·
                      refine ⟨4177471158795856676935081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569961545061142235913441 4177471158795856676935081)
                      ·
                        rfl

theorem cell23_8135596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_8135596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135596 prefixEnd_8135596 := by exact prefixLift 8135596
  have htrace : WordTrace (prefixWord ++ tailWord_8135596) baseStart_8135596 baseEnd_8135596 := by
    simpa [prefixWord, tailWord_8135596, baseEnd_8135596] using wordTrace_append hprefix tailTrace_8135596
  have hstable : (prefixWord ++ tailWord_8135596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135596).length < 2 ^ (prefixWord ++ tailWord_8135596).sum := by decide
  have hdescent : baseEnd_8135596 < baseStart_8135596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135626 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_8135626 : Nat := 118140960795 + 8135626 * 2 ^ 59
def prefixEnd_8135626 : Nat := 4983230072969 + 3 ^ 40 * 8135626 * 2
def baseEnd_8135626 : Nat := 4177486563215491559559943

theorem tailTrace_8135626 : CollatzResearch.WordTrace tailWord_8135626 prefixEnd_8135626 4177486563215491559559943 := by
  unfold tailWord_8135626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74182664406005982786450683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197820438416015954097201821 74182664406005982786450683)
  ·
    refine ⟨111273996609008974179676025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74182664406005982786450683 111273996609008974179676025)
    ·
      refine ⟨83455497456756730634757019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111273996609008974179676025 83455497456756730634757019)
      ·
        refine ⟨125183246185135095952135529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83455497456756730634757019 125183246185135095952135529)
        ·
          refine ⟨93887434638851321964101647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125183246185135095952135529 93887434638851321964101647)
          ·
            refine ⟨140831151958276982946152471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93887434638851321964101647 140831151958276982946152471)
            ·
              refine ⟨211246727937415474419228707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140831151958276982946152471 211246727937415474419228707)
              ·
                refine ⟨316870091906123211628843061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211246727937415474419228707 316870091906123211628843061)
                ·
                  refine ⟨29706571116199051090204037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316870091906123211628843061 29706571116199051090204037)
                  ·
                    refine ⟨5569982084287322079413257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29706571116199051090204037 5569982084287322079413257)
                    ·
                      refine ⟨4177486563215491559559943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5569982084287322079413257 4177486563215491559559943)
                      ·
                        rfl

theorem cell23_8135626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_8135626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135626 prefixEnd_8135626 := by exact prefixLift 8135626
  have htrace : WordTrace (prefixWord ++ tailWord_8135626) baseStart_8135626 baseEnd_8135626 := by
    simpa [prefixWord, tailWord_8135626, baseEnd_8135626] using wordTrace_append hprefix tailTrace_8135626
  have hstable : (prefixWord ++ tailWord_8135626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135626).length < 2 ^ (prefixWord ++ tailWord_8135626).sum := by decide
  have hdescent : baseEnd_8135626 < baseStart_8135626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135636 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_8135636 : Nat := 118140960795 + 8135636 * 2 ^ 59
def prefixEnd_8135636 : Nat := 4983230072969 + 3 ^ 40 * 8135636 * 2
def baseEnd_8135636 : Nat := 1392497232674012173478299

theorem tailTrace_8135636 : CollatzResearch.WordTrace tailWord_8135636 prefixEnd_8135636 1392497232674012173478299 := by
  unfold tailWord_8135636
  simp only [CollatzResearch.WordTrace]
  refine ⟨148365511176993851426833381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197820681569325135235777841 148365511176993851426833381)
  ·
    refine ⟨27818533345686347142531259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148365511176993851426833381 27818533345686347142531259)
    ·
      refine ⟨41727800018529520713796889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27818533345686347142531259 41727800018529520713796889)
      ·
        refine ⟨31295850013897140535347667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41727800018529520713796889 31295850013897140535347667)
        ·
          refine ⟨46943775020845710803021501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31295850013897140535347667 46943775020845710803021501)
          ·
            refine ⟨17603915632817141551133063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46943775020845710803021501 17603915632817141551133063)
            ·
              refine ⟨26405873449225712326699595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17603915632817141551133063 26405873449225712326699595)
              ·
                refine ⟨39608810173838568490049393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26405873449225712326699595 39608810173838568490049393)
                ·
                  refine ⟨29706607630378926367537045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39608810173838568490049393 29706607630378926367537045)
                  ·
                    refine ⟨1392497232674012173478299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29706607630378926367537045 1392497232674012173478299)
                    ·
                      rfl

theorem cell23_8135636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_8135636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135636 prefixEnd_8135636 := by exact prefixLift 8135636
  have htrace : WordTrace (prefixWord ++ tailWord_8135636) baseStart_8135636 baseEnd_8135636 := by
    simpa [prefixWord, tailWord_8135636, baseEnd_8135636] using wordTrace_append hprefix tailTrace_8135636
  have hstable : (prefixWord ++ tailWord_8135636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135636).length < 2 ^ (prefixWord ++ tailWord_8135636).sum := by decide
  have hdescent : baseEnd_8135636 < baseStart_8135636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135676 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_8135676 : Nat := 118140960795 + 8135676 * 2 ^ 59
def prefixEnd_8135676 : Nat := 4983230072969 + 3 ^ 40 * 8135676 * 2
def baseEnd_8135676 : Nat := 4177512237248216363934713

theorem tailTrace_8135676 : CollatzResearch.WordTrace tailWord_8135676 prefixEnd_8135676 4177512237248216363934713 := by
  unfold tailWord_8135676
  simp only [CollatzResearch.WordTrace]
  refine ⟨148366240636921394842561441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197821654182561859790081921 148366240636921394842561441)
  ·
    refine ⟨111274680477691046131921081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148366240636921394842561441 111274680477691046131921081)
    ·
      refine ⟨83456010358268284598940811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111274680477691046131921081 83456010358268284598940811)
      ·
        refine ⟨125184015537402426898411217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83456010358268284598940811 125184015537402426898411217)
        ·
          refine ⟨93888011653051820173808413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125184015537402426898411217 93888011653051820173808413)
          ·
            refine ⟨35208004369894432565178155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93888011653051820173808413 35208004369894432565178155)
            ·
              refine ⟨52812006554841648847767233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35208004369894432565178155 52812006554841648847767233)
              ·
                refine ⟨39609004916131236635825425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52812006554841648847767233 39609004916131236635825425)
                ·
                  refine ⟨29706753687098427476869069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39609004916131236635825425 29706753687098427476869069)
                  ·
                    refine ⟨11140032632661910303825901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29706753687098427476869069 11140032632661910303825901)
                    ·
                      refine ⟨4177512237248216363934713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140032632661910303825901 4177512237248216363934713)
                      ·
                        rfl

theorem cell23_8135676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_8135676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135676 prefixEnd_8135676 := by exact prefixLift 8135676
  have htrace : WordTrace (prefixWord ++ tailWord_8135676) baseStart_8135676 baseEnd_8135676 := by
    simpa [prefixWord, tailWord_8135676, baseEnd_8135676] using wordTrace_append hprefix tailTrace_8135676
  have hstable : (prefixWord ++ tailWord_8135676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135676).length < 2 ^ (prefixWord ++ tailWord_8135676).sum := by decide
  have hdescent : baseEnd_8135676 < baseStart_8135676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135689 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_8135689 : Nat := 118140960795 + 8135689 * 2 ^ 59
def prefixEnd_8135689 : Nat := 4983230072969 + 3 ^ 40 * 8135689 * 2
def baseEnd_8135689 : Nat := 4177518912496724813072153

theorem tailTrace_8135689 : CollatzResearch.WordTrace tailWord_8135689 prefixEnd_8135689 4177518912496724813072153 := by
  unfold tailWord_8135689
  simp only [CollatzResearch.WordTrace]
  refine ⟨296732955422795692905346121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197821970281863795270230747 296732955422795692905346121)
  ·
    refine ⟨222549716567096769679009591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296732955422795692905346121 222549716567096769679009591)
    ·
      refine ⟨333824574850645154518514387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222549716567096769679009591 333824574850645154518514387)
      ·
        refine ⟨500736862275967731777771581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333824574850645154518514387 500736862275967731777771581)
        ·
          refine ⟨187776323353487899416664343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500736862275967731777771581 187776323353487899416664343)
          ·
            refine ⟨281664485030231849124996515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187776323353487899416664343 281664485030231849124996515)
            ·
              refine ⟨422496727545347773687494773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281664485030231849124996515 422496727545347773687494773)
              ·
                refine ⟨39609068207376353783202635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422496727545347773687494773 39609068207376353783202635)
                ·
                  refine ⟨59413602311064530674803953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39609068207376353783202635 59413602311064530674803953)
                  ·
                    refine ⟨44560201733298398006102965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59413602311064530674803953 44560201733298398006102965)
                    ·
                      refine ⟨4177518912496724813072153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44560201733298398006102965 4177518912496724813072153)
                      ·
                        rfl

theorem cell23_8135689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_8135689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135689 prefixEnd_8135689 := by exact prefixLift 8135689
  have htrace : WordTrace (prefixWord ++ tailWord_8135689) baseStart_8135689 baseEnd_8135689 := by
    simpa [prefixWord, tailWord_8135689, baseEnd_8135689] using wordTrace_append hprefix tailTrace_8135689
  have hstable : (prefixWord ++ tailWord_8135689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135689).length < 2 ^ (prefixWord ++ tailWord_8135689).sum := by decide
  have hdescent : baseEnd_8135689 < baseStart_8135689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135793 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 4, 3, 2]
def baseStart_8135793 : Nat := 118140960795 + 8135793 * 2 ^ 59
def prefixEnd_8135793 : Nat := 4983230072969 + 3 ^ 40 * 8135793 * 2
def baseEnd_8135793 : Nat := 4177572314484792406171675

theorem tailTrace_8135793 : CollatzResearch.WordTrace tailWord_8135793 prefixEnd_8135793 4177572314484792406171675 := by
  unfold tailWord_8135793
  simp only [CollatzResearch.WordTrace]
  refine ⟨296736748614418918667132033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197824499076279279111421355 296736748614418918667132033)
  ·
    refine ⟨222552561460814189000349025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296736748614418918667132033 222552561460814189000349025)
    ·
      refine ⟨166914421095610641750261769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222552561460814189000349025 166914421095610641750261769)
      ·
        refine ⟨125185815821707981312696327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166914421095610641750261769 125185815821707981312696327)
        ·
          refine ⟨187778723732561971969044491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125185815821707981312696327 187778723732561971969044491)
          ·
            refine ⟨281668085598842957953566737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187778723732561971969044491 281668085598842957953566737)
            ·
              refine ⟨211251064199132218465175053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281668085598842957953566737 211251064199132218465175053)
              ·
                refine ⟨79219149074674581924440645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211251064199132218465175053 79219149074674581924440645)
                ·
                  refine ⟨14853590451501484110832621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79219149074674581924440645 14853590451501484110832621)
                  ·
                    refine ⟨5570096419313056541562233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14853590451501484110832621 5570096419313056541562233)
                    ·
                      refine ⟨4177572314484792406171675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570096419313056541562233 4177572314484792406171675)
                      ·
                        rfl

theorem cell23_8135793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_8135793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135793 prefixEnd_8135793 := by exact prefixLift 8135793
  have htrace : WordTrace (prefixWord ++ tailWord_8135793) baseStart_8135793 baseEnd_8135793 := by
    simpa [prefixWord, tailWord_8135793, baseEnd_8135793] using wordTrace_append hprefix tailTrace_8135793
  have hstable : (prefixWord ++ tailWord_8135793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135793).length < 2 ^ (prefixWord ++ tailWord_8135793).sum := by decide
  have hdescent : baseEnd_8135793 < baseStart_8135793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135834 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3]
def baseStart_8135834 : Nat := 118140960795 + 8135834 * 2 ^ 59
def prefixEnd_8135834 : Nat := 4983230072969 + 3 ^ 40 * 8135834 * 2
def baseEnd_8135834 : Nat := 4177593367191626745758987

theorem tailTrace_8135834 : CollatzResearch.WordTrace tailWord_8135834 prefixEnd_8135834 4177593367191626745758987 := by
  unfold tailWord_8135834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74184561001817595667343639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197825496004846921779583037 74184561001817595667343639)
  ·
    refine ⟨111276841502726393501015459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74184561001817595667343639 111276841502726393501015459)
    ·
      refine ⟨166915262254089590251523189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111276841502726393501015459 166915262254089590251523189)
      ·
        refine ⟨15648305836320899086080299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166915262254089590251523189 15648305836320899086080299)
        ·
          refine ⟨23472458754481348629120449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15648305836320899086080299 23472458754481348629120449)
          ·
            refine ⟨17604344065861011471840337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23472458754481348629120449 17604344065861011471840337)
            ·
              refine ⟨13203258049395758603880253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17604344065861011471840337 13203258049395758603880253)
              ·
                refine ⟨4951221768523409476455095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13203258049395758603880253 4951221768523409476455095)
                ·
                  refine ⟨7426832652785114214682643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951221768523409476455095 7426832652785114214682643)
                  ·
                    refine ⟨11140248979177671322023965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7426832652785114214682643 11140248979177671322023965)
                    ·
                      refine ⟨4177593367191626745758987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140248979177671322023965 4177593367191626745758987)
                      ·
                        rfl

theorem cell23_8135834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_8135834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135834 prefixEnd_8135834 := by exact prefixLift 8135834
  have htrace : WordTrace (prefixWord ++ tailWord_8135834) baseStart_8135834 baseEnd_8135834 := by
    simpa [prefixWord, tailWord_8135834, baseEnd_8135834] using wordTrace_append hprefix tailTrace_8135834
  have hstable : (prefixWord ++ tailWord_8135834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135834).length < 2 ^ (prefixWord ++ tailWord_8135834).sum := by decide
  have hdescent : baseEnd_8135834 < baseStart_8135834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135840 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 5, 2, 2]
def baseStart_8135840 : Nat := 118140960795 + 8135840 * 2 ^ 59
def prefixEnd_8135840 : Nat := 4983230072969 + 3 ^ 40 * 8135840 * 2
def baseEnd_8135840 : Nat := 4177596448075553722283959

theorem tailTrace_8135840 : CollatzResearch.WordTrace tailWord_8135840 prefixEnd_8135840 4177596448075553722283959 := by
  unfold tailWord_8135840
  simp only [CollatzResearch.WordTrace]
  refine ⟨148369231422624322847046487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197825641896832430462728649 148369231422624322847046487)
  ·
    refine ⟨222553847133936484270569731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148369231422624322847046487 222553847133936484270569731)
    ·
      refine ⟨333830770700904726405854597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222553847133936484270569731 333830770700904726405854597)
      ·
        refine ⟨62593269506419636201097737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333830770700904726405854597 62593269506419636201097737)
        ·
          refine ⟨46944952129814727150823303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62593269506419636201097737 46944952129814727150823303)
          ·
            refine ⟨70417428194722090726234955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46944952129814727150823303 70417428194722090726234955)
            ·
              refine ⟨105626142292083136089352433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70417428194722090726234955 105626142292083136089352433)
              ·
                refine ⟨79219606719062352067014325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105626142292083136089352433 79219606719062352067014325)
                ·
                  refine ⟨7426838129912095506282593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79219606719062352067014325 7426838129912095506282593)
                  ·
                    refine ⟨5570128597434071629711945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426838129912095506282593 5570128597434071629711945)
                    ·
                      refine ⟨4177596448075553722283959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570128597434071629711945 4177596448075553722283959)
                      ·
                        rfl

theorem cell23_8135840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_8135840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135840 prefixEnd_8135840 := by exact prefixLift 8135840
  have htrace : WordTrace (prefixWord ++ tailWord_8135840) baseStart_8135840 baseEnd_8135840 := by
    simpa [prefixWord, tailWord_8135840, baseEnd_8135840] using wordTrace_append hprefix tailTrace_8135840
  have hstable : (prefixWord ++ tailWord_8135840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135840).length < 2 ^ (prefixWord ++ tailWord_8135840).sum := by decide
  have hdescent : baseEnd_8135840 < baseStart_8135840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135857 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 3, 2, 2]
def baseStart_8135857 : Nat := 118140960795 + 8135857 * 2 ^ 59
def prefixEnd_8135857 : Nat := 4983230072969 + 3 ^ 40 * 8135857 * 2
def baseEnd_8135857 : Nat := 4177605177246680155771381

theorem tailTrace_8135857 : CollatzResearch.WordTrace tailWord_8135857 prefixEnd_8135857 4177605177246680155771381 := by
  unfold tailWord_8135857
  simp only [CollatzResearch.WordTrace]
  refine ⟨296739082886187057597461825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197826055257458038398307883 296739082886187057597461825)
  ·
    refine ⟨222554312164640293198096369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296739082886187057597461825 222554312164640293198096369)
    ·
      refine ⟨166915734123480219898572277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222554312164640293198096369 166915734123480219898572277)
      ·
        refine ⟨15648350074076270615491151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166915734123480219898572277 15648350074076270615491151)
        ·
          refine ⟨23472525111114405923236727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15648350074076270615491151 23472525111114405923236727)
          ·
            refine ⟨35208787666671608884855091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23472525111114405923236727 35208787666671608884855091)
            ·
              refine ⟨52813181500007413327282637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35208787666671608884855091 52813181500007413327282637)
              ·
                refine ⟨19804943062502779997730989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52813181500007413327282637 19804943062502779997730989)
                ·
                  refine ⟨7426853648438542499149121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19804943062502779997730989 7426853648438542499149121)
                  ·
                    refine ⟨5570140236328906874361841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426853648438542499149121 5570140236328906874361841)
                    ·
                      refine ⟨4177605177246680155771381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570140236328906874361841 4177605177246680155771381)
                      ·
                        rfl

theorem cell23_8135857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_8135857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135857 prefixEnd_8135857 := by exact prefixLift 8135857
  have htrace : WordTrace (prefixWord ++ tailWord_8135857) baseStart_8135857 baseEnd_8135857 := by
    simpa [prefixWord, tailWord_8135857, baseEnd_8135857] using wordTrace_append hprefix tailTrace_8135857
  have hstable : (prefixWord ++ tailWord_8135857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135857).length < 2 ^ (prefixWord ++ tailWord_8135857).sum := by decide
  have hdescent : baseEnd_8135857 < baseStart_8135857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135870 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_8135870 : Nat := 118140960795 + 8135870 * 2 ^ 59
def prefixEnd_8135870 : Nat := 4983230072969 + 3 ^ 40 * 8135870 * 2
def baseEnd_8135870 : Nat := 4177611852495188604908821

theorem tailTrace_8135870 : CollatzResearch.WordTrace tailWord_8135870 prefixEnd_8135870 4177611852495188604908821 := by
  unfold tailWord_8135870
  simp only [CollatzResearch.WordTrace]
  refine ⟨37092444629392495102210633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197826371356759973878456709 37092444629392495102210633)
  ·
    refine ⟨27819333472044371326657975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37092444629392495102210633 27819333472044371326657975)
    ·
      refine ⟨41729000208066556989986963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27819333472044371326657975 41729000208066556989986963)
      ·
        refine ⟨62593500312099835484980445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41729000208066556989986963 62593500312099835484980445)
        ·
          refine ⟨23472562617037438306867667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62593500312099835484980445 23472562617037438306867667)
          ·
            refine ⟨35208843925556157460301501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23472562617037438306867667 35208843925556157460301501)
            ·
              refine ⟨13203316472083559047613063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35208843925556157460301501 13203316472083559047613063)
              ·
                refine ⟨19804974708125338571419595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13203316472083559047613063 19804974708125338571419595)
                ·
                  refine ⟨29707462062188007857129393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19804974708125338571419595 29707462062188007857129393)
                  ·
                    refine ⟨22280596546641005892847045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29707462062188007857129393 22280596546641005892847045)
                    ·
                      refine ⟨4177611852495188604908821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22280596546641005892847045 4177611852495188604908821)
                      ·
                        rfl

theorem cell23_8135870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_8135870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135870 prefixEnd_8135870 := by exact prefixLift 8135870
  have htrace : WordTrace (prefixWord ++ tailWord_8135870) baseStart_8135870 baseEnd_8135870 := by
    simpa [prefixWord, tailWord_8135870, baseEnd_8135870] using wordTrace_append hprefix tailTrace_8135870
  have hstable : (prefixWord ++ tailWord_8135870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135870).length < 2 ^ (prefixWord ++ tailWord_8135870).sum := by decide
  have hdescent : baseEnd_8135870 < baseStart_8135870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135885 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_8135885 : Nat := 118140960795 + 8135885 * 2 ^ 59
def prefixEnd_8135885 : Nat := 4983230072969 + 3 ^ 40 * 8135885 * 2
def baseEnd_8135885 : Nat := 4177619554705006046221253

theorem tailTrace_8135885 : CollatzResearch.WordTrace tailWord_8135885 prefixEnd_8135885 4177619554705006046221253 := by
  unfold tailWord_8135885
  simp only [CollatzResearch.WordTrace]
  refine ⟨296740104130085618379481109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197826736086723745586320739 296740104130085618379481109)
  ·
    refine ⟨13909692381097763361538177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296740104130085618379481109 13909692381097763361538177)
    ·
      refine ⟨10432269285823322521153633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13909692381097763361538177 10432269285823322521153633)
      ·
        refine ⟨7824201964367491890865225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10432269285823322521153633 7824201964367491890865225)
        ·
          refine ⟨5868151473275618918148919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7824201964367491890865225 5868151473275618918148919)
          ·
            refine ⟨8802227209913428377223379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868151473275618918148919 8802227209913428377223379)
            ·
              refine ⟨13203340814870142565835069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8802227209913428377223379 13203340814870142565835069)
              ·
                refine ⟨4951252805576303462188151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13203340814870142565835069 4951252805576303462188151)
                ·
                  refine ⟨7426879208364455193282227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951252805576303462188151 7426879208364455193282227)
                  ·
                    refine ⟨11140318812546682789923341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7426879208364455193282227 11140318812546682789923341)
                    ·
                      refine ⟨4177619554705006046221253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140318812546682789923341 4177619554705006046221253)
                      ·
                        rfl

theorem cell23_8135885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_8135885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135885 prefixEnd_8135885 := by exact prefixLift 8135885
  have htrace : WordTrace (prefixWord ++ tailWord_8135885) baseStart_8135885 baseEnd_8135885 := by
    simpa [prefixWord, tailWord_8135885, baseEnd_8135885] using wordTrace_append hprefix tailTrace_8135885
  have hstable : (prefixWord ++ tailWord_8135885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135885).length < 2 ^ (prefixWord ++ tailWord_8135885).sum := by decide
  have hdescent : baseEnd_8135885 < baseStart_8135885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135890 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_8135890 : Nat := 118140960795 + 8135890 * 2 ^ 59
def prefixEnd_8135890 : Nat := 4983230072969 + 3 ^ 40 * 8135890 * 2
def baseEnd_8135890 : Nat := 4177622122108278526658729

theorem tailTrace_8135890 : CollatzResearch.WordTrace tailWord_8135890 prefixEnd_8135890 4177622122108278526658729 := by
  unfold tailWord_8135890
  simp only [CollatzResearch.WordTrace]
  refine ⟨74185071623766876058353281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197826857663378336155608749 74185071623766876058353281)
  ·
    refine ⟨55638803717825157043764961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74185071623766876058353281 55638803717825157043764961)
    ·
      refine ⟨41729102788368867782823721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55638803717825157043764961 41729102788368867782823721)
      ·
        refine ⟨31296827091276650837117791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41729102788368867782823721 31296827091276650837117791)
        ·
          refine ⟨46945240636914976255676687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31296827091276650837117791 46945240636914976255676687)
          ·
            refine ⟨70417860955372464383515031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46945240636914976255676687 70417860955372464383515031)
            ·
              refine ⟨105626791433058696575272547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70417860955372464383515031 105626791433058696575272547)
              ·
                refine ⟨158440187149588044862908821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105626791433058696575272547 158440187149588044862908821)
                ·
                  refine ⟨7426883772636939602948851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158440187149588044862908821 7426883772636939602948851)
                  ·
                    refine ⟨11140325658955409404423277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7426883772636939602948851 11140325658955409404423277)
                    ·
                      refine ⟨4177622122108278526658729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140325658955409404423277 4177622122108278526658729)
                      ·
                        rfl

theorem cell23_8135890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_8135890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135890 prefixEnd_8135890 := by exact prefixLift 8135890
  have htrace : WordTrace (prefixWord ++ tailWord_8135890) baseStart_8135890 baseEnd_8135890 := by
    simpa [prefixWord, tailWord_8135890, baseEnd_8135890] using wordTrace_append hprefix tailTrace_8135890
  have hstable : (prefixWord ++ tailWord_8135890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135890).length < 2 ^ (prefixWord ++ tailWord_8135890).sum := by decide
  have hdescent : baseEnd_8135890 < baseStart_8135890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135913 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 8, 2]
def baseStart_8135913 : Nat := 118140960795 + 8135913 * 2 ^ 59
def prefixEnd_8135913 : Nat := 4983230072969 + 3 ^ 40 * 8135913 * 2
def baseEnd_8135913 : Nat := 4177633932163331936671123

theorem tailTrace_8135913 : CollatzResearch.WordTrace tailWord_8135913 prefixEnd_8135913 4177633932163331936671123 := by
  unfold tailWord_8135913
  simp only [CollatzResearch.WordTrace]
  refine ⟨296741125373984179161500393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197827416915989452774333595 296741125373984179161500393)
  ·
    refine ⟨222555844030488134371125295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296741125373984179161500393 222555844030488134371125295)
    ·
      refine ⟨333833766045732201556687943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222555844030488134371125295 333833766045732201556687943)
      ·
        refine ⟨500750649068598302335031915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333833766045732201556687943 500750649068598302335031915)
        ·
          refine ⟨751125973602897453502547873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500750649068598302335031915 751125973602897453502547873)
          ·
            refine ⟨563344480202173090126910905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751125973602897453502547873 563344480202173090126910905)
            ·
              refine ⟨422508360151629817595183179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563344480202173090126910905 422508360151629817595183179)
              ·
                refine ⟨633762540227444726392774769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422508360151629817595183179 633762540227444726392774769)
                ·
                  refine ⟨475321905170583544794581077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633762540227444726392774769 475321905170583544794581077)
                  ·
                    refine ⟨5570178576217775915561497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 475321905170583544794581077 5570178576217775915561497)
                    ·
                      refine ⟨4177633932163331936671123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570178576217775915561497 4177633932163331936671123)
                      ·
                        rfl

theorem cell23_8135913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 8, 2].length) (baseStart_8135913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135913 prefixEnd_8135913 := by exact prefixLift 8135913
  have htrace : WordTrace (prefixWord ++ tailWord_8135913) baseStart_8135913 baseEnd_8135913 := by
    simpa [prefixWord, tailWord_8135913, baseEnd_8135913] using wordTrace_append hprefix tailTrace_8135913
  have hstable : (prefixWord ++ tailWord_8135913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135913).length < 2 ^ (prefixWord ++ tailWord_8135913).sum := by decide
  have hdescent : baseEnd_8135913 < baseStart_8135913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135930 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2]
def baseStart_8135930 : Nat := 118140960795 + 8135930 * 2 ^ 59
def prefixEnd_8135930 : Nat := 4983230072969 + 3 ^ 40 * 8135930 * 2
def baseEnd_8135930 : Nat := 4177642661334458370158545

theorem tailTrace_8135930 : CollatzResearch.WordTrace tailWord_8135930 prefixEnd_8135930 4177642661334458370158545 := by
  unfold tailWord_8135930
  simp only [CollatzResearch.WordTrace]
  refine ⟨74185436353730647766217311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197827830276615060709912829 74185436353730647766217311)
  ·
    refine ⟨111278154530595971649325967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74185436353730647766217311 111278154530595971649325967)
    ·
      refine ⟨166917231795893957473988951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111278154530595971649325967 166917231795893957473988951)
      ·
        refine ⟨250375847693840936210983427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166917231795893957473988951 250375847693840936210983427)
        ·
          refine ⟨375563771540761404316475141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250375847693840936210983427 375563771540761404316475141)
          ·
            refine ⟨70418207163892763309339089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375563771540761404316475141 70418207163892763309339089)
            ·
              refine ⟨52813655372919572482004317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70418207163892763309339089 52813655372919572482004317)
              ·
                refine ⟨19805120764844839680751619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52813655372919572482004317 19805120764844839680751619)
                ·
                  refine ⟨29707681147267259521127429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19805120764844839680751619 29707681147267259521127429)
                  ·
                    refine ⟨5570190215112611160211393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29707681147267259521127429 5570190215112611160211393)
                    ·
                      refine ⟨4177642661334458370158545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570190215112611160211393 4177642661334458370158545)
                      ·
                        rfl

theorem cell23_8135930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_8135930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135930 prefixEnd_8135930 := by exact prefixLift 8135930
  have htrace : WordTrace (prefixWord ++ tailWord_8135930) baseStart_8135930 baseEnd_8135930 := by
    simpa [prefixWord, tailWord_8135930, baseEnd_8135930] using wordTrace_append hprefix tailTrace_8135930
  have hstable : (prefixWord ++ tailWord_8135930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135930).length < 2 ^ (prefixWord ++ tailWord_8135930).sum := by decide
  have hdescent : baseEnd_8135930 < baseStart_8135930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135934 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_8135934 : Nat := 118140960795 + 8135934 * 2 ^ 59
def prefixEnd_8135934 : Nat := 4983230072969 + 3 ^ 40 * 8135934 * 2
def baseEnd_8135934 : Nat := 4177644715257076354508527

theorem tailTrace_8135934 : CollatzResearch.WordTrace tailWord_8135934 prefixEnd_8135934 4177644715257076354508527 := by
  unfold tailWord_8135934
  simp only [CollatzResearch.WordTrace]
  refine ⟨37092736413363512468501857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197827927537938733165343237 37092736413363512468501857)
  ·
    refine ⟨27819552310022634351376393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37092736413363512468501857 27819552310022634351376393)
    ·
      refine ⟨20864664232516975763532295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27819552310022634351376393 20864664232516975763532295)
      ·
        refine ⟨31296996348775463645298443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20864664232516975763532295 31296996348775463645298443)
        ·
          refine ⟨46945494523163195467947665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31296996348775463645298443 46945494523163195467947665)
          ·
            refine ⟨35209120892372396600960749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46945494523163195467947665 35209120892372396600960749)
            ·
              refine ⟨13203420334639648725360281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35209120892372396600960749 13203420334639648725360281)
              ·
                refine ⟨9902565250979736544020211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13203420334639648725360281 9902565250979736544020211)
                ·
                  refine ⟨14853847876469604816030317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9902565250979736544020211 14853847876469604816030317)
                  ·
                    refine ⟨5570192953676101806011369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14853847876469604816030317 5570192953676101806011369)
                    ·
                      refine ⟨4177644715257076354508527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570192953676101806011369 4177644715257076354508527)
                      ·
                        rfl

theorem cell23_8135934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_8135934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135934 prefixEnd_8135934 := by exact prefixLift 8135934
  have htrace : WordTrace (prefixWord ++ tailWord_8135934) baseStart_8135934 baseEnd_8135934 := by
    simpa [prefixWord, tailWord_8135934, baseEnd_8135934] using wordTrace_append hprefix tailTrace_8135934
  have hstable : (prefixWord ++ tailWord_8135934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135934).length < 2 ^ (prefixWord ++ tailWord_8135934).sum := by decide
  have hdescent : baseEnd_8135934 < baseStart_8135934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135936 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 9]
def baseStart_8135936 : Nat := 118140960795 + 8135936 * 2 ^ 59
def prefixEnd_8135936 : Nat := 4983230072969 + 3 ^ 40 * 8135936 * 2
def baseEnd_8135936 : Nat := 464182860246487260742613

theorem tailTrace_8135936 : CollatzResearch.WordTrace tailWord_8135936 prefixEnd_8135936 464182860246487260742613 := by
  unfold tailWord_8135936
  simp only [CollatzResearch.WordTrace]
  refine ⟨148370982126450427044793831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197827976168600569393058441 148370982126450427044793831)
  ·
    refine ⟨222556473189675640567190747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148370982126450427044793831 222556473189675640567190747)
    ·
      refine ⟨333834709784513460850786121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222556473189675640567190747 333834709784513460850786121)
      ·
        refine ⟨250376032338385095638089591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333834709784513460850786121 250376032338385095638089591)
        ·
          refine ⟨375564048507577643457134387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250376032338385095638089591 375564048507577643457134387)
          ·
            refine ⟨563346072761366465185701581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375564048507577643457134387 563346072761366465185701581)
            ·
              refine ⟨211254777285512424444638093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563346072761366465185701581 211254777285512424444638093)
              ·
                refine ⟨79220541482067159166739285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211254777285512424444638093 79220541482067159166739285)
                ·
                  refine ⟨464182860246487260742613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79220541482067159166739285 464182860246487260742613)
                  ·
                    rfl

theorem cell23_8135936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_8135936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135936 prefixEnd_8135936 := by exact prefixLift 8135936
  have htrace : WordTrace (prefixWord ++ tailWord_8135936) baseStart_8135936 baseEnd_8135936 := by
    simpa [prefixWord, tailWord_8135936, baseEnd_8135936] using wordTrace_append hprefix tailTrace_8135936
  have hstable : (prefixWord ++ tailWord_8135936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135936).length < 2 ^ (prefixWord ++ tailWord_8135936).sum := by decide
  have hdescent : baseEnd_8135936 < baseStart_8135936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135963 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 3]
def baseStart_8135963 : Nat := 118140960795 + 8135963 * 2 ^ 59
def prefixEnd_8135963 : Nat := 4983230072969 + 3 ^ 40 * 8135963 * 2
def baseEnd_8135963 : Nat := 4177659606196056741045893

theorem tailTrace_8135963 : CollatzResearch.WordTrace tailWord_8135963 prefixEnd_8135963 4177659606196056741045893 := by
  unfold tailWord_8135963
  simp only [CollatzResearch.WordTrace]
  refine ⟨296742949023803037700820543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197828632682535358467213695 296742949023803037700820543)
  ·
    refine ⟨445114423535704556551230815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296742949023803037700820543 445114423535704556551230815)
    ·
      refine ⟨667671635303556834826846223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445114423535704556551230815 667671635303556834826846223)
      ·
        refine ⟨1001507452955335252240269335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667671635303556834826846223 1001507452955335252240269335)
        ·
          refine ⟨1502261179433002878360404003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001507452955335252240269335 1502261179433002878360404003)
          ·
            refine ⟨2253391769149504317540606005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502261179433002878360404003 2253391769149504317540606005)
            ·
              refine ⟨211255478357766029769431813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2253391769149504317540606005 211255478357766029769431813)
              ·
                refine ⟨39610402192081130581768465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211255478357766029769431813 39610402192081130581768465)
                ·
                  refine ⟨29707801644060847936326349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39610402192081130581768465 29707801644060847936326349)
                  ·
                    refine ⟨11140425616522817976122381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29707801644060847936326349 11140425616522817976122381)
                    ·
                      refine ⟨4177659606196056741045893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140425616522817976122381 4177659606196056741045893)
                      ·
                        rfl

theorem cell23_8135963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 3].length) (baseStart_8135963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135963 prefixEnd_8135963 := by exact prefixLift 8135963
  have htrace : WordTrace (prefixWord ++ tailWord_8135963) baseStart_8135963 baseEnd_8135963 := by
    simpa [prefixWord, tailWord_8135963, baseEnd_8135963] using wordTrace_append hprefix tailTrace_8135963
  have hstable : (prefixWord ++ tailWord_8135963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135963).length < 2 ^ (prefixWord ++ tailWord_8135963).sum := by decide
  have hdescent : baseEnd_8135963 < baseStart_8135963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8135981 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_8135981 : Nat := 118140960795 + 8135981 * 2 ^ 59
def prefixEnd_8135981 : Nat := 4983230072969 + 3 ^ 40 * 8135981 * 2
def baseEnd_8135981 : Nat := 4177668848847837670620811

theorem tailTrace_8135981 : CollatzResearch.WordTrace tailWord_8135981 prefixEnd_8135981 4177668848847837670620811 := by
  unfold tailWord_8135981
  simp only [CollatzResearch.WordTrace]
  refine ⟨296743605537737826774975797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197829070358491884516650531 296743605537737826774975797)
  ·
    refine ⟨27819713019162921260153981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296743605537737826774975797 27819713019162921260153981)
    ·
      refine ⟨10432392382186095472557743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27819713019162921260153981 10432392382186095472557743)
      ·
        refine ⟨15648588573279143208836615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432392382186095472557743 15648588573279143208836615)
        ·
          refine ⟨23472882859918714813254923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15648588573279143208836615 23472882859918714813254923)
          ·
            refine ⟨35209324289878072219882385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23472882859918714813254923 35209324289878072219882385)
            ·
              refine ⟨26406993217408554164911789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35209324289878072219882385 26406993217408554164911789)
              ·
                refine ⟨9902622456528207811841921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26406993217408554164911789 9902622456528207811841921)
                ·
                  refine ⟨7426966842396155858881441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902622456528207811841921 7426966842396155858881441)
                  ·
                    refine ⟨5570225131797116894161081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426966842396155858881441 5570225131797116894161081)
                    ·
                      refine ⟨4177668848847837670620811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570225131797116894161081 4177668848847837670620811)
                      ·
                        rfl

theorem cell23_8135981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_8135981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8135981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8135981 prefixEnd_8135981 := by exact prefixLift 8135981
  have htrace : WordTrace (prefixWord ++ tailWord_8135981) baseStart_8135981 baseEnd_8135981 := by
    simpa [prefixWord, tailWord_8135981, baseEnd_8135981] using wordTrace_append hprefix tailTrace_8135981
  have hstable : (prefixWord ++ tailWord_8135981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8135981).length < 2 ^ (prefixWord ++ tailWord_8135981).sum := by decide
  have hdescent : baseEnd_8135981 < baseStart_8135981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8135981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136004 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 5]
def baseStart_8136004 : Nat := 118140960795 + 8136004 * 2 ^ 59
def prefixEnd_8136004 : Nat := 4983230072969 + 3 ^ 40 * 8136004 * 2
def baseEnd_8136004 : Nat := 464186739878099008959245

theorem tailTrace_8136004 : CollatzResearch.WordTrace tailWord_8136004 prefixEnd_8136004 464186739878099008959245 := by
  unfold tailWord_8136004
  simp only [CollatzResearch.WordTrace]
  refine ⟨148372222208327250851531533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197829629611103001135375377 148372222208327250851531533)
  ·
    refine ⟨55639583328122719069324325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148372222208327250851531533 55639583328122719069324325)
    ·
      refine ⟨10432421874023009825498311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55639583328122719069324325 10432421874023009825498311)
      ·
        refine ⟨15648632811034514738247467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432421874023009825498311 15648632811034514738247467)
        ·
          refine ⟨23472949216551772107371201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15648632811034514738247467 23472949216551772107371201)
          ·
            refine ⟨17604711912413829080528401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23472949216551772107371201 17604711912413829080528401)
            ·
              refine ⟨13203533934310371810396301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17604711912413829080528401 13203533934310371810396301)
              ·
                refine ⟨4951325225366389428898613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13203533934310371810396301 4951325225366389428898613)
                ·
                  refine ⟨464186739878099008959245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4951325225366389428898613 464186739878099008959245)
                  ·
                    rfl

theorem cell23_8136004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_8136004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136004 prefixEnd_8136004 := by exact prefixLift 8136004
  have htrace : WordTrace (prefixWord ++ tailWord_8136004) baseStart_8136004 baseEnd_8136004 := by
    simpa [prefixWord, tailWord_8136004, baseEnd_8136004] using wordTrace_append hprefix tailTrace_8136004
  have hstable : (prefixWord ++ tailWord_8136004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136004).length < 2 ^ (prefixWord ++ tailWord_8136004).sum := by decide
  have hdescent : baseEnd_8136004 < baseStart_8136004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136020 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_8136020 : Nat := 118140960795 + 8136020 * 2 ^ 59
def prefixEnd_8136020 : Nat := 4983230072969 + 3 ^ 40 * 8136020 * 2
def baseEnd_8136020 : Nat := 4177688874593363018033131

theorem tailTrace_8136020 : CollatzResearch.WordTrace tailWord_8136020 prefixEnd_8136020 4177688874593363018033131 := by
  unfold tailWord_8136020
  simp only [CollatzResearch.WordTrace]
  refine ⟨148372513992298268217822757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197830018656397690957097009 148372513992298268217822757)
  ·
    refine ⟨27819846373555925290841767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148372513992298268217822757 27819846373555925290841767)
    ·
      refine ⟨41729769560333887936262651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27819846373555925290841767 41729769560333887936262651)
      ·
        refine ⟨62594654340500831904393977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41729769560333887936262651 62594654340500831904393977)
        ·
          refine ⟨46945990755375623928295483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62594654340500831904393977 46945990755375623928295483)
          ·
            refine ⟨70418986133063435892443225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46945990755375623928295483 70418986133063435892443225)
            ·
              refine ⟨52814239599797576919332419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70418986133063435892443225 52814239599797576919332419)
              ·
                refine ⟨79221359399696365378998629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52814239599797576919332419 79221359399696365378998629)
                ·
                  refine ⟨14854004887443068508562243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79221359399696365378998629 14854004887443068508562243)
                  ·
                    refine ⟨22281007331164602762843365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14854004887443068508562243 22281007331164602762843365)
                    ·
                      refine ⟨4177688874593363018033131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22281007331164602762843365 4177688874593363018033131)
                      ·
                        rfl

theorem cell23_8136020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_8136020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136020 prefixEnd_8136020 := by exact prefixLift 8136020
  have htrace : WordTrace (prefixWord ++ tailWord_8136020) baseStart_8136020 baseEnd_8136020 := by
    simpa [prefixWord, tailWord_8136020, baseEnd_8136020] using wordTrace_append hprefix tailTrace_8136020
  have hstable : (prefixWord ++ tailWord_8136020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136020).length < 2 ^ (prefixWord ++ tailWord_8136020).sum := by decide
  have hdescent : baseEnd_8136020 < baseStart_8136020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136090 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_8136090 : Nat := 118140960795 + 8136090 * 2 ^ 59
def prefixEnd_8136090 : Nat := 4983230072969 + 3 ^ 40 * 8136090 * 2
def baseEnd_8136090 : Nat := 1392574939413059248052603

theorem tailTrace_8136090 : CollatzResearch.WordTrace tailWord_8136090 prefixEnd_8136090 1392574939413059248052603 := by
  unfold tailWord_8136090
  simp only [CollatzResearch.WordTrace]
  refine ⟨74186895273585734597673431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197831720729561958927129149 74186895273585734597673431)
  ·
    refine ⟨111280342910378601896510147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74186895273585734597673431 111280342910378601896510147)
    ·
      refine ⟨166920514365567902844765221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111280342910378601896510147 166920514365567902844765221)
      ·
        refine ⟨31297596443543981783393479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166920514365567902844765221 31297596443543981783393479)
        ·
          refine ⟨46946394665315972675090219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31297596443543981783393479 46946394665315972675090219)
          ·
            refine ⟨70419591997973959012635329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46946394665315972675090219 70419591997973959012635329)
            ·
              refine ⟨52814693998480469259476497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70419591997973959012635329 52814693998480469259476497)
              ·
                refine ⟨39611020498860351944607373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52814693998480469259476497 39611020498860351944607373)
                ·
                  refine ⟨14854132687072631979227765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39611020498860351944607373 14854132687072631979227765)
                  ·
                    refine ⟨1392574939413059248052603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14854132687072631979227765 1392574939413059248052603)
                    ·
                      rfl

theorem cell23_8136090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_8136090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136090 prefixEnd_8136090 := by exact prefixLift 8136090
  have htrace : WordTrace (prefixWord ++ tailWord_8136090) baseStart_8136090 baseEnd_8136090 := by
    simpa [prefixWord, tailWord_8136090, baseEnd_8136090] using wordTrace_append hprefix tailTrace_8136090
  have hstable : (prefixWord ++ tailWord_8136090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136090).length < 2 ^ (prefixWord ++ tailWord_8136090).sum := by decide
  have hdescent : baseEnd_8136090 < baseStart_8136090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136094 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_8136094 : Nat := 118140960795 + 8136094 * 2 ^ 59
def prefixEnd_8136094 : Nat := 4983230072969 + 3 ^ 40 * 8136094 * 2
def baseEnd_8136094 : Nat := 464191874684643969834199

theorem tailTrace_8136094 : CollatzResearch.WordTrace tailWord_8136094 prefixEnd_8136094 464191874684643969834199 := by
  unfold tailWord_8136094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37093465873291055884229917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197831817990885631382559557 37093465873291055884229917)
  ·
    refine ⟨13910049702484145956586219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37093465873291055884229917 13910049702484145956586219)
    ·
      refine ⟨20865074553726218934879329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910049702484145956586219 20865074553726218934879329)
      ·
        refine ⟨15648805915294664201159497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20865074553726218934879329 15648805915294664201159497)
        ·
          refine ⟨11736604436470998150869623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15648805915294664201159497 11736604436470998150869623)
          ·
            refine ⟨17604906654706497226304435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11736604436470998150869623 17604906654706497226304435)
            ·
              refine ⟨26407359982059745839456653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17604906654706497226304435 26407359982059745839456653)
              ·
                refine ⟨9902759993272404689796245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26407359982059745839456653 9902759993272404689796245)
                ·
                  refine ⟨464191874684643969834199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9902759993272404689796245 464191874684643969834199)
                  ·
                    rfl

theorem cell23_8136094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_8136094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136094 prefixEnd_8136094 := by exact prefixLift 8136094
  have htrace : WordTrace (prefixWord ++ tailWord_8136094) baseStart_8136094 baseEnd_8136094 := by
    simpa [prefixWord, tailWord_8136094, baseEnd_8136094] using wordTrace_append hprefix tailTrace_8136094
  have hstable : (prefixWord ++ tailWord_8136094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136094).length < 2 ^ (prefixWord ++ tailWord_8136094).sum := by decide
  have hdescent : baseEnd_8136094 < baseStart_8136094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136120 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 6, 4]
def baseStart_8136120 : Nat := 118140960795 + 8136120 * 2 ^ 59
def prefixEnd_8136120 : Nat := 4983230072969 + 3 ^ 40 * 8136120 * 2
def baseEnd_8136120 : Nat := 1392580074219604208927557

theorem tailTrace_8136120 : CollatzResearch.WordTrace tailWord_8136120 prefixEnd_8136120 1392580074219604208927557 := by
  unfold tailWord_8136120
  simp only [CollatzResearch.WordTrace]
  refine ⟨148374337642117126757142907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197832450189489502342857209 148374337642117126757142907)
  ·
    refine ⟨222561506463175690135714361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148374337642117126757142907 222561506463175690135714361)
    ·
      refine ⟨166921129847381767601785771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222561506463175690135714361 166921129847381767601785771)
      ·
        refine ⟨250381694771072651402678657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166921129847381767601785771 250381694771072651402678657)
        ·
          refine ⟨187786271078304488552008993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250381694771072651402678657 187786271078304488552008993)
          ·
            refine ⟨140839703308728366414006745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187786271078304488552008993 140839703308728366414006745)
            ·
              refine ⟨105629777481546274810505059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140839703308728366414006745 105629777481546274810505059)
              ·
                refine ⟨158444666222319412215757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105629777481546274810505059 158444666222319412215757589)
                ·
                  refine ⟨7427093729171222447613637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158444666222319412215757589 7427093729171222447613637)
                  ·
                    refine ⟨1392580074219604208927557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7427093729171222447613637 1392580074219604208927557)
                    ·
                      rfl

theorem cell23_8136120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_8136120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136120 prefixEnd_8136120 := by exact prefixLift 8136120
  have htrace : WordTrace (prefixWord ++ tailWord_8136120) baseStart_8136120 baseEnd_8136120 := by
    simpa [prefixWord, tailWord_8136120, baseEnd_8136120] using wordTrace_append hprefix tailTrace_8136120
  have hstable : (prefixWord ++ tailWord_8136120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136120).length < 2 ^ (prefixWord ++ tailWord_8136120).sum := by decide
  have hdescent : baseEnd_8136120 < baseStart_8136120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136138 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_8136138 : Nat := 118140960795 + 8136138 * 2 ^ 59
def prefixEnd_8136138 : Nat := 4983230072969 + 3 ^ 40 * 8136138 * 2
def baseEnd_8136138 : Nat := 4177749465310593556357589

theorem tailTrace_8136138 : CollatzResearch.WordTrace tailWord_8136138 prefixEnd_8136138 4177749465310593556357589 := by
  unfold tailWord_8136138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74187332949542260647110267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197832887865446028392294045 74187332949542260647110267)
  ·
    refine ⟨111280999424313390970665401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74187332949542260647110267 111280999424313390970665401)
    ·
      refine ⟨83460749568235043227999051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111280999424313390970665401 83460749568235043227999051)
      ·
        refine ⟨125191124352352564841998577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83460749568235043227999051 125191124352352564841998577)
        ·
          refine ⟨93893343264264423631498933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125191124352352564841998577 93893343264264423631498933)
          ·
            refine ⟨8802500931024789715453025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93893343264264423631498933 8802500931024789715453025)
            ·
              refine ⟨6601875698268592286589769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802500931024789715453025 6601875698268592286589769)
              ·
                refine ⟨4951406773701444214942327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601875698268592286589769 4951406773701444214942327)
                ·
                  refine ⟨7427110160552166322413491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951406773701444214942327 7427110160552166322413491)
                  ·
                    refine ⟨11140665240828249483620237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7427110160552166322413491 11140665240828249483620237)
                    ·
                      refine ⟨4177749465310593556357589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140665240828249483620237 4177749465310593556357589)
                      ·
                        rfl

theorem cell23_8136138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_8136138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136138 prefixEnd_8136138 := by exact prefixLift 8136138
  have htrace : WordTrace (prefixWord ++ tailWord_8136138) baseStart_8136138 baseEnd_8136138 := by
    simpa [prefixWord, tailWord_8136138, baseEnd_8136138] using wordTrace_append hprefix tailTrace_8136138
  have hstable : (prefixWord ++ tailWord_8136138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136138).length < 2 ^ (prefixWord ++ tailWord_8136138).sum := by decide
  have hdescent : baseEnd_8136138 < baseStart_8136138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136157 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_8136157 : Nat := 118140960795 + 8136157 * 2 ^ 59
def prefixEnd_8136157 : Nat := 4983230072969 + 3 ^ 40 * 8136157 * 2
def baseEnd_8136157 : Nat := 4177759221443028982020001

theorem tailTrace_8136157 : CollatzResearch.WordTrace tailWord_8136157 prefixEnd_8136157 4177759221443028982020001 := by
  unfold tailWord_8136157
  simp only [CollatzResearch.WordTrace]
  refine ⟨296750024785100208833382725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197833349856733472555588483 296750024785100208833382725)
  ·
    refine ⟨55640629647206289156259261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296750024785100208833382725 55640629647206289156259261)
    ·
      refine ⟨20865236117702358433597223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55640629647206289156259261 20865236117702358433597223)
      ·
        refine ⟨31297854176553537650395835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20865236117702358433597223 31297854176553537650395835)
        ·
          refine ⟨46946781264830306475593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31297854176553537650395835 46946781264830306475593753)
          ·
            refine ⟨35210085948622729856695315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46946781264830306475593753 35210085948622729856695315)
            ·
              refine ⟨52815128922934094785042973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35210085948622729856695315 52815128922934094785042973)
              ·
                refine ⟨19805673346100285544391115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52815128922934094785042973 19805673346100285544391115)
                ·
                  refine ⟨29708510019150428316586673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19805673346100285544391115 29708510019150428316586673)
                  ·
                    refine ⟨22281382514362821237440005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29708510019150428316586673 22281382514362821237440005)
                    ·
                      refine ⟨4177759221443028982020001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22281382514362821237440005 4177759221443028982020001)
                      ·
                        rfl

theorem cell23_8136157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_8136157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136157 prefixEnd_8136157 := by exact prefixLift 8136157
  have htrace : WordTrace (prefixWord ++ tailWord_8136157) baseStart_8136157 baseEnd_8136157 := by
    simpa [prefixWord, tailWord_8136157, baseEnd_8136157] using wordTrace_append hprefix tailTrace_8136157
  have hstable : (prefixWord ++ tailWord_8136157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136157).length < 2 ^ (prefixWord ++ tailWord_8136157).sum := by decide
  have hdescent : baseEnd_8136157 < baseStart_8136157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136167 : List Nat := [1, 1, 5, 2, 1, 3, 3, 7]
def baseStart_8136167 : Nat := 118140960795 + 8136167 * 2 ^ 59
def prefixEnd_8136167 : Nat := 4983230072969 + 3 ^ 40 * 8136167 * 2
def baseEnd_8136167 : Nat := 154732013194428664551665

theorem tailTrace_8136167 : CollatzResearch.WordTrace tailWord_8136167 prefixEnd_8136167 154732013194428664551665 := by
  unfold tailWord_8136167
  simp only [CollatzResearch.WordTrace]
  refine ⟨296750389515063980541246755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197833593010042653694164503 296750389515063980541246755)
  ·
    refine ⟨445125584272595970811870133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296750389515063980541246755 445125584272595970811870133)
    ·
      refine ⟨41730523525555872263612825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 445125584272595970811870133 41730523525555872263612825)
      ·
        refine ⟨31297892644166904197709619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41730523525555872263612825 31297892644166904197709619)
        ·
          refine ⟨46946838966250356296564429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31297892644166904197709619 46946838966250356296564429)
          ·
            refine ⟨17605064612343883611211661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46946838966250356296564429 17605064612343883611211661)
            ·
              refine ⟨6601899229628956354204373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17605064612343883611211661 6601899229628956354204373)
              ·
                refine ⟨154732013194428664551665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6601899229628956354204373 154732013194428664551665)
                ·
                  rfl

theorem cell23_8136167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 7].length) (baseStart_8136167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136167 prefixEnd_8136167 := by exact prefixLift 8136167
  have htrace : WordTrace (prefixWord ++ tailWord_8136167) baseStart_8136167 baseEnd_8136167 := by
    simpa [prefixWord, tailWord_8136167, baseEnd_8136167] using wordTrace_append hprefix tailTrace_8136167
  have hstable : (prefixWord ++ tailWord_8136167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136167).length < 2 ^ (prefixWord ++ tailWord_8136167).sum := by decide
  have hdescent : baseEnd_8136167 < baseStart_8136167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136177 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_8136177 : Nat := 118140960795 + 8136177 * 2 ^ 59
def prefixEnd_8136177 : Nat := 4983230072969 + 3 ^ 40 * 8136177 * 2
def baseEnd_8136177 : Nat := 4177769491056118903769909

theorem tailTrace_8136177 : CollatzResearch.WordTrace tailWord_8136177 prefixEnd_8136177 4177769491056118903769909 := by
  unfold tailWord_8136177
  simp only [CollatzResearch.WordTrace]
  refine ⟨296750754245027752249110785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197833836163351834832740523 296750754245027752249110785)
  ·
    refine ⟨222563065683770814186833089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296750754245027752249110785 222563065683770814186833089)
    ·
      refine ⟨166922299262828110640124817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222563065683770814186833089 166922299262828110640124817)
      ·
        refine ⟨125191724447121082980093613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166922299262828110640124817 125191724447121082980093613)
        ·
          refine ⟨46946896667670406117535105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125191724447121082980093613 46946896667670406117535105)
          ·
            refine ⟨35210172500752804588151329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46946896667670406117535105 35210172500752804588151329)
            ·
              refine ⟨26407629375564603441113497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35210172500752804588151329 26407629375564603441113497)
              ·
                refine ⟨19805722031673452580835123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26407629375564603441113497 19805722031673452580835123)
                ·
                  refine ⟨29708583047510178871252685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19805722031673452580835123 29708583047510178871252685)
                  ·
                    refine ⟨11140718642816317076719757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29708583047510178871252685 11140718642816317076719757)
                    ·
                      refine ⟨4177769491056118903769909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140718642816317076719757 4177769491056118903769909)
                      ·
                        rfl

theorem cell23_8136177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_8136177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136177 prefixEnd_8136177 := by exact prefixLift 8136177
  have htrace : WordTrace (prefixWord ++ tailWord_8136177) baseStart_8136177 baseEnd_8136177 := by
    simpa [prefixWord, tailWord_8136177, baseEnd_8136177] using wordTrace_append hprefix tailTrace_8136177
  have hstable : (prefixWord ++ tailWord_8136177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136177).length < 2 ^ (prefixWord ++ tailWord_8136177).sum := by decide
  have hdescent : baseEnd_8136177 < baseStart_8136177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136178 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_8136178 : Nat := 118140960795 + 8136178 * 2 ^ 59
def prefixEnd_8136178 : Nat := 4983230072969 + 3 ^ 40 * 8136178 * 2
def baseEnd_8136178 : Nat := 4177770004536773399857405

theorem tailTrace_8136178 : CollatzResearch.WordTrace tailWord_8136178 prefixEnd_8136178 4177770004536773399857405 := by
  unfold tailWord_8136178
  simp only [CollatzResearch.WordTrace]
  refine ⟨74187697679506032354974297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197833860478682752946598125 74187697679506032354974297)
  ·
    refine ⟨55640773259629524266230723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74187697679506032354974297 55640773259629524266230723)
    ·
      refine ⟨83461159889444286399346085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55640773259629524266230723 83461159889444286399346085)
      ·
        refine ⟨15648967479270803699877391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83461159889444286399346085 15648967479270803699877391)
        ·
          refine ⟨23473451218906205549816087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15648967479270803699877391 23473451218906205549816087)
          ·
            refine ⟨35210176828359308324724131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23473451218906205549816087 35210176828359308324724131)
            ·
              refine ⟨52815265242538962487086197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35210176828359308324724131 52815265242538962487086197)
              ·
                refine ⟨4951431116488027733164331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52815265242538962487086197 4951431116488027733164331)
                ·
                  refine ⟨7427146674732041599746497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951431116488027733164331 7427146674732041599746497)
                  ·
                    refine ⟨5570360006049031199809873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7427146674732041599746497 5570360006049031199809873)
                    ·
                      refine ⟨4177770004536773399857405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570360006049031199809873 4177770004536773399857405)
                      ·
                        rfl

theorem cell23_8136178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_8136178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136178 prefixEnd_8136178 := by exact prefixLift 8136178
  have htrace : WordTrace (prefixWord ++ tailWord_8136178) baseStart_8136178 baseEnd_8136178 := by
    simpa [prefixWord, tailWord_8136178, baseEnd_8136178] using wordTrace_append hprefix tailTrace_8136178
  have hstable : (prefixWord ++ tailWord_8136178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136178).length < 2 ^ (prefixWord ++ tailWord_8136178).sum := by decide
  have hdescent : baseEnd_8136178 < baseStart_8136178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136181 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_8136181 : Nat := 118140960795 + 8136181 * 2 ^ 59
def prefixEnd_8136181 : Nat := 4983230072969 + 3 ^ 40 * 8136181 * 2
def baseEnd_8136181 : Nat := 4177771544978736888119891

theorem tailTrace_8136181 : CollatzResearch.WordTrace tailWord_8136181 prefixEnd_8136181 4177771544978736888119891 := by
  unfold tailWord_8136181
  simp only [CollatzResearch.WordTrace]
  refine ⟨296750900137013260932256397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197833933424675507288170931 296750900137013260932256397)
  ·
    refine ⟨111281587551379972849596149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296750900137013260932256397 111281587551379972849596149)
    ·
      refine ⟨10432648832941872454649639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111281587551379972849596149 10432648832941872454649639)
      ·
        refine ⟨15648973249412808681974459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432648832941872454649639 15648973249412808681974459)
        ·
          refine ⟨23473459874119213022961689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15648973249412808681974459 23473459874119213022961689)
          ·
            refine ⟨17605094905589409767221267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23473459874119213022961689 17605094905589409767221267)
            ·
              refine ⟨26407642358384114650831901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17605094905589409767221267 26407642358384114650831901)
              ·
                refine ⟨9902865884394042994061963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26407642358384114650831901 9902865884394042994061963)
                ·
                  refine ⟨14854298826591064491092945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9902865884394042994061963 14854298826591064491092945)
                  ·
                    refine ⟨11140724119943298368319709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14854298826591064491092945 11140724119943298368319709)
                    ·
                      refine ⟨4177771544978736888119891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140724119943298368319709 4177771544978736888119891)
                      ·
                        rfl

theorem cell23_8136181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_8136181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136181 prefixEnd_8136181 := by exact prefixLift 8136181
  have htrace : WordTrace (prefixWord ++ tailWord_8136181) baseStart_8136181 baseEnd_8136181 := by
    simpa [prefixWord, tailWord_8136181, baseEnd_8136181] using wordTrace_append hprefix tailTrace_8136181
  have hstable : (prefixWord ++ tailWord_8136181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136181).length < 2 ^ (prefixWord ++ tailWord_8136181).sum := by decide
  have hdescent : baseEnd_8136181 < baseStart_8136181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136198 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_8136198 : Nat := 118140960795 + 8136198 * 2 ^ 59
def prefixEnd_8136198 : Nat := 4983230072969 + 3 ^ 40 * 8136198 * 2
def baseEnd_8136198 : Nat := 4177780274149863321607313

theorem tailTrace_8136198 : CollatzResearch.WordTrace tailWord_8136198 prefixEnd_8136198 4177780274149863321607313 := by
  unfold tailWord_8136198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273485005560989776113289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197834346785301115223750165 9273485005560989776113289)
  ·
    refine ⟨6955113754170742332084967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9273485005560989776113289 6955113754170742332084967)
    ·
      refine ⟨10432670631256113498127451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955113754170742332084967 10432670631256113498127451)
      ·
        refine ⟨15649005946884170247191177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432670631256113498127451 15649005946884170247191177)
        ·
          refine ⟨11736754460163127685393383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15649005946884170247191177 11736754460163127685393383)
          ·
            refine ⟨17605131690244691528090075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11736754460163127685393383 17605131690244691528090075)
            ·
              refine ⟨26407697535367037292135113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17605131690244691528090075 26407697535367037292135113)
              ·
                refine ⟨19805773151525277969101335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26407697535367037292135113 19805773151525277969101335)
                ·
                  refine ⟨29708659727287916953652003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19805773151525277969101335 29708659727287916953652003)
                  ·
                    refine ⟨44562989590931875430478005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29708659727287916953652003 44562989590931875430478005)
                    ·
                      refine ⟨4177780274149863321607313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44562989590931875430478005 4177780274149863321607313)
                      ·
                        rfl

theorem cell23_8136198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_8136198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136198 prefixEnd_8136198 := by exact prefixLift 8136198
  have htrace : WordTrace (prefixWord ++ tailWord_8136198) baseStart_8136198 baseEnd_8136198 := by
    simpa [prefixWord, tailWord_8136198, baseEnd_8136198] using wordTrace_append hprefix tailTrace_8136198
  have hstable : (prefixWord ++ tailWord_8136198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136198).length < 2 ^ (prefixWord ++ tailWord_8136198).sum := by decide
  have hdescent : baseEnd_8136198 < baseStart_8136198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136200 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_8136200 : Nat := 118140960795 + 8136200 * 2 ^ 59
def prefixEnd_8136200 : Nat := 4983230072969 + 3 ^ 40 * 8136200 * 2
def baseEnd_8136200 : Nat := 4177781301111172313782303

theorem tailTrace_8136200 : CollatzResearch.WordTrace tailWord_8136200 prefixEnd_8136200 4177781301111172313782303 := by
  unfold tailWord_8136200
  simp only [CollatzResearch.WordTrace]
  refine ⟨148375796561972213588599027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197834395415962951451465369 148375796561972213588599027)
  ·
    refine ⟨222563694842958320382898541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148375796561972213588599027 222563694842958320382898541)
    ·
      refine ⟨83461385566109370143586953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222563694842958320382898541 83461385566109370143586953)
      ·
        refine ⟨62596039174582027607690215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83461385566109370143586953 62596039174582027607690215)
        ·
          refine ⟨93894058761873041411535323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62596039174582027607690215 93894058761873041411535323)
          ·
            refine ⟨140841088142809562117302985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93894058761873041411535323 140841088142809562117302985)
            ·
              refine ⟨105630816107107171587977239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140841088142809562117302985 105630816107107171587977239)
              ·
                refine ⟨158446224160660757381965859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105630816107107171587977239 158446224160660757381965859)
                ·
                  refine ⟨237669336240991136072948789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158446224160660757381965859 237669336240991136072948789)
                  ·
                    refine ⟨22281500272592919006838949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237669336240991136072948789 22281500272592919006838949)
                    ·
                      refine ⟨4177781301111172313782303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22281500272592919006838949 4177781301111172313782303)
                      ·
                        rfl

theorem cell23_8136200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_8136200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136200 prefixEnd_8136200 := by exact prefixLift 8136200
  have htrace : WordTrace (prefixWord ++ tailWord_8136200) baseStart_8136200 baseEnd_8136200 := by
    simpa [prefixWord, tailWord_8136200, baseEnd_8136200] using wordTrace_append hprefix tailTrace_8136200
  have hstable : (prefixWord ++ tailWord_8136200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136200).length < 2 ^ (prefixWord ++ tailWord_8136200).sum := by decide
  have hdescent : baseEnd_8136200 < baseStart_8136200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136205 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_8136205 : Nat := 118140960795 + 8136205 * 2 ^ 59
def prefixEnd_8136205 : Nat := 4983230072969 + 3 ^ 40 * 8136205 * 2
def baseEnd_8136205 : Nat := 1392594622838148264739927

theorem tailTrace_8136205 : CollatzResearch.WordTrace tailWord_8136205 prefixEnd_8136205 1392594622838148264739927 := by
  unfold tailWord_8136205
  simp only [CollatzResearch.WordTrace]
  refine ⟨296751775488926313031130069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197834516992617542020753379 296751775488926313031130069)
  ·
    refine ⟨6955119738021710461667111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 296751775488926313031130069 6955119738021710461667111)
    ·
      refine ⟨10432679607032565692500667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955119738021710461667111 10432679607032565692500667)
      ·
        refine ⟨15649019410548848538751001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432679607032565692500667 15649019410548848538751001)
        ·
          refine ⟨11736764557911636404063251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15649019410548848538751001 11736764557911636404063251)
          ·
            refine ⟨17605146836867454606094877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11736764557911636404063251 17605146836867454606094877)
            ·
              refine ⟨6601930063825295477285579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17605146836867454606094877 6601930063825295477285579)
              ·
                refine ⟨9902895095737943215928369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601930063825295477285579 9902895095737943215928369)
                ·
                  refine ⟨7427171321803457411946277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902895095737943215928369 7427171321803457411946277)
                  ·
                    refine ⟨1392594622838148264739927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7427171321803457411946277 1392594622838148264739927)
                    ·
                      rfl

theorem cell23_8136205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_8136205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136205 prefixEnd_8136205 := by exact prefixLift 8136205
  have htrace : WordTrace (prefixWord ++ tailWord_8136205) baseStart_8136205 baseEnd_8136205 := by
    simpa [prefixWord, tailWord_8136205, baseEnd_8136205] using wordTrace_append hprefix tailTrace_8136205
  have hstable : (prefixWord ++ tailWord_8136205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136205).length < 2 ^ (prefixWord ++ tailWord_8136205).sum := by decide
  have hdescent : baseEnd_8136205 < baseStart_8136205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136211 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 2, 1, 3]
def baseStart_8136211 : Nat := 118140960795 + 8136211 * 2 ^ 59
def prefixEnd_8136211 : Nat := 4983230072969 + 3 ^ 40 * 8136211 * 2
def baseEnd_8136211 : Nat := 4177786949398371770744753

theorem tailTrace_8136211 : CollatzResearch.WordTrace tailWord_8136211 prefixEnd_8136211 4177786949398371770744753 := by
  unfold tailWord_8136211
  simp only [CollatzResearch.WordTrace]
  refine ⟨296751994326904576055848487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197834662884603050703898991 296751994326904576055848487)
  ·
    refine ⟨445127991490356864083772731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296751994326904576055848487 445127991490356864083772731)
    ·
      refine ⟨667691987235535296125659097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445127991490356864083772731 667691987235535296125659097)
      ·
        refine ⟨500768990426651472094244323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667691987235535296125659097 500768990426651472094244323)
        ·
          refine ⟨751153485639977208141366485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500768990426651472094244323 751153485639977208141366485)
          ·
            refine ⟨17605159819686965815813277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 751153485639977208141366485 17605159819686965815813277)
            ·
              refine ⟨6601934932382612180929979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17605159819686965815813277 6601934932382612180929979)
              ·
                refine ⟨9902902398573918271394969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601934932382612180929979 9902902398573918271394969)
                ·
                  refine ⟨7427176798930438703546227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902902398573918271394969 7427176798930438703546227)
                  ·
                    refine ⟨11140765198395658055319341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7427176798930438703546227 11140765198395658055319341)
                    ·
                      refine ⟨4177786949398371770744753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140765198395658055319341 4177786949398371770744753)
                      ·
                        rfl

theorem cell23_8136211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 1, 3].length) (baseStart_8136211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136211 prefixEnd_8136211 := by exact prefixLift 8136211
  have htrace : WordTrace (prefixWord ++ tailWord_8136211) baseStart_8136211 baseEnd_8136211 := by
    simpa [prefixWord, tailWord_8136211, baseEnd_8136211] using wordTrace_append hprefix tailTrace_8136211
  have hstable : (prefixWord ++ tailWord_8136211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136211).length < 2 ^ (prefixWord ++ tailWord_8136211).sum := by decide
  have hdescent : baseEnd_8136211 < baseStart_8136211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136221 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_8136221 : Nat := 118140960795 + 8136221 * 2 ^ 59
def prefixEnd_8136221 : Nat := 4983230072969 + 3 ^ 40 * 8136221 * 2
def baseEnd_8136221 : Nat := 4177792084204916731619707

theorem tailTrace_8136221 : CollatzResearch.WordTrace tailWord_8136221 prefixEnd_8136221 4177792084204916731619707 := by
  unfold tailWord_8136221
  simp only [CollatzResearch.WordTrace]
  refine ⟨296752359056868347763712517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197834906037912231842475011 296752359056868347763712517)
  ·
    refine ⟨55641067323162815205696097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296752359056868347763712517 55641067323162815205696097)
    ·
      refine ⟨41730800492372111404272073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55641067323162815205696097 41730800492372111404272073)
      ·
        refine ⟨31298100369279083553204055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41730800492372111404272073 31298100369279083553204055)
        ·
          refine ⟨46947150553918625329806083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31298100369279083553204055 46947150553918625329806083)
          ·
            refine ⟨70420725830877937994709125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46947150553918625329806083 70420725830877937994709125)
            ·
              refine ⟨13203886093289613374007961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70420725830877937994709125 13203886093289613374007961)
              ·
                refine ⟨9902914569967210030505971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13203886093289613374007961 9902914569967210030505971)
                ·
                  refine ⟨14854371854950815045758957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9902914569967210030505971 14854371854950815045758957)
                  ·
                    refine ⟨5570389445606555642159609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14854371854950815045758957 5570389445606555642159609)
                    ·
                      refine ⟨4177792084204916731619707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570389445606555642159609 4177792084204916731619707)
                      ·
                        rfl

theorem cell23_8136221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_8136221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136221 prefixEnd_8136221 := by exact prefixLift 8136221
  have htrace : WordTrace (prefixWord ++ tailWord_8136221) baseStart_8136221 baseEnd_8136221 := by
    simpa [prefixWord, tailWord_8136221, baseEnd_8136221] using wordTrace_append hprefix tailTrace_8136221
  have hstable : (prefixWord ++ tailWord_8136221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136221).length < 2 ^ (prefixWord ++ tailWord_8136221).sum := by decide
  have hdescent : baseEnd_8136221 < baseStart_8136221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136234 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_8136234 : Nat := 118140960795 + 8136234 * 2 ^ 59
def prefixEnd_8136234 : Nat := 4983230072969 + 3 ^ 40 * 8136234 * 2
def baseEnd_8136234 : Nat := 4177798759453425180757147

theorem tailTrace_8136234 : CollatzResearch.WordTrace tailWord_8136234 prefixEnd_8136234 4177798759453425180757147 := by
  unfold tailWord_8136234
  simp only [CollatzResearch.WordTrace]
  refine ⟨74188208301455312745983939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197835222137214167322623837 74188208301455312745983939)
  ·
    refine ⟨111282312452182969118975909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74188208301455312745983939 111282312452182969118975909)
    ·
      refine ⟨20865433584784306709807983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111282312452182969118975909 20865433584784306709807983)
      ·
        refine ⟨31298150377176460064711975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20865433584784306709807983 31298150377176460064711975)
        ·
          refine ⟨46947225565764690097067963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31298150377176460064711975 46947225565764690097067963)
          ·
            refine ⟨70420838348647035145601945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46947225565764690097067963 70420838348647035145601945)
            ·
              refine ⟨52815628761485276359201459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70420838348647035145601945 52815628761485276359201459)
              ·
                refine ⟨79223443142227914538802189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52815628761485276359201459 79223443142227914538802189)
                ·
                  refine ⟨29708791178335467952050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79223443142227914538802189 29708791178335467952050821)
                  ·
                    refine ⟨5570398345937900241009529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29708791178335467952050821 5570398345937900241009529)
                    ·
                      refine ⟨4177798759453425180757147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570398345937900241009529 4177798759453425180757147)
                      ·
                        rfl

theorem cell23_8136234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_8136234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136234 prefixEnd_8136234 := by exact prefixLift 8136234
  have htrace : WordTrace (prefixWord ++ tailWord_8136234) baseStart_8136234 baseEnd_8136234 := by
    simpa [prefixWord, tailWord_8136234, baseEnd_8136234] using wordTrace_append hprefix tailTrace_8136234
  have hstable : (prefixWord ++ tailWord_8136234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136234).length < 2 ^ (prefixWord ++ tailWord_8136234).sum := by decide
  have hdescent : baseEnd_8136234 < baseStart_8136234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136250 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_8136250 : Nat := 118140960795 + 8136250 * 2 ^ 59
def prefixEnd_8136250 : Nat := 4983230072969 + 3 ^ 40 * 8136250 * 2
def baseEnd_8136250 : Nat := 4177806975143897118157073

theorem tailTrace_8136250 : CollatzResearch.WordTrace tailWord_8136250 prefixEnd_8136250 4177806975143897118157073 := by
  unfold tailWord_8136250
  simp only [CollatzResearch.WordTrace]
  refine ⟨74188354193440821429129551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197835611182508857144345469 74188354193440821429129551)
  ·
    refine ⟨111282531290161232143694327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74188354193440821429129551 111282531290161232143694327)
    ·
      refine ⟨166923796935241848215541491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111282531290161232143694327 166923796935241848215541491)
      ·
        refine ⟨250385695402862772323312237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166923796935241848215541491 250385695402862772323312237)
        ·
          refine ⟨93894635776073539621242089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250385695402862772323312237 93894635776073539621242089)
          ·
            refine ⟨70420976832055154715931567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93894635776073539621242089 70420976832055154715931567)
            ·
              refine ⟨105631465248082732073897351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70420976832055154715931567 105631465248082732073897351)
              ·
                refine ⟨158447197872124098110846027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105631465248082732073897351 158447197872124098110846027)
                ·
                  refine ⟨237670796808186147166269041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158447197872124098110846027 237670796808186147166269041)
                  ·
                    refine ⟨178253097606139610374701781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237670796808186147166269041 178253097606139610374701781)
                    ·
                      refine ⟨4177806975143897118157073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178253097606139610374701781 4177806975143897118157073)
                      ·
                        rfl

theorem cell23_8136250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_8136250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136250 prefixEnd_8136250 := by exact prefixLift 8136250
  have htrace : WordTrace (prefixWord ++ tailWord_8136250) baseStart_8136250 baseEnd_8136250 := by
    simpa [prefixWord, tailWord_8136250, baseEnd_8136250] using wordTrace_append hprefix tailTrace_8136250
  have hstable : (prefixWord ++ tailWord_8136250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136250).length < 2 ^ (prefixWord ++ tailWord_8136250).sum := by decide
  have hdescent : baseEnd_8136250 < baseStart_8136250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136262 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_8136262 : Nat := 118140960795 + 8136262 * 2 ^ 59
def prefixEnd_8136262 : Nat := 4983230072969 + 3 ^ 40 * 8136262 * 2
def baseEnd_8136262 : Nat := 4177813136911751071207019

theorem tailTrace_8136262 : CollatzResearch.WordTrace tailWord_8136262 prefixEnd_8136262 4177813136911751071207019 := by
  unfold tailWord_8136262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273557951553744117686095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197835902966479874510636693 9273557951553744117686095)
  ·
    refine ⟨13910336927330616176529143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9273557951553744117686095 13910336927330616176529143)
    ·
      refine ⟨20865505390995924264793715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910336927330616176529143 20865505390995924264793715)
      ·
        refine ⟨31298258086493886397190573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20865505390995924264793715 31298258086493886397190573)
        ·
          refine ⟨11736846782435207398946465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31298258086493886397190573 11736846782435207398946465)
          ·
            refine ⟨8802635086826405549209849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11736846782435207398946465 8802635086826405549209849)
            ·
              refine ⟨6601976315119804161907387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802635086826405549209849 6601976315119804161907387)
              ·
                refine ⟨9902964472679706242861081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601976315119804161907387 9902964472679706242861081)
                ·
                  refine ⟨7427223354509779682145811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902964472679706242861081 7427223354509779682145811)
                  ·
                    refine ⟨11140835031764669523218717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7427223354509779682145811 11140835031764669523218717)
                    ·
                      refine ⟨4177813136911751071207019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140835031764669523218717 4177813136911751071207019)
                      ·
                        rfl

theorem cell23_8136262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_8136262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136262 prefixEnd_8136262 := by exact prefixLift 8136262
  have htrace : WordTrace (prefixWord ++ tailWord_8136262) baseStart_8136262 baseEnd_8136262 := by
    simpa [prefixWord, tailWord_8136262, baseEnd_8136262] using wordTrace_append hprefix tailTrace_8136262
  have hstable : (prefixWord ++ tailWord_8136262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136262).length < 2 ^ (prefixWord ++ tailWord_8136262).sum := by decide
  have hdescent : baseEnd_8136262 < baseStart_8136262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136268 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 2, 2, 2]
def baseStart_8136268 : Nat := 118140960795 + 8136268 * 2 ^ 59
def prefixEnd_8136268 : Nat := 4983230072969 + 3 ^ 40 * 8136268 * 2
def baseEnd_8136268 : Nat := 4177816217795678047731991

theorem tailTrace_8136268 : CollatzResearch.WordTrace tailWord_8136268 prefixEnd_8136268 4177816217795678047731991 := by
  unfold tailWord_8136268
  simp only [CollatzResearch.WordTrace]
  refine ⟨148377036643849037395336729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197836048858465383193782305 148377036643849037395336729)
  ·
    refine ⟨111282777482886778046502547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148377036643849037395336729 111282777482886778046502547)
    ·
      refine ⟨166924166224330167069753821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111282777482886778046502547 166924166224330167069753821)
      ·
        refine ⟨62596562334123812651157683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166924166224330167069753821 62596562334123812651157683)
        ·
          refine ⟨93894843501185718976736525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62596562334123812651157683 93894843501185718976736525)
          ·
            refine ⟨35210566312944644616276197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93894843501185718976736525 35210566312944644616276197)
            ·
              refine ⟨6601981183677120865551787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35210566312944644616276197 6601981183677120865551787)
              ·
                refine ⟨9902971775515681298327681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601981183677120865551787 9902971775515681298327681)
                ·
                  refine ⟨7427228831636760973745761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902971775515681298327681 7427228831636760973745761)
                  ·
                    refine ⟨5570421623727570730309321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7427228831636760973745761 5570421623727570730309321)
                    ·
                      refine ⟨4177816217795678047731991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570421623727570730309321 4177816217795678047731991)
                      ·
                        rfl

theorem cell23_8136268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_8136268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136268 prefixEnd_8136268 := by exact prefixLift 8136268
  have htrace : WordTrace (prefixWord ++ tailWord_8136268) baseStart_8136268 baseEnd_8136268 := by
    simpa [prefixWord, tailWord_8136268, baseEnd_8136268] using wordTrace_append hprefix tailTrace_8136268
  have hstable : (prefixWord ++ tailWord_8136268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136268).length < 2 ^ (prefixWord ++ tailWord_8136268).sum := by decide
  have hdescent : baseEnd_8136268 < baseStart_8136268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136280 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_8136280 : Nat := 118140960795 + 8136280 * 2 ^ 59
def prefixEnd_8136280 : Nat := 4983230072969 + 3 ^ 40 * 8136280 * 2
def baseEnd_8136280 : Nat := 4177822379563532000781935

theorem tailTrace_8136280 : CollatzResearch.WordTrace tailWord_8136280 prefixEnd_8136280 4177822379563532000781935 := by
  unfold tailWord_8136280
  simp only [CollatzResearch.WordTrace]
  refine ⟨148377255481827300420055147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197836340642436400560073529 148377255481827300420055147)
  ·
    refine ⟨222565883222740950630082721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148377255481827300420055147 222565883222740950630082721)
    ·
      refine ⟨166924412417055712972562041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222565883222740950630082721 166924412417055712972562041)
      ·
        refine ⟨125193309312791784729421531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166924412417055712972562041 125193309312791784729421531)
        ·
          refine ⟨187789963969187677094132297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125193309312791784729421531 187789963969187677094132297)
          ·
            refine ⟨140842472976890757820599223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187789963969187677094132297 140842472976890757820599223)
            ·
              refine ⟨211263709465336136730898835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140842472976890757820599223 211263709465336136730898835)
              ·
                refine ⟨316895564198004205096348253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211263709465336136730898835 316895564198004205096348253)
                ·
                  refine ⟨118835836574251576911130595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316895564198004205096348253 118835836574251576911130595)
                  ·
                    refine ⟨178253754861377365366695893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118835836574251576911130595 178253754861377365366695893)
                    ·
                      refine ⟨4177822379563532000781935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178253754861377365366695893 4177822379563532000781935)
                      ·
                        rfl

theorem cell23_8136280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_8136280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136280 prefixEnd_8136280 := by exact prefixLift 8136280
  have htrace : WordTrace (prefixWord ++ tailWord_8136280) baseStart_8136280 baseEnd_8136280 := by
    simpa [prefixWord, tailWord_8136280, baseEnd_8136280] using wordTrace_append hprefix tailTrace_8136280
  have hstable : (prefixWord ++ tailWord_8136280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136280).length < 2 ^ (prefixWord ++ tailWord_8136280).sum := by decide
  have hdescent : baseEnd_8136280 < baseStart_8136280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136334 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_8136334 : Nat := 118140960795 + 8136334 * 2 ^ 59
def prefixEnd_8136334 : Nat := 4983230072969 + 3 ^ 40 * 8136334 * 2
def baseEnd_8136334 : Nat := 1392616702506291596502229

theorem tailTrace_8136334 : CollatzResearch.WordTrace tailWord_8136334 prefixEnd_8136334 1392616702506291596502229 := by
  unfold tailWord_8136334
  simp only [CollatzResearch.WordTrace]
  refine ⟨37094560063182371007822007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197837653670305978708384037 37094560063182371007822007)
  ·
    refine ⟨55641840094773556511733011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37094560063182371007822007 55641840094773556511733011)
    ·
      refine ⟨83462760142160334767599517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55641840094773556511733011 83462760142160334767599517)
      ·
        refine ⟨31298535053310125537849819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83462760142160334767599517 31298535053310125537849819)
        ·
          refine ⟨46947802579965188306774729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31298535053310125537849819 46947802579965188306774729)
          ·
            refine ⟨35210851934973891230081047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46947802579965188306774729 35210851934973891230081047)
            ·
              refine ⟨52816277902460836845121571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35210851934973891230081047 52816277902460836845121571)
              ·
                refine ⟨79224416853691255267682357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52816277902460836845121571 79224416853691255267682357)
                ·
                  refine ⟨7427289080033555181345221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79224416853691255267682357 7427289080033555181345221)
                  ·
                    refine ⟨1392616702506291596502229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7427289080033555181345221 1392616702506291596502229)
                    ·
                      rfl

theorem cell23_8136334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_8136334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136334 prefixEnd_8136334 := by exact prefixLift 8136334
  have htrace : WordTrace (prefixWord ++ tailWord_8136334) baseStart_8136334 baseEnd_8136334 := by
    simpa [prefixWord, tailWord_8136334, baseEnd_8136334] using wordTrace_append hprefix tailTrace_8136334
  have hstable : (prefixWord ++ tailWord_8136334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136334).length < 2 ^ (prefixWord ++ tailWord_8136334).sum := by decide
  have hdescent : baseEnd_8136334 < baseStart_8136334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136338 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_8136338 : Nat := 118140960795 + 8136338 * 2 ^ 59
def prefixEnd_8136338 : Nat := 4983230072969 + 3 ^ 40 * 8136338 * 2
def baseEnd_8136338 : Nat := 1392617387147164257952223

theorem tailTrace_8136338 : CollatzResearch.WordTrace tailWord_8136338 prefixEnd_8136338 1392617387147164257952223 := by
  unfold tailWord_8136338
  simp only [CollatzResearch.WordTrace]
  refine ⟨74189156599361119186430417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197837750931629651163814445 74189156599361119186430417)
  ·
    refine ⟨55641867449520839389822813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74189156599361119186430417 55641867449520839389822813)
    ·
      refine ⟨20865700293570314771183555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55641867449520839389822813 20865700293570314771183555)
      ·
        refine ⟨31298550440355472156775333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20865700293570314771183555 31298550440355472156775333)
        ·
          refine ⟨5868478207566651029395375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31298550440355472156775333 5868478207566651029395375)
          ·
            refine ⟨8802717311349976544093063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868478207566651029395375 8802717311349976544093063)
            ·
              refine ⟨13204075967024964816139595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8802717311349976544093063 13204075967024964816139595)
              ·
                refine ⟨19806113950537447224209393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13204075967024964816139595 19806113950537447224209393)
                ·
                  refine ⟨14854585462903085418157045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19806113950537447224209393 14854585462903085418157045)
                  ·
                    refine ⟨1392617387147164257952223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14854585462903085418157045 1392617387147164257952223)
                    ·
                      rfl

theorem cell23_8136338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_8136338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136338 prefixEnd_8136338 := by exact prefixLift 8136338
  have htrace : WordTrace (prefixWord ++ tailWord_8136338) baseStart_8136338 baseEnd_8136338 := by
    simpa [prefixWord, tailWord_8136338, baseEnd_8136338] using wordTrace_append hprefix tailTrace_8136338
  have hstable : (prefixWord ++ tailWord_8136338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136338).length < 2 ^ (prefixWord ++ tailWord_8136338).sum := by decide
  have hdescent : baseEnd_8136338 < baseStart_8136338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136344 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_8136344 : Nat := 118140960795 + 8136344 * 2 ^ 59
def prefixEnd_8136344 : Nat := 4983230072969 + 3 ^ 40 * 8136344 * 2
def baseEnd_8136344 : Nat := 4177855242325419750381641

theorem tailTrace_8136344 : CollatzResearch.WordTrace tailWord_8136344 prefixEnd_8136344 4177855242325419750381641 := by
  unfold tailWord_8136344
  simp only [CollatzResearch.WordTrace]
  refine ⟨148378422617711369885220043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197837896823615159846960057 148378422617711369885220043)
  ·
    refine ⟨222567633926567054827830065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148378422617711369885220043 222567633926567054827830065)
    ·
      refine ⟨166925725444925291120872549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222567633926567054827830065 166925725444925291120872549)
      ·
        refine ⟨31298573520923492085163603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166925725444925291120872549 31298573520923492085163603)
        ·
          refine ⟨46947860281385238127745405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31298573520923492085163603 46947860281385238127745405)
          ·
            refine ⟨17605447605519464297904527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46947860281385238127745405 17605447605519464297904527)
            ·
              refine ⟨26408171408279196446856791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17605447605519464297904527 26408171408279196446856791)
              ·
                refine ⟨39612257112418794670285187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26408171408279196446856791 39612257112418794670285187)
                ·
                  refine ⟨59418385668628192005427781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39612257112418794670285187 59418385668628192005427781)
                  ·
                    refine ⟨11140947312867786001017709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59418385668628192005427781 11140947312867786001017709)
                    ·
                      refine ⟨4177855242325419750381641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11140947312867786001017709 4177855242325419750381641)
                      ·
                        rfl

theorem cell23_8136344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_8136344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136344 prefixEnd_8136344 := by exact prefixLift 8136344
  have htrace : WordTrace (prefixWord ++ tailWord_8136344) baseStart_8136344 baseEnd_8136344 := by
    simpa [prefixWord, tailWord_8136344, baseEnd_8136344] using wordTrace_append hprefix tailTrace_8136344
  have hstable : (prefixWord ++ tailWord_8136344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136344).length < 2 ^ (prefixWord ++ tailWord_8136344).sum := by decide
  have hdescent : baseEnd_8136344 < baseStart_8136344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136377 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_8136377 : Nat := 118140960795 + 8136377 * 2 ^ 59
def prefixEnd_8136377 : Nat := 4983230072969 + 3 ^ 40 * 8136377 * 2
def baseEnd_8136377 : Nat := 1392624062395672707089663

theorem tailTrace_8136377 : CollatzResearch.WordTrace tailWord_8136377 prefixEnd_8136377 1392624062395672707089663 := by
  unfold tailWord_8136377
  simp only [CollatzResearch.WordTrace]
  refine ⟨296758048844303186406391385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197838699229535457604260923 296758048844303186406391385)
  ·
    refine ⟨222568536633227389804793539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296758048844303186406391385 222568536633227389804793539)
    ·
      refine ⟨333852804949841084707190309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222568536633227389804793539 333852804949841084707190309)
      ·
        refine ⟨62597400928095203382598183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333852804949841084707190309 62597400928095203382598183)
        ·
          refine ⟨93896101392142805073897275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62597400928095203382598183 93896101392142805073897275)
          ·
            refine ⟨140844152088214207610845913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93896101392142805073897275 140844152088214207610845913)
            ·
              refine ⟨105633114066160655708134435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140844152088214207610845913 105633114066160655708134435)
              ·
                refine ⟨158449671099240983562201653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105633114066160655708134435 158449671099240983562201653)
                ·
                  refine ⟨14854656665553842208956405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158449671099240983562201653 14854656665553842208956405)
                  ·
                    refine ⟨1392624062395672707089663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14854656665553842208956405 1392624062395672707089663)
                    ·
                      rfl

theorem cell23_8136377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_8136377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136377 prefixEnd_8136377 := by exact prefixLift 8136377
  have htrace : WordTrace (prefixWord ++ tailWord_8136377) baseStart_8136377 baseEnd_8136377 := by
    simpa [prefixWord, tailWord_8136377, baseEnd_8136377] using wordTrace_append hprefix tailTrace_8136377
  have hstable : (prefixWord ++ tailWord_8136377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136377).length < 2 ^ (prefixWord ++ tailWord_8136377).sum := by decide
  have hdescent : baseEnd_8136377 < baseStart_8136377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136384 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 3, 5, 2]
def baseStart_8136384 : Nat := 118140960795 + 8136384 * 2 ^ 59
def prefixEnd_8136384 : Nat := 4983230072969 + 3 ^ 40 * 8136384 * 2
def baseEnd_8136384 : Nat := 4177875781551599593881457

theorem tailTrace_8136384 : CollatzResearch.WordTrace tailWord_8136384 prefixEnd_8136384 4177875781551599593881457 := by
  unfold tailWord_8136384
  simp only [CollatzResearch.WordTrace]
  refine ⟨148379152077638913300948103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197838869436851884401264137 148379152077638913300948103)
  ·
    refine ⟨222568728116458369951422155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148379152077638913300948103 222568728116458369951422155)
    ·
      refine ⟨333853092174687554927133233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222568728116458369951422155 333853092174687554927133233)
      ·
        refine ⟨250389819131015666195349925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333853092174687554927133233 250389819131015666195349925)
        ·
          refine ⟨46948091087065437411628111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250389819131015666195349925 46948091087065437411628111)
          ·
            refine ⟨70422136630598156117442167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46948091087065437411628111 70422136630598156117442167)
            ·
              refine ⟨105633204945897234176163251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70422136630598156117442167 105633204945897234176163251)
              ·
                refine ⟨158449807418845851264244877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105633204945897234176163251 158449807418845851264244877)
                ·
                  refine ⟨59418677782067194224091829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158449807418845851264244877 59418677782067194224091829)
                  ·
                    refine ⟨5570501042068799458508609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59418677782067194224091829 5570501042068799458508609)
                    ·
                      refine ⟨4177875781551599593881457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570501042068799458508609 4177875781551599593881457)
                      ·
                        rfl

theorem cell23_8136384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_8136384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136384 prefixEnd_8136384 := by exact prefixLift 8136384
  have htrace : WordTrace (prefixWord ++ tailWord_8136384) baseStart_8136384 baseEnd_8136384 := by
    simpa [prefixWord, tailWord_8136384, baseEnd_8136384] using wordTrace_append hprefix tailTrace_8136384
  have hstable : (prefixWord ++ tailWord_8136384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136384).length < 2 ^ (prefixWord ++ tailWord_8136384).sum := by decide
  have hdescent : baseEnd_8136384 < baseStart_8136384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136407 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 3, 6]
def baseStart_8136407 : Nat := 118140960795 + 8136407 * 2 ^ 59
def prefixEnd_8136407 : Nat := 4983230072969 + 3 ^ 40 * 8136407 * 2
def baseEnd_8136407 : Nat := 1392629197202217667964617

theorem tailTrace_8136407 : CollatzResearch.WordTrace tailWord_8136407 prefixEnd_8136407 1392629197202217667964617 := by
  unfold tailWord_8136407
  simp only [CollatzResearch.WordTrace]
  refine ⟨296759143034194501529983475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197839428689463001019988983 296759143034194501529983475)
  ·
    refine ⟨445138714551291752294975213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296759143034194501529983475 445138714551291752294975213)
    ·
      refine ⟨166927017956734407110615705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445138714551291752294975213 166927017956734407110615705)
      ·
        refine ⟨125195263467550805332961779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166927017956734407110615705 125195263467550805332961779)
        ·
          refine ⟨187792895201326207999442669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125195263467550805332961779 187792895201326207999442669)
          ·
            refine ⟨70422335700497327999791001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187792895201326207999442669 70422335700497327999791001)
            ·
              refine ⟨52816751775372995999843251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70422335700497327999791001 52816751775372995999843251)
              ·
                refine ⟨79225127663059493999764877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52816751775372995999843251 79225127663059493999764877)
                ·
                  refine ⟨29709422873647310249911829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79225127663059493999764877 29709422873647310249911829)
                  ·
                    refine ⟨1392629197202217667964617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29709422873647310249911829 1392629197202217667964617)
                    ·
                      rfl

theorem cell23_8136407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_8136407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136407 prefixEnd_8136407 := by exact prefixLift 8136407
  have htrace : WordTrace (prefixWord ++ tailWord_8136407) baseStart_8136407 baseEnd_8136407 := by
    simpa [prefixWord, tailWord_8136407, baseEnd_8136407] using wordTrace_append hprefix tailTrace_8136407
  have hstable : (prefixWord ++ tailWord_8136407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136407).length < 2 ^ (prefixWord ++ tailWord_8136407).sum := by decide
  have hdescent : baseEnd_8136407 < baseStart_8136407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136427 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6]
def baseStart_8136427 : Nat := 118140960795 + 8136427 * 2 ^ 59
def prefixEnd_8136427 : Nat := 4983230072969 + 3 ^ 40 * 8136427 * 2
def baseEnd_8136427 : Nat := 4177897861219742925643759

theorem tailTrace_8136427 : CollatzResearch.WordTrace tailWord_8136427 prefixEnd_8136427 4177897861219742925643759 := by
  unfold tailWord_8136427
  simp only [CollatzResearch.WordTrace]
  refine ⟨296759872494122044945711535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197839914996081363297141023 296759872494122044945711535)
  ·
    refine ⟨445139808741183067418567303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296759872494122044945711535 445139808741183067418567303)
    ·
      refine ⟨667709713111774601127850955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445139808741183067418567303 667709713111774601127850955)
      ·
        refine ⟨1001564569667661901691776433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667709713111774601127850955 1001564569667661901691776433)
        ·
          refine ⟨751173427250746426268832325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001564569667661901691776433 751173427250746426268832325)
          ·
            refine ⟨140845017609514954925406061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 751173427250746426268832325 140845017609514954925406061)
            ·
              refine ⟨52816881603568108097027273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140845017609514954925406061 52816881603568108097027273)
              ·
                refine ⟨39612661202676081072770455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52816881603568108097027273 39612661202676081072770455)
                ·
                  refine ⟨59418991804014121609155683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39612661202676081072770455 59418991804014121609155683)
                  ·
                    refine ⟨89128487706021182413733525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59418991804014121609155683 89128487706021182413733525)
                    ·
                      refine ⟨4177897861219742925643759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89128487706021182413733525 4177897861219742925643759)
                      ·
                        rfl

theorem cell23_8136427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_8136427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136427 prefixEnd_8136427 := by exact prefixLift 8136427
  have htrace : WordTrace (prefixWord ++ tailWord_8136427) baseStart_8136427 baseEnd_8136427 := by
    simpa [prefixWord, tailWord_8136427, baseEnd_8136427] using wordTrace_append hprefix tailTrace_8136427
  have hstable : (prefixWord ++ tailWord_8136427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136427).length < 2 ^ (prefixWord ++ tailWord_8136427).sum := by decide
  have hdescent : baseEnd_8136427 < baseStart_8136427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136434 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_8136434 : Nat := 118140960795 + 8136434 * 2 ^ 59
def prefixEnd_8136434 : Nat := 4983230072969 + 3 ^ 40 * 8136434 * 2
def baseEnd_8136434 : Nat := 4177901455584324398256227

theorem tailTrace_8136434 : CollatzResearch.WordTrace tailWord_8136434 prefixEnd_8136434 4177901455584324398256227 := by
  unfold tailWord_8136434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74190031951274171285304089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197840085203397790094144237 74190031951274171285304089)
  ·
    refine ⟨55642523963455628463978067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74190031951274171285304089 55642523963455628463978067)
    ·
      refine ⟨83463785945183442695967101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55642523963455628463978067 83463785945183442695967101)
      ·
        refine ⟨31298919729443791010987663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83463785945183442695967101 31298919729443791010987663)
        ·
          refine ⟨46948379594165686516481495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31298919729443791010987663 46948379594165686516481495)
          ·
            refine ⟨70422569391248529774722243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46948379594165686516481495 70422569391248529774722243)
            ·
              refine ⟨105633854086872794662083365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70422569391248529774722243 105633854086872794662083365)
              ·
                refine ⟨19806347641288648999140631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105633854086872794662083365 19806347641288648999140631)
                ·
                  refine ⟨29709521461932973498710947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19806347641288648999140631 29709521461932973498710947)
                  ·
                    refine ⟨44564282192899460248066421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29709521461932973498710947 44564282192899460248066421)
                    ·
                      refine ⟨4177901455584324398256227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44564282192899460248066421 4177901455584324398256227)
                      ·
                        rfl

theorem cell23_8136434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_8136434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136434 prefixEnd_8136434 := by exact prefixLift 8136434
  have htrace : WordTrace (prefixWord ++ tailWord_8136434) baseStart_8136434 baseEnd_8136434 := by
    simpa [prefixWord, tailWord_8136434, baseEnd_8136434] using wordTrace_append hprefix tailTrace_8136434
  have hstable : (prefixWord ++ tailWord_8136434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136434).length < 2 ^ (prefixWord ++ tailWord_8136434).sum := by decide
  have hdescent : baseEnd_8136434 < baseStart_8136434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136444 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_8136444 : Nat := 118140960795 + 8136444 * 2 ^ 59
def prefixEnd_8136444 : Nat := 4983230072969 + 3 ^ 40 * 8136444 * 2
def baseEnd_8136444 : Nat := 4177906590390869359131181

theorem tailTrace_8136444 : CollatzResearch.WordTrace tailWord_8136444 prefixEnd_8136444 4177906590390869359131181 := by
  unfold tailWord_8136444
  simp only [CollatzResearch.WordTrace]
  refine ⟨148380246267530228424540193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197840328356706971232720257 148380246267530228424540193)
  ·
    refine ⟨111285184700647671318405145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148380246267530228424540193 111285184700647671318405145)
    ·
      refine ⟨83463888525485753488803859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111285184700647671318405145 83463888525485753488803859)
      ·
        refine ⟨125195832788228630233205789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83463888525485753488803859 125195832788228630233205789)
        ·
          refine ⟨46948437295585736337452171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125195832788228630233205789 46948437295585736337452171)
          ·
            refine ⟨70422655943378604506178257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46948437295585736337452171 70422655943378604506178257)
            ·
              refine ⟨52816991957533953379633693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70422655943378604506178257 52816991957533953379633693)
              ·
                refine ⟨19806371984075232517362635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52816991957533953379633693 19806371984075232517362635)
                ·
                  refine ⟨29709557976112848776043953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19806371984075232517362635 29709557976112848776043953)
                  ·
                    refine ⟨22282168482084636582032965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29709557976112848776043953 22282168482084636582032965)
                    ·
                      refine ⟨4177906590390869359131181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22282168482084636582032965 4177906590390869359131181)
                      ·
                        rfl

theorem cell23_8136444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_8136444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136444 prefixEnd_8136444 := by exact prefixLift 8136444
  have htrace : WordTrace (prefixWord ++ tailWord_8136444) baseStart_8136444 baseEnd_8136444 := by
    simpa [prefixWord, tailWord_8136444, baseEnd_8136444] using wordTrace_append hprefix tailTrace_8136444
  have hstable : (prefixWord ++ tailWord_8136444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136444).length < 2 ^ (prefixWord ++ tailWord_8136444).sum := by decide
  have hdescent : baseEnd_8136444 < baseStart_8136444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136451 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 3]
def baseStart_8136451 : Nat := 118140960795 + 8136451 * 2 ^ 59
def prefixEnd_8136451 : Nat := 4983230072969 + 3 ^ 40 * 8136451 * 2
def baseEnd_8136451 : Nat := 4177910184755450831743649

theorem tailTrace_8136451 : CollatzResearch.WordTrace tailWord_8136451 prefixEnd_8136451 4177910184755450831743649 := by
  unfold tailWord_8136451
  simp only [CollatzResearch.WordTrace]
  refine ⟨296760747846035097044585207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197840498564023398029723471 296760747846035097044585207)
  ·
    refine ⟨445141121769052645566877811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296760747846035097044585207 445141121769052645566877811)
    ·
      refine ⟨667711682653578968350316717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445141121769052645566877811 667711682653578968350316717)
      ·
        refine ⟨250391880995092113131368769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667711682653578968350316717 250391880995092113131368769)
        ·
          refine ⟨187793910746319084848526577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250391880995092113131368769 187793910746319084848526577)
          ·
            refine ⟨140845433059739313636394933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187793910746319084848526577 140845433059739313636394933)
            ·
              refine ⟨13204259349350560653412025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140845433059739313636394933 13204259349350560653412025)
              ·
                refine ⟨9903194512012920490059019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13204259349350560653412025 9903194512012920490059019)
                ·
                  refine ⟨14854791768019380735088529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9903194512012920490059019 14854791768019380735088529)
                  ·
                    refine ⟨11141093826014535551316397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14854791768019380735088529 11141093826014535551316397)
                    ·
                      refine ⟨4177910184755450831743649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141093826014535551316397 4177910184755450831743649)
                      ·
                        rfl

theorem cell23_8136451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_8136451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136451 prefixEnd_8136451 := by exact prefixLift 8136451
  have htrace : WordTrace (prefixWord ++ tailWord_8136451) baseStart_8136451 baseEnd_8136451 := by
    simpa [prefixWord, tailWord_8136451, baseEnd_8136451] using wordTrace_append hprefix tailTrace_8136451
  have hstable : (prefixWord ++ tailWord_8136451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136451).length < 2 ^ (prefixWord ++ tailWord_8136451).sum := by decide
  have hdescent : baseEnd_8136451 < baseStart_8136451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136484 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_8136484 : Nat := 118140960795 + 8136484 * 2 ^ 59
def prefixEnd_8136484 : Nat := 4983230072969 + 3 ^ 40 * 8136484 * 2
def baseEnd_8136484 : Nat := 1392642376539016400876999

theorem tailTrace_8136484 : CollatzResearch.WordTrace tailWord_8136484 prefixEnd_8136484 1392642376539016400876999 := by
  unfold tailWord_8136484
  simp only [CollatzResearch.WordTrace]
  refine ⟨148380975727457771840268253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197841300969943695787024337 148380975727457771840268253)
  ·
    refine ⟨55642865897796664440100595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148380975727457771840268253 55642865897796664440100595)
    ·
      refine ⟨83464298846694996660150893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55642865897796664440100595 83464298846694996660150893)
      ·
        refine ⟨31299112067510623747556585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83464298846694996660150893 31299112067510623747556585)
        ·
          refine ⟨23474334050632967810667439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31299112067510623747556585 23474334050632967810667439)
          ·
            refine ⟨35211501075949451716001159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23474334050632967810667439 35211501075949451716001159)
            ·
              refine ⟨52817251613924177574001739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35211501075949451716001159 52817251613924177574001739)
              ·
                refine ⟨79225877420886266361002609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52817251613924177574001739 79225877420886266361002609)
                ·
                  refine ⟨59419408065664699770751957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79225877420886266361002609 59419408065664699770751957)
                  ·
                    refine ⟨1392642376539016400876999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59419408065664699770751957 1392642376539016400876999)
                    ·
                      rfl

theorem cell23_8136484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_8136484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136484 prefixEnd_8136484 := by exact prefixLift 8136484
  have htrace : WordTrace (prefixWord ++ tailWord_8136484) baseStart_8136484 baseEnd_8136484 := by
    simpa [prefixWord, tailWord_8136484, baseEnd_8136484] using wordTrace_append hprefix tailTrace_8136484
  have hstable : (prefixWord ++ tailWord_8136484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136484).length < 2 ^ (prefixWord ++ tailWord_8136484).sum := by decide
  have hdescent : baseEnd_8136484 < baseStart_8136484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136498 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_8136498 : Nat := 118140960795 + 8136498 * 2 ^ 59
def prefixEnd_8136498 : Nat := 4983230072969 + 3 ^ 40 * 8136498 * 2
def baseEnd_8136498 : Nat := 4177934318346212147855933

theorem tailTrace_8136498 : CollatzResearch.WordTrace tailWord_8136498 prefixEnd_8136498 4177934318346212147855933 := by
  unfold tailWord_8136498
  simp only [CollatzResearch.WordTrace]
  refine ⟨74190615519216206017886537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197841641384576549381030765 74190615519216206017886537)
  ·
    refine ⟨55642961639412154513414903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74190615519216206017886537 55642961639412154513414903)
    ·
      refine ⟨83464442459118231770122355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55642961639412154513414903 83464442459118231770122355)
      ·
        refine ⟨125196663688677347655183533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83464442459118231770122355 125196663688677347655183533)
        ·
          refine ⟨46948748883254005370693825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125196663688677347655183533 46948748883254005370693825)
          ·
            refine ⟨35211561662440504028020369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46948748883254005370693825 35211561662440504028020369)
            ·
              refine ⟨26408671246830378021015277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35211561662440504028020369 26408671246830378021015277)
              ·
                refine ⟨9903251717561391757880729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26408671246830378021015277 9903251717561391757880729)
                ·
                  refine ⟨7427438788171043818410547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9903251717561391757880729 7427438788171043818410547)
                  ·
                    refine ⟨11141158182256565727615821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7427438788171043818410547 11141158182256565727615821)
                    ·
                      refine ⟨4177934318346212147855933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141158182256565727615821 4177934318346212147855933)
                      ·
                        rfl

theorem cell23_8136498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_8136498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136498 prefixEnd_8136498 := by exact prefixLift 8136498
  have htrace : WordTrace (prefixWord ++ tailWord_8136498) baseStart_8136498 baseEnd_8136498 := by
    simpa [prefixWord, tailWord_8136498, baseEnd_8136498] using wordTrace_append hprefix tailTrace_8136498
  have hstable : (prefixWord ++ tailWord_8136498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136498).length < 2 ^ (prefixWord ++ tailWord_8136498).sum := by decide
  have hdescent : baseEnd_8136498 < baseStart_8136498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136521 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 1, 4, 2]
def baseStart_8136521 : Nat := 118140960795 + 8136521 * 2 ^ 59
def prefixEnd_8136521 : Nat := 4983230072969 + 3 ^ 40 * 8136521 * 2
def baseEnd_8136521 : Nat := 4177946128401265557868327

theorem tailTrace_8136521 : CollatzResearch.WordTrace tailWord_8136521 prefixEnd_8136521 4177946128401265557868327 := by
  unfold tailWord_8136521
  simp only [CollatzResearch.WordTrace]
  refine ⟨296763300955781498999633417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197842200637187665999755611 296763300955781498999633417)
  ·
    refine ⟨222572475716836124249725063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296763300955781498999633417 222572475716836124249725063)
    ·
      refine ⟨333858713575254186374587595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222572475716836124249725063 333858713575254186374587595)
      ·
        refine ⟨500788070362881279561881393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333858713575254186374587595 500788070362881279561881393)
        ·
          refine ⟨375591052772160959671411045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500788070362881279561881393 375591052772160959671411045)
          ·
            refine ⟨70423322394780179938389571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375591052772160959671411045 70423322394780179938389571)
            ·
              refine ⟨105634983592170269907584357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70423322394780179938389571 105634983592170269907584357)
              ·
                refine ⟨19806559423531925607672067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105634983592170269907584357 19806559423531925607672067)
                ·
                  refine ⟨29709839135297888411508101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19806559423531925607672067 29709839135297888411508101)
                  ·
                    refine ⟨5570594837868354077157769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29709839135297888411508101 5570594837868354077157769)
                    ·
                      refine ⟨4177946128401265557868327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570594837868354077157769 4177946128401265557868327)
                      ·
                        rfl

theorem cell23_8136521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 4, 2].length) (baseStart_8136521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136521 prefixEnd_8136521 := by exact prefixLift 8136521
  have htrace : WordTrace (prefixWord ++ tailWord_8136521) baseStart_8136521 baseEnd_8136521 := by
    simpa [prefixWord, tailWord_8136521, baseEnd_8136521] using wordTrace_append hprefix tailTrace_8136521
  have hstable : (prefixWord ++ tailWord_8136521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136521).length < 2 ^ (prefixWord ++ tailWord_8136521).sum := by decide
  have hdescent : baseEnd_8136521 < baseStart_8136521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136538 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2]
def baseStart_8136538 : Nat := 118140960795 + 8136538 * 2 ^ 59
def prefixEnd_8136538 : Nat := 4983230072969 + 3 ^ 40 * 8136538 * 2
def baseEnd_8136538 : Nat := 4177954857572391991355749

theorem tailTrace_8136538 : CollatzResearch.WordTrace tailWord_8136538 prefixEnd_8136538 4177954857572391991355749 := by
  unfold tailWord_8136538
  simp only [CollatzResearch.WordTrace]
  refine ⟨74190980249179977725750567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197842613997813273935334845 74190980249179977725750567)
  ·
    refine ⟨111286470373769966588625851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74190980249179977725750567 111286470373769966588625851)
    ·
      refine ⟨166929705560654949882938777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111286470373769966588625851 166929705560654949882938777)
      ·
        refine ⟨125197279170491212412204083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166929705560654949882938777 125197279170491212412204083)
        ·
          refine ⟨187795918755736818618306125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125197279170491212412204083 187795918755736818618306125)
          ·
            refine ⟨70423469533401306981864797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187795918755736818618306125 70423469533401306981864797)
            ·
              refine ⟨26408801075025490118199299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70423469533401306981864797 26408801075025490118199299)
              ·
                refine ⟨39613201612538235177298949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26408801075025490118199299 39613201612538235177298949)
                ·
                  refine ⟨7427475302350919095743553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39613201612538235177298949 7427475302350919095743553)
                  ·
                    refine ⟨5570606476763189321807665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7427475302350919095743553 5570606476763189321807665)
                    ·
                      refine ⟨4177954857572391991355749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570606476763189321807665 4177954857572391991355749)
                      ·
                        rfl

theorem cell23_8136538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_8136538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136538 prefixEnd_8136538 := by exact prefixLift 8136538
  have htrace : WordTrace (prefixWord ++ tailWord_8136538) baseStart_8136538 baseEnd_8136538 := by
    simpa [prefixWord, tailWord_8136538, baseEnd_8136538] using wordTrace_append hprefix tailTrace_8136538
  have hstable : (prefixWord ++ tailWord_8136538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136538).length < 2 ^ (prefixWord ++ tailWord_8136538).sum := by decide
  have hdescent : baseEnd_8136538 < baseStart_8136538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136544 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 7]
def baseStart_8136544 : Nat := 118140960795 + 8136544 * 2 ^ 59
def prefixEnd_8136544 : Nat := 4983230072969 + 3 ^ 40 * 8136544 * 2
def baseEnd_8136544 : Nat := 464217548717368774208969

theorem tailTrace_8136544 : CollatzResearch.WordTrace tailWord_8136544 prefixEnd_8136544 464217548717368774208969 := by
  unfold tailWord_8136544
  simp only [CollatzResearch.WordTrace]
  refine ⟨148382069917349086963860343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197842759889798782618480457 148382069917349086963860343)
  ·
    refine ⟨222573104876023630445790515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148382069917349086963860343 222573104876023630445790515)
    ·
      refine ⟨333859657314035445668685773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222573104876023630445790515 333859657314035445668685773)
      ·
        refine ⟨125197371492763292125757165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333859657314035445668685773 125197371492763292125757165)
        ·
          refine ⟨46949014309786234547158937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125197371492763292125757165 46949014309786234547158937)
          ·
            refine ⟨35211760732339675910369203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46949014309786234547158937 35211760732339675910369203)
            ·
              refine ⟨52817641098509513865553805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35211760732339675910369203 52817641098509513865553805)
              ·
                refine ⟨19806615411941067699582677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52817641098509513865553805 19806615411941067699582677)
                ·
                  refine ⟨464217548717368774208969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19806615411941067699582677 464217548717368774208969)
                  ·
                    rfl

theorem cell23_8136544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_8136544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136544 prefixEnd_8136544 := by exact prefixLift 8136544
  have htrace : WordTrace (prefixWord ++ tailWord_8136544) baseStart_8136544 baseEnd_8136544 := by
    simpa [prefixWord, tailWord_8136544, baseEnd_8136544] using wordTrace_append hprefix tailTrace_8136544
  have hstable : (prefixWord ++ tailWord_8136544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136544).length < 2 ^ (prefixWord ++ tailWord_8136544).sum := by decide
  have hdescent : baseEnd_8136544 < baseStart_8136544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136611 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 6, 2]
def baseStart_8136611 : Nat := 118140960795 + 8136611 * 2 ^ 59
def prefixEnd_8136611 : Nat := 4983230072969 + 3 ^ 40 * 8136611 * 2
def baseEnd_8136611 : Nat := 4177992341660170205742913

theorem tailTrace_8136611 : CollatzResearch.WordTrace tailWord_8136611 prefixEnd_8136611 4177992341660170205742913 := by
  unfold tailWord_8136611
  simp only [CollatzResearch.WordTrace]
  refine ⟨296766583525455444370409687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197844389016970296246939791 296766583525455444370409687)
  ·
    refine ⟨445149875288183166555614531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296766583525455444370409687 445149875288183166555614531)
    ·
      refine ⟨667724812932274749833421797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445149875288183166555614531 667724812932274749833421797)
      ·
        refine ⟨125198402424801515593766587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 667724812932274749833421797 125198402424801515593766587)
        ·
          refine ⟨187797603637202273390649881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125198402424801515593766587 187797603637202273390649881)
          ·
            refine ⟨140848202727901705042987411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187797603637202273390649881 140848202727901705042987411)
            ·
              refine ⟨211272304091852557564481117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140848202727901705042987411 211272304091852557564481117)
              ·
                refine ⟨79227114034444709086680419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211272304091852557564481117 79227114034444709086680419)
                ·
                  refine ⟨118840671051667063630020629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79227114034444709086680419 118840671051667063630020629)
                  ·
                    refine ⟨5570656455546893607657217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118840671051667063630020629 5570656455546893607657217)
                    ·
                      refine ⟨4177992341660170205742913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570656455546893607657217 4177992341660170205742913)
                      ·
                        rfl

theorem cell23_8136611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_8136611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136611 prefixEnd_8136611 := by exact prefixLift 8136611
  have htrace : WordTrace (prefixWord ++ tailWord_8136611) baseStart_8136611 baseEnd_8136611 := by
    simpa [prefixWord, tailWord_8136611, baseEnd_8136611] using wordTrace_append hprefix tailTrace_8136611
  have hstable : (prefixWord ++ tailWord_8136611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136611).length < 2 ^ (prefixWord ++ tailWord_8136611).sum := by decide
  have hdescent : baseEnd_8136611 < baseStart_8136611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136634 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_8136634 : Nat := 118140960795 + 8136634 * 2 ^ 59
def prefixEnd_8136634 : Nat := 4983230072969 + 3 ^ 40 * 8136634 * 2
def baseEnd_8136634 : Nat := 464222683523913735083923

theorem tailTrace_8136634 : CollatzResearch.WordTrace tailWord_8136634 prefixEnd_8136634 464222683523913735083923 := by
  unfold tailWord_8136634
  simp only [CollatzResearch.WordTrace]
  refine ⟨74191855601093029824624239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197844948269581412865664637 74191855601093029824624239)
  ·
    refine ⟨111287783401639544736936359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74191855601093029824624239 111287783401639544736936359)
    ·
      refine ⟨166931675102459317105404539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111287783401639544736936359 166931675102459317105404539)
      ·
        refine ⟨250397512653688975658106809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166931675102459317105404539 250397512653688975658106809)
        ·
          refine ⟨187798134490266731743580107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250397512653688975658106809 187798134490266731743580107)
          ·
            refine ⟨281697201735400097615370161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187798134490266731743580107 281697201735400097615370161)
            ·
              refine ⟨211272901301550073211527621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281697201735400097615370161 211272901301550073211527621)
              ·
                refine ⟨39613668994040638727161429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211272901301550073211527621 39613668994040638727161429)
                ·
                  refine ⟨464222683523913735083923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39613668994040638727161429 464222683523913735083923)
                  ·
                    rfl

theorem cell23_8136634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_8136634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136634 prefixEnd_8136634 := by exact prefixLift 8136634
  have htrace : WordTrace (prefixWord ++ tailWord_8136634) baseStart_8136634 baseEnd_8136634 := by
    simpa [prefixWord, tailWord_8136634, baseEnd_8136634] using wordTrace_append hprefix tailTrace_8136634
  have hstable : (prefixWord ++ tailWord_8136634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136634).length < 2 ^ (prefixWord ++ tailWord_8136634).sum := by decide
  have hdescent : baseEnd_8136634 < baseStart_8136634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136648 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_8136648 : Nat := 118140960795 + 8136648 * 2 ^ 59
def prefixEnd_8136648 : Nat := 4983230072969 + 3 ^ 40 * 8136648 * 2
def baseEnd_8136648 : Nat := 4178011340444386560980243

theorem tailTrace_8136648 : CollatzResearch.WordTrace tailWord_8136648 prefixEnd_8136648 4178011340444386560980243 := by
  unfold tailWord_8136648
  simp only [CollatzResearch.WordTrace]
  refine ⟨148383966513160699844753299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197845288684214266459671065 148383966513160699844753299)
  ·
    refine ⟨222575949769741049767129949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148383966513160699844753299 222575949769741049767129949)
    ·
      refine ⟨83465981163652893662673731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222575949769741049767129949 83465981163652893662673731)
      ·
        refine ⟨125198971745479340494010597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83465981163652893662673731 125198971745479340494010597)
        ·
          refine ⟨23474807202277376342626987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125198971745479340494010597 23474807202277376342626987)
          ·
            refine ⟨35212210803416064513940481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23474807202277376342626987 35212210803416064513940481)
            ·
              refine ⟨26409158102562048385455361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35212210803416064513940481 26409158102562048385455361)
              ·
                refine ⟨19806868576921536289091521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26409158102562048385455361 19806868576921536289091521)
                ·
                  refine ⟨14855151432691152216818641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19806868576921536289091521 14855151432691152216818641)
                  ·
                    refine ⟨11141363574518364162613981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14855151432691152216818641 11141363574518364162613981)
                    ·
                      refine ⟨4178011340444386560980243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141363574518364162613981 4178011340444386560980243)
                      ·
                        rfl

theorem cell23_8136648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_8136648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136648 prefixEnd_8136648 := by exact prefixLift 8136648
  have htrace : WordTrace (prefixWord ++ tailWord_8136648) baseStart_8136648 baseEnd_8136648 := by
    simpa [prefixWord, tailWord_8136648, baseEnd_8136648] using wordTrace_append hprefix tailTrace_8136648
  have hstable : (prefixWord ++ tailWord_8136648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136648).length < 2 ^ (prefixWord ++ tailWord_8136648).sum := by decide
  have hdescent : baseEnd_8136648 < baseStart_8136648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136651 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 6]
def baseStart_8136651 : Nat := 118140960795 + 8136651 * 2 ^ 59
def prefixEnd_8136651 : Nat := 4983230072969 + 3 ^ 40 * 8136651 * 2
def baseEnd_8136651 : Nat := 464223653431816672138081

theorem tailTrace_8136651 : CollatzResearch.WordTrace tailWord_8136651 prefixEnd_8136651 464223653431816672138081 := by
  unfold tailWord_8136651
  simp only [CollatzResearch.WordTrace]
  refine ⟨296768042445310531201865807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197845361630207020801243871 296768042445310531201865807)
  ·
    refine ⟨445152063667965796802798711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296768042445310531201865807 445152063667965796802798711)
    ·
      refine ⟨667728095501948695204198067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445152063667965796802798711 667728095501948695204198067)
      ·
        refine ⟨1001592143252923042806297101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667728095501948695204198067 1001592143252923042806297101)
        ·
          refine ⟨375597053719846141052361413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1001592143252923042806297101 375597053719846141052361413)
          ·
            refine ⟨70424447572471151447317765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375597053719846141052361413 70424447572471151447317765)
            ·
              refine ⟨13204583919838340896372081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70424447572471151447317765 13204583919838340896372081)
              ·
                refine ⟨9903437939878755672279061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13204583919838340896372081 9903437939878755672279061)
                ·
                  refine ⟨464223653431816672138081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9903437939878755672279061 464223653431816672138081)
                  ·
                    rfl

theorem cell23_8136651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 6].length) (baseStart_8136651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136651 prefixEnd_8136651 := by exact prefixLift 8136651
  have htrace : WordTrace (prefixWord ++ tailWord_8136651) baseStart_8136651 baseEnd_8136651 := by
    simpa [prefixWord, tailWord_8136651, baseEnd_8136651] using wordTrace_append hprefix tailTrace_8136651
  have hstable : (prefixWord ++ tailWord_8136651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136651).length < 2 ^ (prefixWord ++ tailWord_8136651).sum := by decide
  have hdescent : baseEnd_8136651 < baseStart_8136651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136662 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_8136662 : Nat := 118140960795 + 8136662 * 2 ^ 59
def prefixEnd_8136662 : Nat := 4983230072969 + 3 ^ 40 * 8136662 * 2
def baseEnd_8136662 : Nat := 4178018529173549506205179

theorem tailTrace_8136662 : CollatzResearch.WordTrace tailWord_8136662 prefixEnd_8136662 4178018529173549506205179 := by
  unfold tailWord_8136662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548027728016917505032265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197845629098847120053677493 18548027728016917505032265)
  ·
    refine ⟨13911020796012688128774199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18548027728016917505032265 13911020796012688128774199)
    ·
      refine ⟨20866531194019032193161299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13911020796012688128774199 20866531194019032193161299)
      ·
        refine ⟨31299796791028548289741949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20866531194019032193161299 31299796791028548289741949)
        ·
          refine ⟨11737423796635705608653231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31299796791028548289741949 11737423796635705608653231)
          ·
            refine ⟨17606135694953558412979847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737423796635705608653231 17606135694953558412979847)
            ·
              refine ⟨26409203542430337619469771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606135694953558412979847 26409203542430337619469771)
              ·
                refine ⟨39613805313645506429204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26409203542430337619469771 39613805313645506429204657)
                ·
                  refine ⟨29710353985234129821903493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39613805313645506429204657 29710353985234129821903493)
                  ·
                    refine ⟨5570691372231399341606905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29710353985234129821903493 5570691372231399341606905)
                    ·
                      refine ⟨4178018529173549506205179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570691372231399341606905 4178018529173549506205179)
                      ·
                        rfl

theorem cell23_8136662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_8136662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136662 prefixEnd_8136662 := by exact prefixLift 8136662
  have htrace : WordTrace (prefixWord ++ tailWord_8136662) baseStart_8136662 baseEnd_8136662 := by
    simpa [prefixWord, tailWord_8136662, baseEnd_8136662] using wordTrace_append hprefix tailTrace_8136662
  have hstable : (prefixWord ++ tailWord_8136662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136662).length < 2 ^ (prefixWord ++ tailWord_8136662).sum := by decide
  have hdescent : baseEnd_8136662 < baseStart_8136662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136731 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4]
def baseStart_8136731 : Nat := 118140960795 + 8136731 * 2 ^ 59
def prefixEnd_8136731 : Nat := 4983230072969 + 3 ^ 40 * 8136731 * 2
def baseEnd_8136731 : Nat := 4178053959338709736242361

theorem tailTrace_8136731 : CollatzResearch.WordTrace tailWord_8136731 prefixEnd_8136731 4178053959338709736242361 := by
  unfold tailWord_8136731
  simp only [CollatzResearch.WordTrace]
  refine ⟨296770960285020704864778047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197847306856680469909852031 296770960285020704864778047)
  ·
    refine ⟨445156440427531057297167071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296770960285020704864778047 445156440427531057297167071)
    ·
      refine ⟨667734660641296585945750607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445156440427531057297167071 667734660641296585945750607)
      ·
        refine ⟨1001601990961944878918625911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667734660641296585945750607 1001601990961944878918625911)
        ·
          refine ⟨1502402986442917318377938867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001601990961944878918625911 1502402986442917318377938867)
          ·
            refine ⟨2253604479664375977566908301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502402986442917318377938867 2253604479664375977566908301)
            ·
              refine ⟨845101679874140991587590613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2253604479664375977566908301 845101679874140991587590613)
              ·
                refine ⟨19807070622050179490334155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 845101679874140991587590613 19807070622050179490334155)
                ·
                  refine ⟨29710605933075269235501233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19807070622050179490334155 29710605933075269235501233)
                  ·
                    refine ⟨22282954449806451926625925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29710605933075269235501233 22282954449806451926625925)
                    ·
                      refine ⟨4178053959338709736242361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22282954449806451926625925 4178053959338709736242361)
                      ·
                        rfl

theorem cell23_8136731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].length) (baseStart_8136731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136731 prefixEnd_8136731 := by exact prefixLift 8136731
  have htrace : WordTrace (prefixWord ++ tailWord_8136731) baseStart_8136731 baseEnd_8136731 := by
    simpa [prefixWord, tailWord_8136731, baseEnd_8136731] using wordTrace_append hprefix tailTrace_8136731
  have hstable : (prefixWord ++ tailWord_8136731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136731).length < 2 ^ (prefixWord ++ tailWord_8136731).sum := by decide
  have hdescent : baseEnd_8136731 < baseStart_8136731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136735 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 3, 2, 2]
def baseStart_8136735 : Nat := 118140960795 + 8136735 * 2 ^ 59
def prefixEnd_8136735 : Nat := 4983230072969 + 3 ^ 40 * 8136735 * 2
def baseEnd_8136735 : Nat := 4178056013261327720592343

theorem tailTrace_8136735 : CollatzResearch.WordTrace tailWord_8136735 prefixEnd_8136735 4178056013261327720592343 := by
  unfold tailWord_8136735
  simp only [CollatzResearch.WordTrace]
  refine ⟨296771106177006213547923659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197847404118004142365282439 296771106177006213547923659)
  ·
    refine ⟨445156659265509320321885489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296771106177006213547923659 445156659265509320321885489)
    ·
      refine ⟨333867494449131990241414117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445156659265509320321885489 333867494449131990241414117)
      ·
        refine ⟨62600155209212248170265147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333867494449131990241414117 62600155209212248170265147)
        ·
          refine ⟨93900232813818372255397721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62600155209212248170265147 93900232813818372255397721)
          ·
            refine ⟨70425174610363779191548291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93900232813818372255397721 70425174610363779191548291)
            ·
              refine ⟨105637761915545668787322437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70425174610363779191548291 105637761915545668787322437)
              ·
                refine ⟨19807080359164812897622957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105637761915545668787322437 19807080359164812897622957)
                ·
                  refine ⟨7427655134686804836608609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19807080359164812897622957 7427655134686804836608609)
                  ·
                    refine ⟨5570741351015103627456457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7427655134686804836608609 5570741351015103627456457)
                    ·
                      refine ⟨4178056013261327720592343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570741351015103627456457 4178056013261327720592343)
                      ·
                        rfl

theorem cell23_8136735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_8136735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136735 prefixEnd_8136735 := by exact prefixLift 8136735
  have htrace : WordTrace (prefixWord ++ tailWord_8136735) baseStart_8136735 baseEnd_8136735 := by
    simpa [prefixWord, tailWord_8136735, baseEnd_8136735] using wordTrace_append hprefix tailTrace_8136735
  have hstable : (prefixWord ++ tailWord_8136735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136735).length < 2 ^ (prefixWord ++ tailWord_8136735).sum := by decide
  have hdescent : baseEnd_8136735 < baseStart_8136735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136741 : List Nat := [1, 3, 1, 2, 2, 4, 1, 9]
def baseStart_8136741 : Nat := 118140960795 + 8136741 * 2 ^ 59
def prefixEnd_8136741 : Nat := 4983230072969 + 3 ^ 40 * 8136741 * 2
def baseEnd_8136741 : Nat := 154742929412787211004345

theorem tailTrace_8136741 : CollatzResearch.WordTrace tailWord_8136741 prefixEnd_8136741 154742929412787211004345 := by
  unfold tailWord_8136741
  simp only [CollatzResearch.WordTrace]
  refine ⟨296771325014984476572642077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197847550009989651048428051 296771325014984476572642077)
  ·
    refine ⟨111289246880619178714740779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296771325014984476572642077 111289246880619178714740779)
    ·
      refine ⟨166933870320928768072111169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111289246880619178714740779 166933870320928768072111169)
      ·
        refine ⟨125200402740696576054083377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166933870320928768072111169 125200402740696576054083377)
        ·
          refine ⟨93900302055522432040562533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125200402740696576054083377 93900302055522432040562533)
          ·
            refine ⟨17606306635410456007605475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93900302055522432040562533 17606306635410456007605475)
            ·
              refine ⟨26409459953115684011408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606306635410456007605475 26409459953115684011408213)
              ·
                refine ⟨154742929412787211004345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26409459953115684011408213 154742929412787211004345)
                ·
                  rfl

theorem cell23_8136741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 9].length) (baseStart_8136741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136741 prefixEnd_8136741 := by exact prefixLift 8136741
  have htrace : WordTrace (prefixWord ++ tailWord_8136741) baseStart_8136741 baseEnd_8136741 := by
    simpa [prefixWord, tailWord_8136741, baseEnd_8136741] using wordTrace_append hprefix tailTrace_8136741
  have hstable : (prefixWord ++ tailWord_8136741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136741).length < 2 ^ (prefixWord ++ tailWord_8136741).sum := by decide
  have hdescent : baseEnd_8136741 < baseStart_8136741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136769 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_8136769 : Nat := 118140960795 + 8136769 * 2 ^ 59
def prefixEnd_8136769 : Nat := 4983230072969 + 3 ^ 40 * 8136769 * 2
def baseEnd_8136769 : Nat := 4178073471603580587567187

theorem tailTrace_8136769 : CollatzResearch.WordTrace tailWord_8136769 prefixEnd_8136769 4178073471603580587567187 := by
  unfold tailWord_8136769
  simp only [CollatzResearch.WordTrace]
  refine ⟨296772346258883037354661361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197848230839255358236440907 296772346258883037354661361)
  ·
    refine ⟨222579259694162278015996021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296772346258883037354661361 222579259694162278015996021)
    ·
      refine ⟨20866805596327713563999627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222579259694162278015996021 20866805596327713563999627)
      ·
        refine ⟨31300208394491570345999441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20866805596327713563999627 31300208394491570345999441)
        ·
          refine ⟨23475156295868677759499581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31300208394491570345999441 23475156295868677759499581)
          ·
            refine ⟨8803183610950754159812343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23475156295868677759499581 8803183610950754159812343)
            ·
              refine ⟨13204775416426131239718515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8803183610950754159812343 13204775416426131239718515)
              ·
                refine ⟨19807163124639196859577773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13204775416426131239718515 19807163124639196859577773)
                ·
                  refine ⟨7427686171739698822341665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19807163124639196859577773 7427686171739698822341665)
                  ·
                    refine ⟨5570764628804774116756249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7427686171739698822341665 5570764628804774116756249)
                    ·
                      refine ⟨4178073471603580587567187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570764628804774116756249 4178073471603580587567187)
                      ·
                        rfl

theorem cell23_8136769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_8136769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136769 prefixEnd_8136769 := by exact prefixLift 8136769
  have htrace : WordTrace (prefixWord ++ tailWord_8136769) baseStart_8136769 baseEnd_8136769 := by
    simpa [prefixWord, tailWord_8136769, baseEnd_8136769] using wordTrace_append hprefix tailTrace_8136769
  have hstable : (prefixWord ++ tailWord_8136769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136769).length < 2 ^ (prefixWord ++ tailWord_8136769).sum := by decide
  have hdescent : baseEnd_8136769 < baseStart_8136769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136778 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_8136778 : Nat := 118140960795 + 8136778 * 2 ^ 59
def prefixEnd_8136778 : Nat := 4983230072969 + 3 ^ 40 * 8136778 * 2
def baseEnd_8136778 : Nat := 4178078092929471052354645

theorem tailTrace_8136778 : CollatzResearch.WordTrace tailWord_8136778 prefixEnd_8136778 4178078092929471052354645 := by
  unfold tailWord_8136778
  simp only [CollatzResearch.WordTrace]
  refine ⟨74193168628962607972934747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197848449677233621261159325 74193168628962607972934747)
  ·
    refine ⟨111289752943443911959402121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74193168628962607972934747 111289752943443911959402121)
    ·
      refine ⟨83467314707582933969551591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111289752943443911959402121 83467314707582933969551591)
      ·
        refine ⟨125200972061374400954327387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83467314707582933969551591 125200972061374400954327387)
        ·
          refine ⟨187801458092061601431491081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125200972061374400954327387 187801458092061601431491081)
          ·
            refine ⟨140851093569046201073618311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187801458092061601431491081 140851093569046201073618311)
            ·
              refine ⟨211276640353569301610427467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140851093569046201073618311 211276640353569301610427467)
              ·
                refine ⟨316914960530353952415641201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211276640353569301610427467 316914960530353952415641201)
                ·
                  refine ⟨237686220397765464311730901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316914960530353952415641201 237686220397765464311730901)
                  ·
                    refine ⟨5570770790572628069806193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 237686220397765464311730901 5570770790572628069806193)
                    ·
                      refine ⟨4178078092929471052354645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570770790572628069806193 4178078092929471052354645)
                      ·
                        rfl

theorem cell23_8136778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_8136778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136778 prefixEnd_8136778 := by exact prefixLift 8136778
  have htrace : WordTrace (prefixWord ++ tailWord_8136778) baseStart_8136778 baseEnd_8136778 := by
    simpa [prefixWord, tailWord_8136778, baseEnd_8136778] using wordTrace_append hprefix tailTrace_8136778
  have hstable : (prefixWord ++ tailWord_8136778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136778).length < 2 ^ (prefixWord ++ tailWord_8136778).sum := by decide
  have hdescent : baseEnd_8136778 < baseStart_8136778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136801 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_8136801 : Nat := 118140960795 + 8136801 * 2 ^ 59
def prefixEnd_8136801 : Nat := 4983230072969 + 3 ^ 40 * 8136801 * 2
def baseEnd_8136801 : Nat := 1392696634328174820789013

theorem tailTrace_8136801 : CollatzResearch.WordTrace tailWord_8136801 prefixEnd_8136801 1392696634328174820789013 := by
  unfold tailWord_8136801
  simp only [CollatzResearch.WordTrace]
  refine ⟨296773513394767106819826257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197849008929844737879884171 296773513394767106819826257)
  ·
    refine ⟨222580135046075330114869693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296773513394767106819826257 222580135046075330114869693)
    ·
      refine ⟨83467550642278248793076135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222580135046075330114869693 83467550642278248793076135)
      ·
        refine ⟨125201325963417373189614203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83467550642278248793076135 125201325963417373189614203)
        ·
          refine ⟨187801988945126059784421305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125201325963417373189614203 187801988945126059784421305)
          ·
            refine ⟨140851491708844544838315979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187801988945126059784421305 140851491708844544838315979)
            ·
              refine ⟨211277237563266817257473969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140851491708844544838315979 211277237563266817257473969)
              ·
                refine ⟨158457928172450112943105477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211277237563266817257473969 158457928172450112943105477)
                ·
                  refine ⟨29710861532334396176832277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158457928172450112943105477 29710861532334396176832277)
                  ·
                    refine ⟨1392696634328174820789013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29710861532334396176832277 1392696634328174820789013)
                    ·
                      rfl

theorem cell23_8136801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_8136801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136801 prefixEnd_8136801 := by exact prefixLift 8136801
  have htrace : WordTrace (prefixWord ++ tailWord_8136801) baseStart_8136801 baseEnd_8136801 := by
    simpa [prefixWord, tailWord_8136801, baseEnd_8136801] using wordTrace_append hprefix tailTrace_8136801
  have hstable : (prefixWord ++ tailWord_8136801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136801).length < 2 ^ (prefixWord ++ tailWord_8136801).sum := by decide
  have hdescent : baseEnd_8136801 < baseStart_8136801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136802 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_8136802 : Nat := 118140960795 + 8136802 * 2 ^ 59
def prefixEnd_8136802 : Nat := 4983230072969 + 3 ^ 40 * 8136802 * 2
def baseEnd_8136802 : Nat := 4178090416465178958454535

theorem tailTrace_8136802 : CollatzResearch.WordTrace tailWord_8136802 prefixEnd_8136802 4178090416465178958454535 := by
  unfold tailWord_8136802
  simp only [CollatzResearch.WordTrace]
  refine ⟨74193387466940870997653165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197849033245175655993741773 74193387466940870997653165)
  ·
    refine ⟨27822520300102826624119937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74193387466940870997653165 27822520300102826624119937)
    ·
      refine ⟨20866890225077119968089953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27822520300102826624119937 20866890225077119968089953)
      ·
        refine ⟨15650167668807839976067465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20866890225077119968089953 15650167668807839976067465)
        ·
          refine ⟨11737625751605879982050599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15650167668807839976067465 11737625751605879982050599)
          ·
            refine ⟨17606438627408819973075899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737625751605879982050599 17606438627408819973075899)
            ·
              refine ⟨26409657941113229959613849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606438627408819973075899 26409657941113229959613849)
              ·
                refine ⟨19807243455834922469710387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26409657941113229959613849 19807243455834922469710387)
                ·
                  refine ⟨29710865183752383704565581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19807243455834922469710387 29710865183752383704565581)
                  ·
                    refine ⟨11141574443907143889212093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29710865183752383704565581 11141574443907143889212093)
                    ·
                      refine ⟨4178090416465178958454535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141574443907143889212093 4178090416465178958454535)
                      ·
                        rfl

theorem cell23_8136802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_8136802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136802 prefixEnd_8136802 := by exact prefixLift 8136802
  have htrace : WordTrace (prefixWord ++ tailWord_8136802) baseStart_8136802 baseEnd_8136802 := by
    simpa [prefixWord, tailWord_8136802, baseEnd_8136802] using wordTrace_append hprefix tailTrace_8136802
  have hstable : (prefixWord ++ tailWord_8136802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136802).length < 2 ^ (prefixWord ++ tailWord_8136802).sum := by decide
  have hdescent : baseEnd_8136802 < baseStart_8136802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136828 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_8136828 : Nat := 118140960795 + 8136828 * 2 ^ 59
def prefixEnd_8136828 : Nat := 4983230072969 + 3 ^ 40 * 8136828 * 2
def baseEnd_8136828 : Nat := 4178103766962195856729415

theorem tailTrace_8136828 : CollatzResearch.WordTrace tailWord_8136828 prefixEnd_8136828 4178103766962195856729415 := by
  unfold tailWord_8136828
  simp only [CollatzResearch.WordTrace]
  refine ⟨148387249082834645215529569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197849665443779526954039425 148387249082834645215529569)
  ·
    refine ⟨111290436812125983911647177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148387249082834645215529569 111290436812125983911647177)
    ·
      refine ⟨83467827609094487933735383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111290436812125983911647177 83467827609094487933735383)
      ·
        refine ⟨125201741413641731900603075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83467827609094487933735383 125201741413641731900603075)
        ·
          refine ⟨187802612120462597850904613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125201741413641731900603075 187802612120462597850904613)
          ·
            refine ⟨35212989772586737097044615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187802612120462597850904613 35212989772586737097044615)
            ·
              refine ⟨52819484658880105645566923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35212989772586737097044615 52819484658880105645566923)
              ·
                refine ⟨79229226988320158468350385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52819484658880105645566923 79229226988320158468350385)
                ·
                  refine ⟨59421920241240118851262789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79229226988320158468350385 59421920241240118851262789)
                  ·
                    refine ⟨11141610045232522284611773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59421920241240118851262789 11141610045232522284611773)
                    ·
                      refine ⟨4178103766962195856729415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141610045232522284611773 4178103766962195856729415)
                      ·
                        rfl

theorem cell23_8136828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_8136828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136828 prefixEnd_8136828 := by exact prefixLift 8136828
  have htrace : WordTrace (prefixWord ++ tailWord_8136828) baseStart_8136828 baseEnd_8136828 := by
    simpa [prefixWord, tailWord_8136828, baseEnd_8136828] using wordTrace_append hprefix tailTrace_8136828
  have hstable : (prefixWord ++ tailWord_8136828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136828).length < 2 ^ (prefixWord ++ tailWord_8136828).sum := by decide
  have hdescent : baseEnd_8136828 < baseStart_8136828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136842 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_8136842 : Nat := 118140960795 + 8136842 * 2 ^ 59
def prefixEnd_8136842 : Nat := 4983230072969 + 3 ^ 40 * 8136842 * 2
def baseEnd_8136842 : Nat := 4178110955691358801954351

theorem tailTrace_8136842 : CollatzResearch.WordTrace tailWord_8136842 prefixEnd_8136842 4178110955691358801954351 := by
  unfold tailWord_8136842
  simp only [CollatzResearch.WordTrace]
  refine ⟨74193752196904642705517195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197850005858412380548045853 74193752196904642705517195)
  ·
    refine ⟨111290628295356964058275793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74193752196904642705517195 111290628295356964058275793)
    ·
      refine ⟨83467971221517723043706845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111290628295356964058275793 83467971221517723043706845)
      ·
        refine ⟨31300489208069146141390067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83467971221517723043706845 31300489208069146141390067)
        ·
          refine ⟨46950733812103719212085101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31300489208069146141390067 46950733812103719212085101)
          ·
            refine ⟨17606525179538894704531913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46950733812103719212085101 17606525179538894704531913)
            ·
              refine ⟨13204893884654171028398935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17606525179538894704531913 13204893884654171028398935)
              ·
                refine ⟨19807340826981256542598403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13204893884654171028398935 19807340826981256542598403)
                ·
                  refine ⟨29711011240471884813897605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19807340826981256542598403 29711011240471884813897605)
                  ·
                    refine ⟨5570814607588478402605801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29711011240471884813897605 5570814607588478402605801)
                    ·
                      refine ⟨4178110955691358801954351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570814607588478402605801 4178110955691358801954351)
                      ·
                        rfl

theorem cell23_8136842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_8136842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136842 prefixEnd_8136842 := by exact prefixLift 8136842
  have htrace : WordTrace (prefixWord ++ tailWord_8136842) baseStart_8136842 baseEnd_8136842 := by
    simpa [prefixWord, tailWord_8136842, baseEnd_8136842] using wordTrace_append hprefix tailTrace_8136842
  have hstable : (prefixWord ++ tailWord_8136842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136842).length < 2 ^ (prefixWord ++ tailWord_8136842).sum := by decide
  have hdescent : baseEnd_8136842 < baseStart_8136842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136865 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 5]
def baseStart_8136865 : Nat := 118140960795 + 8136865 * 2 ^ 59
def prefixEnd_8136865 : Nat := 4983230072969 + 3 ^ 40 * 8136865 * 2
def baseEnd_8136865 : Nat := 464235862860712467996305

theorem tailTrace_8136865 : CollatzResearch.WordTrace tailWord_8136865 prefixEnd_8136865 464235862860712467996305 := by
  unfold tailWord_8136865
  simp only [CollatzResearch.WordTrace]
  refine ⟨296775847666535245750156049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197850565111023497166770699 296775847666535245750156049)
  ·
    refine ⟨222581885749901434312617037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296775847666535245750156049 222581885749901434312617037)
    ·
      refine ⟨83468207156213037867231389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222581885749901434312617037 83468207156213037867231389)
      ·
        refine ⟨31300577683579889200211771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83468207156213037867231389 31300577683579889200211771)
        ·
          refine ⟨46950866525369833800317657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31300577683579889200211771 46950866525369833800317657)
          ·
            refine ⟨35213149894027375350238243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46950866525369833800317657 35213149894027375350238243)
            ·
              refine ⟨52819724841041063025357365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35213149894027375350238243 52819724841041063025357365)
              ·
                refine ⟨4951849203847599658627253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52819724841041063025357365 4951849203847599658627253)
                ·
                  refine ⟨464235862860712467996305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4951849203847599658627253 464235862860712467996305)
                  ·
                    rfl

theorem cell23_8136865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 5].length) (baseStart_8136865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136865 prefixEnd_8136865 := by exact prefixLift 8136865
  have htrace : WordTrace (prefixWord ++ tailWord_8136865) baseStart_8136865 baseEnd_8136865 := by
    simpa [prefixWord, tailWord_8136865, baseEnd_8136865] using wordTrace_append hprefix tailTrace_8136865
  have hstable : (prefixWord ++ tailWord_8136865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136865).length < 2 ^ (prefixWord ++ tailWord_8136865).sum := by decide
  have hdescent : baseEnd_8136865 < baseStart_8136865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136938 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_8136938 : Nat := 118140960795 + 8136938 * 2 ^ 59
def prefixEnd_8136938 : Nat := 4983230072969 + 3 ^ 40 * 8136938 * 2
def baseEnd_8136938 : Nat := 464240027759354491817101

theorem tailTrace_8136938 : CollatzResearch.WordTrace tailWord_8136938 prefixEnd_8136938 464240027759354491817101 := by
  unfold tailWord_8136938
  simp only [CollatzResearch.WordTrace]
  refine ⟨74194627548817694804390867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197852340130180519478375645 74194627548817694804390867)
  ·
    refine ⟨111291941323226542206586301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74194627548817694804390867 111291941323226542206586301)
    ·
      refine ⟨41734477996209953327469863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111291941323226542206586301 41734477996209953327469863)
      ·
        refine ⟨62601716994314929991204795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41734477996209953327469863 62601716994314929991204795)
        ·
          refine ⟨93902575491472394986807193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62601716994314929991204795 93902575491472394986807193)
          ·
            refine ⟨70426931618604296240105395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93902575491472394986807193 70426931618604296240105395)
            ·
              refine ⟨105640397427906444360158093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70426931618604296240105395 105640397427906444360158093)
              ·
                refine ⟨39615149035464916635059285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105640397427906444360158093 39615149035464916635059285)
                ·
                  refine ⟨464240027759354491817101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39615149035464916635059285 464240027759354491817101)
                  ·
                    rfl

theorem cell23_8136938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_8136938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136938 prefixEnd_8136938 := by exact prefixLift 8136938
  have htrace : WordTrace (prefixWord ++ tailWord_8136938) baseStart_8136938 baseEnd_8136938 := by
    simpa [prefixWord, tailWord_8136938, baseEnd_8136938] using wordTrace_append hprefix tailTrace_8136938
  have hstable : (prefixWord ++ tailWord_8136938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136938).length < 2 ^ (prefixWord ++ tailWord_8136938).sum := by decide
  have hdescent : baseEnd_8136938 < baseStart_8136938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8136975 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 1, 5, 2]
def baseStart_8136975 : Nat := 118140960795 + 8136975 * 2 ^ 59
def prefixEnd_8136975 : Nat := 4983230072969 + 3 ^ 40 * 8136975 * 2
def baseEnd_8136975 : Nat := 4178179248618406781591239

theorem tailTrace_8136975 : CollatzResearch.WordTrace tailWord_8136975 prefixEnd_8136975 4178179248618406781591239 := by
  unfold tailWord_8136975
  simp only [CollatzResearch.WordTrace]
  refine ⟨296779859696136734536660379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197853239797424489691106919 296779859696136734536660379)
  ·
    refine ⟨445169789544205101804990569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296779859696136734536660379 445169789544205101804990569)
    ·
      refine ⟨333877342158153826353742927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445169789544205101804990569 333877342158153826353742927)
      ·
        refine ⟨500816013237230739530614391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333877342158153826353742927 500816013237230739530614391)
        ·
          refine ⟨751224019855846109295921587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500816013237230739530614391 751224019855846109295921587)
          ·
            refine ⟨1126836029783769163943882381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751224019855846109295921587 1126836029783769163943882381)
            ·
              refine ⟨422563511168913436478955893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126836029783769163943882381 422563511168913436478955893)
              ·
                refine ⟨39615329172085634669902115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422563511168913436478955893 39615329172085634669902115)
                ·
                  refine ⟨59422993758128452004853173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39615329172085634669902115 59422993758128452004853173)
                  ·
                    refine ⟨5570905664824542375454985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59422993758128452004853173 5570905664824542375454985)
                    ·
                      refine ⟨4178179248618406781591239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570905664824542375454985 4178179248618406781591239)
                      ·
                        rfl

theorem cell23_8136975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5, 2].length) (baseStart_8136975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8136975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8136975 prefixEnd_8136975 := by exact prefixLift 8136975
  have htrace : WordTrace (prefixWord ++ tailWord_8136975) baseStart_8136975 baseEnd_8136975 := by
    simpa [prefixWord, tailWord_8136975, baseEnd_8136975] using wordTrace_append hprefix tailTrace_8136975
  have hstable : (prefixWord ++ tailWord_8136975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8136975).length < 2 ^ (prefixWord ++ tailWord_8136975).sum := by decide
  have hdescent : baseEnd_8136975 < baseStart_8136975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8136975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137022 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_8137022 : Nat := 118140960795 + 8137022 * 2 ^ 59
def prefixEnd_8137022 : Nat := 4983230072969 + 3 ^ 40 * 8137022 * 2
def baseEnd_8137022 : Nat := 4178203382209168097703523

theorem tailTrace_8137022 : CollatzResearch.WordTrace tailWord_8137022 prefixEnd_8137022 4178203382209168097703523 := by
  unfold tailWord_8137022
  simp only [CollatzResearch.WordTrace]
  refine ⟨37097696740870807695452665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197854382617977641042414213 37097696740870807695452665)
  ·
    refine ⟨27823272555653105771589499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37097696740870807695452665 27823272555653105771589499)
    ·
      refine ⟨41734908833479658657384249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27823272555653105771589499 41734908833479658657384249)
      ·
        refine ⟨31301181625109743993038187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41734908833479658657384249 31301181625109743993038187)
        ·
          refine ⟨46951772437664615989557281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31301181625109743993038187 46951772437664615989557281)
          ·
            refine ⟨35213829328248461992167961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46951772437664615989557281 35213829328248461992167961)
            ·
              refine ⟨26410371996186346494125971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35213829328248461992167961 26410371996186346494125971)
              ·
                refine ⟨39615557994279519741188957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26410371996186346494125971 39615557994279519741188957)
                ·
                  refine ⟨14855834247854819902945859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39615557994279519741188957 14855834247854819902945859)
                  ·
                    refine ⟨22283751371782229854418789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14855834247854819902945859 22283751371782229854418789)
                    ·
                      refine ⟨4178203382209168097703523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22283751371782229854418789 4178203382209168097703523)
                      ·
                        rfl

theorem cell23_8137022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_8137022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137022 prefixEnd_8137022 := by exact prefixLift 8137022
  have htrace : WordTrace (prefixWord ++ tailWord_8137022) baseStart_8137022 baseEnd_8137022 := by
    simpa [prefixWord, tailWord_8137022, baseEnd_8137022] using wordTrace_append hprefix tailTrace_8137022
  have hstable : (prefixWord ++ tailWord_8137022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137022).length < 2 ^ (prefixWord ++ tailWord_8137022).sum := by decide
  have hdescent : baseEnd_8137022 < baseStart_8137022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137045 : List Nat := [1, 3, 2, 2, 4, 1, 10]
def baseStart_8137045 : Nat := 118140960795 + 8137045 * 2 ^ 59
def prefixEnd_8137045 : Nat := 4983230072969 + 3 ^ 40 * 8137045 * 2
def baseEnd_8137045 : Nat := 51582903608200265527357

theorem tailTrace_8137045 : CollatzResearch.WordTrace tailWord_8137045 prefixEnd_8137045 51582903608200265527357 := by
  unfold tailWord_8137045
  simp only [CollatzResearch.WordTrace]
  refine ⟨296782412805883136491708589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197854941870588757661139059 296782412805883136491708589)
  ·
    refine ⟨111293404802206176184390721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296782412805883136491708589 111293404802206176184390721)
    ·
      refine ⟨83470053601654632138293041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111293404802206176184390721 83470053601654632138293041)
      ·
        refine ⟨62602540201240974103719781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83470053601654632138293041 62602540201240974103719781)
        ·
          refine ⟨11737976287732682644447459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62602540201240974103719781 11737976287732682644447459)
          ·
            refine ⟨17606964431599023966671189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737976287732682644447459 17606964431599023966671189)
            ·
              refine ⟨51582903608200265527357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17606964431599023966671189 51582903608200265527357)
              ·
                rfl

theorem cell23_8137045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 10].length) (baseStart_8137045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137045 prefixEnd_8137045 := by exact prefixLift 8137045
  have htrace : WordTrace (prefixWord ++ tailWord_8137045) baseStart_8137045 baseEnd_8137045 := by
    simpa [prefixWord, tailWord_8137045, baseEnd_8137045] using wordTrace_append hprefix tailTrace_8137045
  have hstable : (prefixWord ++ tailWord_8137045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137045).length < 2 ^ (prefixWord ++ tailWord_8137045).sum := by decide
  have hdescent : baseEnd_8137045 < baseStart_8137045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137055 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_8137055 : Nat := 118140960795 + 8137055 * 2 ^ 59
def prefixEnd_8137055 : Nat := 4983230072969 + 3 ^ 40 * 8137055 * 2
def baseEnd_8137055 : Nat := 4178220327070766468590871

theorem tailTrace_8137055 : CollatzResearch.WordTrace tailWord_8137055 prefixEnd_8137055 4178220327070766468590871 := by
  unfold tailWord_8137055
  simp only [CollatzResearch.WordTrace]
  refine ⟨296782777535846908199572619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197855185023897938799715079 296782777535846908199572619)
  ·
    refine ⟨445174166303770362299358929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296782777535846908199572619 445174166303770362299358929)
    ·
      refine ⟨333880624727827771724519197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445174166303770362299358929 333880624727827771724519197)
      ·
        refine ⟨125205234272935414396694699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333880624727827771724519197 125205234272935414396694699)
        ·
          refine ⟨187807851409403121595042049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125205234272935414396694699 187807851409403121595042049)
          ·
            refine ⟨140855888557052341196281537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187807851409403121595042049 140855888557052341196281537)
            ·
              refine ⟨105641916417789255897211153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140855888557052341196281537 105641916417789255897211153)
              ·
                refine ⟨79231437313341941922908365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105641916417789255897211153 79231437313341941922908365)
                ·
                  refine ⟨29711788992503228221090637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79231437313341941922908365 29711788992503228221090637)
                  ·
                    refine ⟨11141920872188710582908989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29711788992503228221090637 11141920872188710582908989)
                    ·
                      refine ⟨4178220327070766468590871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141920872188710582908989 4178220327070766468590871)
                      ·
                        rfl

theorem cell23_8137055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_8137055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137055 prefixEnd_8137055 := by exact prefixLift 8137055
  have htrace : WordTrace (prefixWord ++ tailWord_8137055) baseStart_8137055 baseEnd_8137055 := by
    simpa [prefixWord, tailWord_8137055, baseEnd_8137055] using wordTrace_append hprefix tailTrace_8137055
  have hstable : (prefixWord ++ tailWord_8137055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137055).length < 2 ^ (prefixWord ++ tailWord_8137055).sum := by decide
  have hdescent : baseEnd_8137055 < baseStart_8137055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137056 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 3, 2, 2]
def baseStart_8137056 : Nat := 118140960795 + 8137056 * 2 ^ 59
def prefixEnd_8137056 : Nat := 4983230072969 + 3 ^ 40 * 8137056 * 2
def baseEnd_8137056 : Nat := 4178220840551420964678367

theorem tailTrace_8137056 : CollatzResearch.WordTrace tailWord_8137056 prefixEnd_8137056 4178220840551420964678367 := by
  unfold tailWord_8137056
  simp only [CollatzResearch.WordTrace]
  refine ⟨148391407004421642685179511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197855209339228856913572681 148391407004421642685179511)
  ·
    refine ⟨222587110506632464027769267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148391407004421642685179511 222587110506632464027769267)
    ·
      refine ⟨333880665759948696041653901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222587110506632464027769267 333880665759948696041653901)
      ·
        refine ⟨125205249659980761015620213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333880665759948696041653901 125205249659980761015620213)
        ·
          refine ⟨11737992155623196345214395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125205249659980761015620213 11737992155623196345214395)
          ·
            refine ⟨17606988233434794517821593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737992155623196345214395 17606988233434794517821593)
            ·
              refine ⟨13205241175076095888366195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17606988233434794517821593 13205241175076095888366195)
              ·
                refine ⟨19807861762614143832549293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13205241175076095888366195 19807861762614143832549293)
                ·
                  refine ⟨7427948160980303937205985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19807861762614143832549293 7427948160980303937205985)
                  ·
                    refine ⟨5570961120735227952904489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7427948160980303937205985 5570961120735227952904489)
                    ·
                      refine ⟨4178220840551420964678367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570961120735227952904489 4178220840551420964678367)
                      ·
                        rfl

theorem cell23_8137056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_8137056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137056 prefixEnd_8137056 := by exact prefixLift 8137056
  have htrace : WordTrace (prefixWord ++ tailWord_8137056) baseStart_8137056 baseEnd_8137056 := by
    simpa [prefixWord, tailWord_8137056, baseEnd_8137056] using wordTrace_append hprefix tailTrace_8137056
  have hstable : (prefixWord ++ tailWord_8137056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137056).length < 2 ^ (prefixWord ++ tailWord_8137056).sum := by decide
  have hdescent : baseEnd_8137056 < baseStart_8137056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137066 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_8137066 : Nat := 118140960795 + 8137066 * 2 ^ 59
def prefixEnd_8137066 : Nat := 4983230072969 + 3 ^ 40 * 8137066 * 2
def baseEnd_8137066 : Nat := 1392741991785988641851107

theorem tailTrace_8137066 : CollatzResearch.WordTrace tailWord_8137066 prefixEnd_8137066 1392741991785988641851107 := by
  unfold tailWord_8137066
  simp only [CollatzResearch.WordTrace]
  refine ⟨74195794684701764269555763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197855452492538038052148701 74195794684701764269555763)
  ·
    refine ⟨111293692027052646404333645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74195794684701764269555763 111293692027052646404333645)
    ·
      refine ⟨41735134510144742401625117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111293692027052646404333645 41735134510144742401625117)
      ·
        refine ⟨15650675441304278400609419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41735134510144742401625117 15650675441304278400609419)
        ·
          refine ⟨23476013161956417600914129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15650675441304278400609419 23476013161956417600914129)
          ·
            refine ⟨17607009871467313200685597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23476013161956417600914129 17607009871467313200685597)
            ·
              refine ⟨6602628701800242450257099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17607009871467313200685597 6602628701800242450257099)
              ·
                refine ⟨9903943052700363675385649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602628701800242450257099 9903943052700363675385649)
                ·
                  refine ⟨7427957289525272756539237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9903943052700363675385649 7427957289525272756539237)
                  ·
                    refine ⟨1392741991785988641851107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7427957289525272756539237 1392741991785988641851107)
                    ·
                      rfl

theorem cell23_8137066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_8137066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137066 prefixEnd_8137066 := by exact prefixLift 8137066
  have htrace : WordTrace (prefixWord ++ tailWord_8137066) baseStart_8137066 baseEnd_8137066 := by
    simpa [prefixWord, tailWord_8137066, baseEnd_8137066] using wordTrace_append hprefix tailTrace_8137066
  have hstable : (prefixWord ++ tailWord_8137066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137066).length < 2 ^ (prefixWord ++ tailWord_8137066).sum := by decide
  have hdescent : baseEnd_8137066 < baseStart_8137066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137072 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_8137072 : Nat := 118140960795 + 8137072 * 2 ^ 59
def prefixEnd_8137072 : Nat := 4983230072969 + 3 ^ 40 * 8137072 * 2
def baseEnd_8137072 : Nat := 4178229056241892902078293

theorem tailTrace_8137072 : CollatzResearch.WordTrace tailWord_8137072 prefixEnd_8137072 4178229056241892902078293 := by
  unfold tailWord_8137072
  simp only [CollatzResearch.WordTrace]
  refine ⟨148391698788392660051470735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197855598384523546735294313 148391698788392660051470735)
  ·
    refine ⟨222587548182588990077206103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148391698788392660051470735 222587548182588990077206103)
    ·
      refine ⟨333881322273883485115809155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222587548182588990077206103 333881322273883485115809155)
      ·
        refine ⟨500821983410825227673713733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333881322273883485115809155 500821983410825227673713733)
        ·
          refine ⟨93904121889529730188821325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500821983410825227673713733 93904121889529730188821325)
          ·
            refine ⟨35214045708573648820807997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93904121889529730188821325 35214045708573648820807997)
            ·
              refine ⟨13205267140715118307802999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35214045708573648820807997 13205267140715118307802999)
              ·
                refine ⟨19807900711072677461704499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13205267140715118307802999 19807900711072677461704499)
                ·
                  refine ⟨29711851066609016192556749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19807900711072677461704499 29711851066609016192556749)
                  ·
                    refine ⟨11141944149978381072208781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29711851066609016192556749 11141944149978381072208781)
                    ·
                      refine ⟨4178229056241892902078293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141944149978381072208781 4178229056241892902078293)
                      ·
                        rfl

theorem cell23_8137072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_8137072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137072 prefixEnd_8137072 := by exact prefixLift 8137072
  have htrace : WordTrace (prefixWord ++ tailWord_8137072) baseStart_8137072 baseEnd_8137072 := by
    simpa [prefixWord, tailWord_8137072, baseEnd_8137072] using wordTrace_append hprefix tailTrace_8137072
  have hstable : (prefixWord ++ tailWord_8137072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137072).length < 2 ^ (prefixWord ++ tailWord_8137072).sum := by decide
  have hdescent : baseEnd_8137072 < baseStart_8137072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137085 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_8137085 : Nat := 118140960795 + 8137085 * 2 ^ 59
def prefixEnd_8137085 : Nat := 4983230072969 + 3 ^ 40 * 8137085 * 2
def baseEnd_8137085 : Nat := 4178235731490401351215733

theorem tailTrace_8137085 : CollatzResearch.WordTrace tailWord_8137085 prefixEnd_8137085 4178235731490401351215733 := by
  unfold tailWord_8137085
  simp only [CollatzResearch.WordTrace]
  refine ⟨296783871725738223323164709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197855914483825482215443139 296783871725738223323164709)
  ·
    refine ⟨55646975948575916873093383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296783871725738223323164709 55646975948575916873093383)
    ·
      refine ⟨83470463922863875309640075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55646975948575916873093383 83470463922863875309640075)
      ·
        refine ⟨125205695884295812964460113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83470463922863875309640075 125205695884295812964460113)
        ·
          refine ⟨93904271913221859723345085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125205695884295812964460113 93904271913221859723345085)
          ·
            refine ⟨35214101967458197396254407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93904271913221859723345085 35214101967458197396254407)
            ·
              refine ⟨52821152951187296094381611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35214101967458197396254407 52821152951187296094381611)
              ·
                refine ⟨79231729426780944141572417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52821152951187296094381611 79231729426780944141572417)
                ·
                  refine ⟨59423797070085708106179313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79231729426780944141572417 59423797070085708106179313)
                  ·
                    refine ⟨44567847802564281079634485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59423797070085708106179313 44567847802564281079634485)
                    ·
                      refine ⟨4178235731490401351215733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44567847802564281079634485 4178235731490401351215733)
                      ·
                        rfl

theorem cell23_8137085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_8137085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137085 prefixEnd_8137085 := by exact prefixLift 8137085
  have htrace : WordTrace (prefixWord ++ tailWord_8137085) baseStart_8137085 baseEnd_8137085 := by
    simpa [prefixWord, tailWord_8137085, baseEnd_8137085] using wordTrace_append hprefix tailTrace_8137085
  have hstable : (prefixWord ++ tailWord_8137085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137085).length < 2 ^ (prefixWord ++ tailWord_8137085).sum := by decide
  have hdescent : baseEnd_8137085 < baseStart_8137085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137089 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_8137089 : Nat := 118140960795 + 8137089 * 2 ^ 59
def prefixEnd_8137089 : Nat := 4983230072969 + 3 ^ 40 * 8137089 * 2
def baseEnd_8137089 : Nat := 4178237785413019335565715

theorem tailTrace_8137089 : CollatzResearch.WordTrace tailWord_8137089 prefixEnd_8137089 4178237785413019335565715 := by
  unfold tailWord_8137089
  simp only [CollatzResearch.WordTrace]
  refine ⟨296784017617723732006310321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197856011745149154670873547 296784017617723732006310321)
  ·
    refine ⟨222588013213292799004732741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296784017617723732006310321 222588013213292799004732741)
    ·
      refine ⟨41735252477492399813387389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222588013213292799004732741 41735252477492399813387389)
      ·
        refine ⟨15650719679059649930020271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41735252477492399813387389 15650719679059649930020271)
        ·
          refine ⟨23476079518589474895030407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15650719679059649930020271 23476079518589474895030407)
          ·
            refine ⟨35214119277884212342545611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23476079518589474895030407 35214119277884212342545611)
            ·
              refine ⟨52821178916826318513818417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35214119277884212342545611 52821178916826318513818417)
              ·
                refine ⟨39615884187619738885363813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52821178916826318513818417 39615884187619738885363813)
                ·
                  refine ⟨7427978285178701041005715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39615884187619738885363813 7427978285178701041005715)
                  ·
                    refine ⟨11141967427768051561508573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7427978285178701041005715 11141967427768051561508573)
                    ·
                      refine ⟨4178237785413019335565715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11141967427768051561508573 4178237785413019335565715)
                      ·
                        rfl

theorem cell23_8137089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_8137089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137089 prefixEnd_8137089 := by exact prefixLift 8137089
  have htrace : WordTrace (prefixWord ++ tailWord_8137089) baseStart_8137089 baseEnd_8137089 := by
    simpa [prefixWord, tailWord_8137089, baseEnd_8137089] using wordTrace_append hprefix tailTrace_8137089
  have hstable : (prefixWord ++ tailWord_8137089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137089).length < 2 ^ (prefixWord ++ tailWord_8137089).sum := by decide
  have hdescent : baseEnd_8137089 < baseStart_8137089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137099 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 1, 3, 2]
def baseStart_8137099 : Nat := 118140960795 + 8137099 * 2 ^ 59
def prefixEnd_8137099 : Nat := 4983230072969 + 3 ^ 40 * 8137099 * 2
def baseEnd_8137099 : Nat := 4178242920219564296440669

theorem tailTrace_8137099 : CollatzResearch.WordTrace tailWord_8137099 prefixEnd_8137099 4178242920219564296440669 := by
  unfold tailWord_8137099
  simp only [CollatzResearch.WordTrace]
  refine ⟨296784382347687503714174351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197856254898458335809449567 296784382347687503714174351)
  ·
    refine ⟨445176573521531255571261527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296784382347687503714174351 445176573521531255571261527)
    ·
      refine ⟨667764860282296883356892291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445176573521531255571261527 667764860282296883356892291)
      ·
        refine ⟨1001647290423445325035338437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667764860282296883356892291 1001647290423445325035338437)
        ·
          refine ⟨187808866954395998444125957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1001647290423445325035338437 187808866954395998444125957)
          ·
            refine ⟨35214162553949249708273617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187808866954395998444125957 35214162553949249708273617)
            ·
              refine ⟨26410621915461937281205213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35214162553949249708273617 26410621915461937281205213)
              ·
                refine ⟨9903983218298226480451955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26410621915461937281205213 9903983218298226480451955)
                ·
                  refine ⟨14855974827447339720677933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9903983218298226480451955 14855974827447339720677933)
                  ·
                    refine ⟨5570990560292752395254225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14855974827447339720677933 5570990560292752395254225)
                    ·
                      refine ⟨4178242920219564296440669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5570990560292752395254225 4178242920219564296440669)
                      ·
                        rfl

theorem cell23_8137099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 3, 2].length) (baseStart_8137099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137099 prefixEnd_8137099 := by exact prefixLift 8137099
  have htrace : WordTrace (prefixWord ++ tailWord_8137099) baseStart_8137099 baseEnd_8137099 := by
    simpa [prefixWord, tailWord_8137099, baseEnd_8137099] using wordTrace_append hprefix tailTrace_8137099
  have hstable : (prefixWord ++ tailWord_8137099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137099).length < 2 ^ (prefixWord ++ tailWord_8137099).sum := by decide
  have hdescent : baseEnd_8137099 < baseStart_8137099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137125 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_8137125 : Nat := 118140960795 + 8137125 * 2 ^ 59
def prefixEnd_8137125 : Nat := 4983230072969 + 3 ^ 40 * 8137125 * 2
def baseEnd_8137125 : Nat := 4178256270716581194715549

theorem tailTrace_8137125 : CollatzResearch.WordTrace tailWord_8137125 prefixEnd_8137125 4178256270716581194715549 := by
  unfold tailWord_8137125
  simp only [CollatzResearch.WordTrace]
  refine ⟨296785330645593310154620829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197856887097062206769747219 296785330645593310154620829)
  ·
    refine ⟨111294498992097491307982811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296785330645593310154620829 111294498992097491307982811)
    ·
      refine ⟨166941748488146236961974217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111294498992097491307982811 166941748488146236961974217)
      ·
        refine ⟨125206311366109677721480663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166941748488146236961974217 125206311366109677721480663)
        ·
          refine ⟨187809467049164516582220995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125206311366109677721480663 187809467049164516582220995)
          ·
            refine ⟨281714200573746774873331493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187809467049164516582220995 281714200573746774873331493)
            ·
              refine ⟨52821412607577520288749655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281714200573746774873331493 52821412607577520288749655)
              ·
                refine ⟨79232118911366280433124483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52821412607577520288749655 79232118911366280433124483)
                ·
                  refine ⟨118848178367049420649686725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79232118911366280433124483 118848178367049420649686725)
                  ·
                    refine ⟨22284033443821766371816261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118848178367049420649686725 22284033443821766371816261)
                    ·
                      refine ⟨4178256270716581194715549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22284033443821766371816261 4178256270716581194715549)
                      ·
                        rfl

theorem cell23_8137125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_8137125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137125 prefixEnd_8137125 := by exact prefixLift 8137125
  have htrace : WordTrace (prefixWord ++ tailWord_8137125) baseStart_8137125 baseEnd_8137125 := by
    simpa [prefixWord, tailWord_8137125, baseEnd_8137125] using wordTrace_append hprefix tailTrace_8137125
  have hstable : (prefixWord ++ tailWord_8137125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137125).length < 2 ^ (prefixWord ++ tailWord_8137125).sum := by decide
  have hdescent : baseEnd_8137125 < baseStart_8137125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137152 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 5]
def baseStart_8137152 : Nat := 118140960795 + 8137152 * 2 ^ 59
def prefixEnd_8137152 : Nat := 4983230072969 + 3 ^ 40 * 8137152 * 2
def baseEnd_8137152 : Nat := 464252237188250287675325

theorem tailTrace_8137152 : CollatzResearch.WordTrace tailWord_8137152 prefixEnd_8137152 464252237188250287675325 := by
  unfold tailWord_8137152
  simp only [CollatzResearch.WordTrace]
  refine ⟨148393157708247746882926855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197857543610996995843902473 148393157708247746882926855)
  ·
    refine ⟨222589736562371620324390283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148393157708247746882926855 222589736562371620324390283)
    ·
      refine ⟨333884604843557430486585425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222589736562371620324390283 333884604843557430486585425)
      ·
        refine ⟨250413453632668072864939069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333884604843557430486585425 250413453632668072864939069)
        ·
          refine ⟨93905045112250527324352151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250413453632668072864939069 93905045112250527324352151)
          ·
            refine ⟨140857567668375790986528227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93905045112250527324352151 140857567668375790986528227)
            ·
              refine ⟨211286351502563686479792341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140857567668375790986528227 211286351502563686479792341)
              ·
                refine ⟨4952023863341336401870133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 211286351502563686479792341 4952023863341336401870133)
                ·
                  refine ⟨464252237188250287675325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4952023863341336401870133 464252237188250287675325)
                  ·
                    rfl

theorem cell23_8137152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 5].length) (baseStart_8137152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137152 prefixEnd_8137152 := by exact prefixLift 8137152
  have htrace : WordTrace (prefixWord ++ tailWord_8137152) baseStart_8137152 baseEnd_8137152 := by
    simpa [prefixWord, tailWord_8137152, baseEnd_8137152] using wordTrace_append hprefix tailTrace_8137152
  have hstable : (prefixWord ++ tailWord_8137152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137152).length < 2 ^ (prefixWord ++ tailWord_8137152).sum := by decide
  have hdescent : baseEnd_8137152 < baseStart_8137152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137162 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_8137162 : Nat := 118140960795 + 8137162 * 2 ^ 59
def prefixEnd_8137162 : Nat := 4983230072969 + 3 ^ 40 * 8137162 * 2
def baseEnd_8137162 : Nat := 4178275269500797549952879

theorem tailTrace_8137162 : CollatzResearch.WordTrace tailWord_8137162 prefixEnd_8137162 4178275269500797549952879 := by
  unfold tailWord_8137162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74196670036614816368429435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197857786764306176982478493 74196670036614816368429435)
  ·
    refine ⟨111295005054922224552644153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74196670036614816368429435 111295005054922224552644153)
    ·
      refine ⟨83471253791191668414483115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111295005054922224552644153 83471253791191668414483115)
      ·
        refine ⟨125206880686787502621724673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83471253791191668414483115 125206880686787502621724673)
        ·
          refine ⟨93905160515090626966293505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125206880686787502621724673 93905160515090626966293505)
          ·
            refine ⟨70428870386317970224720129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93905160515090626966293505 70428870386317970224720129)
            ·
              refine ⟨52821652789738477668540097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70428870386317970224720129 52821652789738477668540097)
              ·
                refine ⟨39616239592303858251405073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52821652789738477668540097 39616239592303858251405073)
                ·
                  refine ⟨29712179694227893688553805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39616239592303858251405073 29712179694227893688553805)
                  ·
                    refine ⟨11142067385335460133207677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29712179694227893688553805 11142067385335460133207677)
                    ·
                      refine ⟨4178275269500797549952879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11142067385335460133207677 4178275269500797549952879)
                      ·
                        rfl

theorem cell23_8137162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_8137162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137162 prefixEnd_8137162 := by exact prefixLift 8137162
  have htrace : WordTrace (prefixWord ++ tailWord_8137162) baseStart_8137162 baseEnd_8137162 := by
    simpa [prefixWord, tailWord_8137162, baseEnd_8137162] using wordTrace_append hprefix tailTrace_8137162
  have hstable : (prefixWord ++ tailWord_8137162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137162).length < 2 ^ (prefixWord ++ tailWord_8137162).sum := by decide
  have hdescent : baseEnd_8137162 < baseStart_8137162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137186 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_8137186 : Nat := 118140960795 + 8137186 * 2 ^ 59
def prefixEnd_8137186 : Nat := 4983230072969 + 3 ^ 40 * 8137186 * 2
def baseEnd_8137186 : Nat := 464254177004056161783641

theorem tailTrace_8137186 : CollatzResearch.WordTrace tailWord_8137186 prefixEnd_8137186 464254177004056161783641 := by
  unfold tailWord_8137186
  simp only [CollatzResearch.WordTrace]
  refine ⟨74196888874593079393147853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197858370332248211715060941 74196888874593079393147853)
  ·
    refine ⟨27823833327972404772430445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74196888874593079393147853 27823833327972404772430445)
    ·
      refine ⟨10433937497989651789661417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27823833327972404772430445 10433937497989651789661417)
      ·
        refine ⟨7825453123492238842246063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10433937497989651789661417 7825453123492238842246063)
        ·
          refine ⟨11738179685238358263369095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825453123492238842246063 11738179685238358263369095)
          ·
            refine ⟨17607269527857537395053643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11738179685238358263369095 17607269527857537395053643)
            ·
              refine ⟨26410904291786306092580465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17607269527857537395053643 26410904291786306092580465)
              ·
                refine ⟨19808178218839729569435349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26410904291786306092580465 19808178218839729569435349)
                ·
                  refine ⟨464254177004056161783641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19808178218839729569435349 464254177004056161783641)
                  ·
                    rfl

theorem cell23_8137186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_8137186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137186 prefixEnd_8137186 := by exact prefixLift 8137186
  have htrace : WordTrace (prefixWord ++ tailWord_8137186) baseStart_8137186 baseEnd_8137186 := by
    simpa [prefixWord, tailWord_8137186, baseEnd_8137186] using wordTrace_append hprefix tailTrace_8137186
  have hstable : (prefixWord ++ tailWord_8137186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137186).length < 2 ^ (prefixWord ++ tailWord_8137186).sum := by decide
  have hdescent : baseEnd_8137186 < baseStart_8137186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137212 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_8137212 : Nat := 118140960795 + 8137212 * 2 ^ 59
def prefixEnd_8137212 : Nat := 4983230072969 + 3 ^ 40 * 8137212 * 2
def baseEnd_8137212 : Nat := 1392766981177840784775883

theorem tailTrace_8137212 : CollatzResearch.WordTrace tailWord_8137212 prefixEnd_8137212 1392766981177840784775883 := by
  unfold tailWord_8137212
  simp only [CollatzResearch.WordTrace]
  refine ⟨148394251898139062006518945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197859002530852082675358593 148394251898139062006518945)
  ·
    refine ⟨111295688923604296504889209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148394251898139062006518945 111295688923604296504889209)
    ·
      refine ⟨83471766692703222378666907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111295688923604296504889209 83471766692703222378666907)
      ·
        refine ⟨125207650039054833568000361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83471766692703222378666907 125207650039054833568000361)
        ·
          refine ⟨93905737529291125176000271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125207650039054833568000361 93905737529291125176000271)
          ·
            refine ⟨140858606293936687764000407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93905737529291125176000271 140858606293936687764000407)
            ·
              refine ⟨211287909440905031646000611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140858606293936687764000407 211287909440905031646000611)
              ·
                refine ⟨316931864161357547469000917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211287909440905031646000611 316931864161357547469000917)
                ·
                  refine ⟨7428090566281817518804709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 316931864161357547469000917 7428090566281817518804709)
                  ·
                    refine ⟨1392766981177840784775883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428090566281817518804709 1392766981177840784775883)
                    ·
                      rfl

theorem cell23_8137212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_8137212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137212 prefixEnd_8137212 := by exact prefixLift 8137212
  have htrace : WordTrace (prefixWord ++ tailWord_8137212) baseStart_8137212 baseEnd_8137212 := by
    simpa [prefixWord, tailWord_8137212, baseEnd_8137212] using wordTrace_append hprefix tailTrace_8137212
  have hstable : (prefixWord ++ tailWord_8137212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137212).length < 2 ^ (prefixWord ++ tailWord_8137212).sum := by decide
  have hdescent : baseEnd_8137212 < baseStart_8137212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137215 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_8137215 : Nat := 118140960795 + 8137215 * 2 ^ 59
def prefixEnd_8137215 : Nat := 4983230072969 + 3 ^ 40 * 8137215 * 2
def baseEnd_8137215 : Nat := 4178302483975485842590135

theorem tailTrace_8137215 : CollatzResearch.WordTrace tailWord_8137215 prefixEnd_8137215 4178302483975485842590135 := by
  unfold tailWord_8137215
  simp only [CollatzResearch.WordTrace]
  refine ⟨296788613215267255525397099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197859075476844837016931399 296788613215267255525397099)
  ·
    refine ⟨445182919822900883288095649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296788613215267255525397099 445182919822900883288095649)
    ·
      refine ⟨333887189867175662466071737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445182919822900883288095649 333887189867175662466071737)
      ·
        refine ⟨250415392400381746849553803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333887189867175662466071737 250415392400381746849553803)
        ·
          refine ⟨375623088600572620274330705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250415392400381746849553803 375623088600572620274330705)
          ·
            refine ⟨281717316450429465205748029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375623088600572620274330705 281717316450429465205748029)
            ·
              refine ⟨105643993668911049452155511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281717316450429465205748029 105643993668911049452155511)
              ·
                refine ⟨158465990503366574178233267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105643993668911049452155511 158465990503366574178233267)
                ·
                  refine ⟨237698985755049861267349901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158465990503366574178233267 237698985755049861267349901)
                  ·
                    refine ⟨89137119658143697975256213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237698985755049861267349901 89137119658143697975256213)
                    ·
                      refine ⟨4178302483975485842590135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89137119658143697975256213 4178302483975485842590135)
                      ·
                        rfl

theorem cell23_8137215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_8137215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137215 prefixEnd_8137215 := by exact prefixLift 8137215
  have htrace : WordTrace (prefixWord ++ tailWord_8137215) baseStart_8137215 baseEnd_8137215 := by
    simpa [prefixWord, tailWord_8137215, baseEnd_8137215] using wordTrace_append hprefix tailTrace_8137215
  have hstable : (prefixWord ++ tailWord_8137215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137215).length < 2 ^ (prefixWord ++ tailWord_8137215).sum := by decide
  have hdescent : baseEnd_8137215 < baseStart_8137215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137242 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_8137242 : Nat := 118140960795 + 8137242 * 2 ^ 59
def prefixEnd_8137242 : Nat := 4983230072969 + 3 ^ 40 * 8137242 * 2
def baseEnd_8137242 : Nat := 464257371994795248550279

theorem tailTrace_8137242 : CollatzResearch.WordTrace tailWord_8137242 prefixEnd_8137242 464257371994795248550279 := by
  unfold tailWord_8137242
  simp only [CollatzResearch.WordTrace]
  refine ⟨74197399496542359784157495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197859731990779626091086653 74197399496542359784157495)
  ·
    refine ⟨111296099244813539676236243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74197399496542359784157495 111296099244813539676236243)
    ·
      refine ⟨166944148867220309514354365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111296099244813539676236243 166944148867220309514354365)
      ·
        refine ⟨62604055825207616067882887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166944148867220309514354365 62604055825207616067882887)
        ·
          refine ⟨93906083737811424101824331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62604055825207616067882887 93906083737811424101824331)
          ·
            refine ⟨140859125606717136152736497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93906083737811424101824331 140859125606717136152736497)
            ·
              refine ⟨105644344205037852114552373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140859125606717136152736497 105644344205037852114552373)
              ·
                refine ⟨9904157269222298635739285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105644344205037852114552373 9904157269222298635739285)
                ·
                  refine ⟨464257371994795248550279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9904157269222298635739285 464257371994795248550279)
                  ·
                    rfl

theorem cell23_8137242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_8137242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137242 prefixEnd_8137242 := by exact prefixLift 8137242
  have htrace : WordTrace (prefixWord ++ tailWord_8137242) baseStart_8137242 baseEnd_8137242 := by
    simpa [prefixWord, tailWord_8137242, baseEnd_8137242] using wordTrace_append hprefix tailTrace_8137242
  have hstable : (prefixWord ++ tailWord_8137242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137242).length < 2 ^ (prefixWord ++ tailWord_8137242).sum := by decide
  have hdescent : baseEnd_8137242 < baseStart_8137242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137293 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 6]
def baseStart_8137293 : Nat := 118140960795 + 8137293 * 2 ^ 59
def prefixEnd_8137293 : Nat := 4983230072969 + 3 ^ 40 * 8137293 * 2
def baseEnd_8137293 : Nat := 464260281718504059712753

theorem tailTrace_8137293 : CollatzResearch.WordTrace tailWord_8137293 prefixEnd_8137293 464260281718504059712753 := by
  unfold tailWord_8137293
  simp only [CollatzResearch.WordTrace]
  refine ⟨296791458108984674846736533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197860972072656449897824355 296791458108984674846736533)
  ·
    refine ⟨13912099598858656633440775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296791458108984674846736533 13912099598858656633440775)
    ·
      refine ⟨20868149398287984950161163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13912099598858656633440775 20868149398287984950161163)
      ·
        refine ⟨31302224097431977425241745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20868149398287984950161163 31302224097431977425241745)
        ·
          refine ⟨23476668073073983068931309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31302224097431977425241745 23476668073073983068931309)
          ·
            refine ⟨8803750527402743650849241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23476668073073983068931309 8803750527402743650849241)
            ·
              refine ⟨6602812895552057738136931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8803750527402743650849241 6602812895552057738136931)
              ·
                refine ⟨9904219343328086607205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602812895552057738136931 9904219343328086607205397)
                ·
                  refine ⟨464260281718504059712753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9904219343328086607205397 464260281718504059712753)
                  ·
                    rfl

theorem cell23_8137293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_8137293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137293 prefixEnd_8137293 := by exact prefixLift 8137293
  have htrace : WordTrace (prefixWord ++ tailWord_8137293) baseStart_8137293 baseEnd_8137293 := by
    simpa [prefixWord, tailWord_8137293, baseEnd_8137293] using wordTrace_append hprefix tailTrace_8137293
  have hstable : (prefixWord ++ tailWord_8137293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137293).length < 2 ^ (prefixWord ++ tailWord_8137293).sum := by decide
  have hdescent : baseEnd_8137293 < baseStart_8137293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137312 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_8137312 : Nat := 118140960795 + 8137312 * 2 ^ 59
def prefixEnd_8137312 : Nat := 4983230072969 + 3 ^ 40 * 8137312 * 2
def baseEnd_8137312 : Nat := 4178352291598971963077189

theorem tailTrace_8137312 : CollatzResearch.WordTrace tailWord_8137312 prefixEnd_8137312 4178352291598971963077189 := by
  unfold tailWord_8137312
  simp only [CollatzResearch.WordTrace]
  refine ⟨148396075547957920545839095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197861434063943894061118793 148396075547957920545839095)
  ·
    refine ⟨222594113321936880818758643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148396075547957920545839095 222594113321936880818758643)
    ·
      refine ⟨333891169982905321228137965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222594113321936880818758643 333891169982905321228137965)
      ·
        refine ⟨125209188743589495460551737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333891169982905321228137965 125209188743589495460551737)
        ·
          refine ⟨93906891557692121595413803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125209188743589495460551737 93906891557692121595413803)
          ·
            refine ⟨140860337336538182393120705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93906891557692121595413803 140860337336538182393120705)
            ·
              refine ⟨105645253002403636794840529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140860337336538182393120705 105645253002403636794840529)
              ·
                refine ⟨79233939751802727596130397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105645253002403636794840529 79233939751802727596130397)
                ·
                  refine ⟨29712727406926022848548899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79233939751802727596130397 29712727406926022848548899)
                  ·
                    refine ⟨44569091110389034272823349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29712727406926022848548899 44569091110389034272823349)
                    ·
                      refine ⟨4178352291598971963077189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44569091110389034272823349 4178352291598971963077189)
                      ·
                        rfl

theorem cell23_8137312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_8137312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137312 prefixEnd_8137312 := by exact prefixLift 8137312
  have htrace : WordTrace (prefixWord ++ tailWord_8137312) baseStart_8137312 baseEnd_8137312 := by
    simpa [prefixWord, tailWord_8137312, baseEnd_8137312] using wordTrace_append hprefix tailTrace_8137312
  have hstable : (prefixWord ++ tailWord_8137312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137312).length < 2 ^ (prefixWord ++ tailWord_8137312).sum := by decide
  have hdescent : baseEnd_8137312 < baseStart_8137312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137349 : List Nat := [1, 3, 1, 1, 4, 4, 1, 8]
def baseStart_8137349 : Nat := 118140960795 + 8137349 * 2 ^ 59
def prefixEnd_8137349 : Nat := 4983230072969 + 3 ^ 40 * 8137349 * 2
def baseEnd_8137349 : Nat := 154754492236414382159797

theorem tailTrace_8137349 : CollatzResearch.WordTrace tailWord_8137349 prefixEnd_8137349 154754492236414382159797 := by
  unfold tailWord_8137349
  simp only [CollatzResearch.WordTrace]
  refine ⟨296793500596781796410775101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197862333731187864273850067 296793500596781796410775101)
  ·
    refine ⟨111297562723793173654040663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296793500596781796410775101 111297562723793173654040663)
    ·
      refine ⟨166946344085689760481060995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111297562723793173654040663 166946344085689760481060995)
      ·
        refine ⟨250419516128534640721591493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166946344085689760481060995 250419516128534640721591493)
        ·
          refine ⟨46953659274100245135298405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250419516128534640721591493 46953659274100245135298405)
          ·
            refine ⟨8803811113893795962868451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46953659274100245135298405 8803811113893795962868451)
            ·
              refine ⟨13205716670840693944302677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8803811113893795962868451 13205716670840693944302677)
              ·
                refine ⟨154754492236414382159797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13205716670840693944302677 154754492236414382159797)
                ·
                  rfl

theorem cell23_8137349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 8].length) (baseStart_8137349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137349 prefixEnd_8137349 := by exact prefixLift 8137349
  have htrace : WordTrace (prefixWord ++ tailWord_8137349) baseStart_8137349 baseEnd_8137349 := by
    simpa [prefixWord, tailWord_8137349, baseEnd_8137349] using wordTrace_append hprefix tailTrace_8137349
  have hstable : (prefixWord ++ tailWord_8137349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137349).length < 2 ^ (prefixWord ++ tailWord_8137349).sum := by decide
  have hdescent : baseEnd_8137349 < baseStart_8137349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137377 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_8137377 : Nat := 118140960795 + 8137377 * 2 ^ 59
def prefixEnd_8137377 : Nat := 4983230072969 + 3 ^ 40 * 8137377 * 2
def baseEnd_8137377 : Nat := 4178385667841514208764391

theorem tailTrace_8137377 : CollatzResearch.WordTrace tailWord_8137377 prefixEnd_8137377 4178385667841514208764391 := by
  unfold tailWord_8137377
  simp only [CollatzResearch.WordTrace]
  refine ⟨296794521840680357192794385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197863014560453571461862923 296794521840680357192794385)
  ·
    refine ⟨222595891380510267894595789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296794521840680357192794385 222595891380510267894595789)
    ·
      refine ⟨83473459267691350460473421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222595891380510267894595789 83473459267691350460473421)
      ·
        refine ⟨31302547225384256422677533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83473459267691350460473421 31302547225384256422677533)
        ·
          refine ⟨11738455209519096158504075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31302547225384256422677533 11738455209519096158504075)
          ·
            refine ⟨17607682814278644237756113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11738455209519096158504075 17607682814278644237756113)
            ·
              refine ⟨13205762110708983178317085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17607682814278644237756113 13205762110708983178317085)
              ·
                refine ⟨4952160791515868691868907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13205762110708983178317085 4952160791515868691868907)
                ·
                  refine ⟨7428241187273803037803361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952160791515868691868907 7428241187273803037803361)
                  ·
                    refine ⟨5571180890455352278352521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7428241187273803037803361 5571180890455352278352521)
                    ·
                      refine ⟨4178385667841514208764391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571180890455352278352521 4178385667841514208764391)
                      ·
                        rfl

theorem cell23_8137377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_8137377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137377 prefixEnd_8137377 := by exact prefixLift 8137377
  have htrace : WordTrace (prefixWord ++ tailWord_8137377) baseStart_8137377 baseEnd_8137377 := by
    simpa [prefixWord, tailWord_8137377, baseEnd_8137377] using wordTrace_append hprefix tailTrace_8137377
  have hstable : (prefixWord ++ tailWord_8137377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137377).length < 2 ^ (prefixWord ++ tailWord_8137377).sum := by decide
  have hdescent : baseEnd_8137377 < baseStart_8137377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137420 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 1, 3, 2]
def baseStart_8137420 : Nat := 118140960795 + 8137420 * 2 ^ 59
def prefixEnd_8137420 : Nat := 4983230072969 + 3 ^ 40 * 8137420 * 2
def baseEnd_8137420 : Nat := 4178407747509657540526693

theorem tailTrace_8137420 : CollatzResearch.WordTrace tailWord_8137420 prefixEnd_8137420 4178407747509657540526693 := by
  unfold tailWord_8137420
  simp only [CollatzResearch.WordTrace]
  refine ⟨148398045089762287768304857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197864060119683050357739809 148398045089762287768304857)
  ·
    refine ⟨111298533817321715826228643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148398045089762287768304857 111298533817321715826228643)
    ·
      refine ⟨166947800725982573739342965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111298533817321715826228643 166947800725982573739342965)
      ·
        refine ⟨15651356318060866288063403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166947800725982573739342965 15651356318060866288063403)
        ·
          refine ⟨23477034477091299432095105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651356318060866288063403 23477034477091299432095105)
          ·
            refine ⟨17607775857818474574071329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23477034477091299432095105 17607775857818474574071329)
            ·
              refine ⟨13205831893363855930553497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17607775857818474574071329 13205831893363855930553497)
              ·
                refine ⟨9904373920022891947915123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13205831893363855930553497 9904373920022891947915123)
                ·
                  refine ⟨14856560880034337921872685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9904373920022891947915123 14856560880034337921872685)
                  ·
                    refine ⟨5571210330012876720702257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14856560880034337921872685 5571210330012876720702257)
                    ·
                      refine ⟨4178407747509657540526693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571210330012876720702257 4178407747509657540526693)
                      ·
                        rfl

theorem cell23_8137420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_8137420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137420 prefixEnd_8137420 := by exact prefixLift 8137420
  have htrace : WordTrace (prefixWord ++ tailWord_8137420) baseStart_8137420 baseEnd_8137420 := by
    simpa [prefixWord, tailWord_8137420, baseEnd_8137420] using wordTrace_append hprefix tailTrace_8137420
  have hstable : (prefixWord ++ tailWord_8137420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137420).length < 2 ^ (prefixWord ++ tailWord_8137420).sum := by decide
  have hdescent : baseEnd_8137420 < baseStart_8137420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137436 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8137436 : Nat := 118140960795 + 8137436 * 2 ^ 59
def prefixEnd_8137436 : Nat := 4983230072969 + 3 ^ 40 * 8137436 * 2
def baseEnd_8137436 : Nat := 4178415963200129477926619

theorem tailTrace_8137436 : CollatzResearch.WordTrace tailWord_8137436 prefixEnd_8137436 4178415963200129477926619 := by
  unfold tailWord_8137436
  simp only [CollatzResearch.WordTrace]
  refine ⟨148398336873733305134596081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197864449164977740179461441 148398336873733305134596081)
  ·
    refine ⟨111298752655299978850947061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148398336873733305134596081 111298752655299978850947061)
    ·
      refine ⟨10434258061434373017276287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111298752655299978850947061 10434258061434373017276287)
      ·
        refine ⟨15651387092151559525914431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10434258061434373017276287 15651387092151559525914431)
        ·
          refine ⟨23477080638227339288871647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651387092151559525914431 23477080638227339288871647)
          ·
            refine ⟨35215620957341008933307471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23477080638227339288871647 35215620957341008933307471)
            ·
              refine ⟨52823431436011513399961207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35215620957341008933307471 52823431436011513399961207)
              ·
                refine ⟨79235147154017270099941811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52823431436011513399961207 79235147154017270099941811)
                ·
                  refine ⟨118852720731025905149912717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79235147154017270099941811 118852720731025905149912717)
                  ·
                    refine ⟨44569770274134714431217269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118852720731025905149912717 44569770274134714431217269)
                    ·
                      refine ⟨4178415963200129477926619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44569770274134714431217269 4178415963200129477926619)
                      ·
                        rfl

theorem cell23_8137436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8137436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137436 prefixEnd_8137436 := by exact prefixLift 8137436
  have htrace : WordTrace (prefixWord ++ tailWord_8137436) baseStart_8137436 baseEnd_8137436 := by
    simpa [prefixWord, tailWord_8137436, baseEnd_8137436] using wordTrace_append hprefix tailTrace_8137436
  have hstable : (prefixWord ++ tailWord_8137436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137436).length < 2 ^ (prefixWord ++ tailWord_8137436).sum := by decide
  have hdescent : baseEnd_8137436 < baseStart_8137436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137449 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_8137449 : Nat := 118140960795 + 8137449 * 2 ^ 59
def prefixEnd_8137449 : Nat := 4983230072969 + 3 ^ 40 * 8137449 * 2
def baseEnd_8137449 : Nat := 4178422638448637927064059

theorem tailTrace_8137449 : CollatzResearch.WordTrace tailWord_8137449 prefixEnd_8137449 4178422638448637927064059 := by
  unfold tailWord_8137449
  simp only [CollatzResearch.WordTrace]
  refine ⟨296797147896419513489415401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197864765264279675659610267 296797147896419513489415401)
  ·
    refine ⟨222597860922314635117061551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296797147896419513489415401 222597860922314635117061551)
    ·
      refine ⟨333896791383471952675592327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222597860922314635117061551 333896791383471952675592327)
      ·
        refine ⟨500845187075207929013388491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333896791383471952675592327 500845187075207929013388491)
        ·
          refine ⟨751267780612811893520082737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500845187075207929013388491 751267780612811893520082737)
          ·
            refine ⟨563450835459608920140062053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751267780612811893520082737 563450835459608920140062053)
            ·
              refine ⟨105647031648676672526261635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 563450835459608920140062053 105647031648676672526261635)
              ·
                refine ⟨158470547473015008789392453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105647031648676672526261635 158470547473015008789392453)
                ·
                  refine ⟨29713227651190314148011085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158470547473015008789392453 29713227651190314148011085)
                  ·
                    refine ⟨11142460369196367805504157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29713227651190314148011085 11142460369196367805504157)
                    ·
                      refine ⟨4178422638448637927064059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11142460369196367805504157 4178422638448637927064059)
                      ·
                        rfl

theorem cell23_8137449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_8137449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137449 prefixEnd_8137449 := by exact prefixLift 8137449
  have htrace : WordTrace (prefixWord ++ tailWord_8137449) baseStart_8137449 baseEnd_8137449 := by
    simpa [prefixWord, tailWord_8137449, baseEnd_8137449] using wordTrace_append hprefix tailTrace_8137449
  have hstable : (prefixWord ++ tailWord_8137449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137449).length < 2 ^ (prefixWord ++ tailWord_8137449).sum := by decide
  have hdescent : baseEnd_8137449 < baseStart_8137449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137461 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_8137461 : Nat := 118140960795 + 8137461 * 2 ^ 59
def prefixEnd_8137461 : Nat := 4983230072969 + 3 ^ 40 * 8137461 * 2
def baseEnd_8137461 : Nat := 4178428800216491880114005

theorem tailTrace_8137461 : CollatzResearch.WordTrace tailWord_8137461 prefixEnd_8137461 4178428800216491880114005 := by
  unfold tailWord_8137461
  simp only [CollatzResearch.WordTrace]
  refine ⟨296797585572376039538852237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197865057048250693025901491 296797585572376039538852237)
  ·
    refine ⟨111299094589641014827069589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296797585572376039538852237 111299094589641014827069589)
    ·
      refine ⟨5217145058889422570018887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111299094589641014827069589 5217145058889422570018887)
      ·
        refine ⟨7825717588334133855028331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217145058889422570018887 7825717588334133855028331)
        ·
          refine ⟨11738576382501200782542497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825717588334133855028331 11738576382501200782542497)
          ·
            refine ⟨8803932286875900586906873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11738576382501200782542497 8803932286875900586906873)
            ·
              refine ⟨6602949215156925440180155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8803932286875900586906873 6602949215156925440180155)
              ·
                refine ⟨9904423822735388160270233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602949215156925440180155 9904423822735388160270233)
                ·
                  refine ⟨7428317867051541120202675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9904423822735388160270233 7428317867051541120202675)
                  ·
                    refine ⟨11142476800577311680304013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7428317867051541120202675 11142476800577311680304013)
                    ·
                      refine ⟨4178428800216491880114005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11142476800577311680304013 4178428800216491880114005)
                      ·
                        rfl

theorem cell23_8137461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_8137461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137461 prefixEnd_8137461 := by exact prefixLift 8137461
  have htrace : WordTrace (prefixWord ++ tailWord_8137461) baseStart_8137461 baseEnd_8137461 := by
    simpa [prefixWord, tailWord_8137461, baseEnd_8137461] using wordTrace_append hprefix tailTrace_8137461
  have hstable : (prefixWord ++ tailWord_8137461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137461).length < 2 ^ (prefixWord ++ tailWord_8137461).sum := by decide
  have hdescent : baseEnd_8137461 < baseStart_8137461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137469 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_8137469 : Nat := 118140960795 + 8137469 * 2 ^ 59
def prefixEnd_8137469 : Nat := 4983230072969 + 3 ^ 40 * 8137469 * 2
def baseEnd_8137469 : Nat := 1392810969353909282937989

theorem tailTrace_8137469 : CollatzResearch.WordTrace tailWord_8137469 prefixEnd_8137469 1392810969353909282937989 := by
  unfold tailWord_8137469
  simp only [CollatzResearch.WordTrace]
  refine ⟨296797877356347056905143461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197865251570898037936762307 296797877356347056905143461)
  ·
    refine ⟨55649602004315073169714399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296797877356347056905143461 55649602004315073169714399)
    ·
      refine ⟨83474403006472609754571599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55649602004315073169714399 83474403006472609754571599)
      ·
        refine ⟨125211604509708914631857399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83474403006472609754571599 125211604509708914631857399)
        ·
          refine ⟨187817406764563371947786099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125211604509708914631857399 187817406764563371947786099)
          ·
            refine ⟨281726110146845057921679149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187817406764563371947786099 281726110146845057921679149)
            ·
              refine ⟨105647291305066896720629681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281726110146845057921679149 105647291305066896720629681)
              ·
                refine ⟨79235468478800172540472261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105647291305066896720629681 79235468478800172540472261)
                ·
                  refine ⟨14856650339775032351338549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79235468478800172540472261 14856650339775032351338549)
                  ·
                    refine ⟨1392810969353909282937989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14856650339775032351338549 1392810969353909282937989)
                    ·
                      rfl

theorem cell23_8137469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_8137469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137469 prefixEnd_8137469 := by exact prefixLift 8137469
  have htrace : WordTrace (prefixWord ++ tailWord_8137469) baseStart_8137469 baseEnd_8137469 := by
    simpa [prefixWord, tailWord_8137469, baseEnd_8137469] using wordTrace_append hprefix tailTrace_8137469
  have hstable : (prefixWord ++ tailWord_8137469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137469).length < 2 ^ (prefixWord ++ tailWord_8137469).sum := by decide
  have hdescent : baseEnd_8137469 < baseStart_8137469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137489 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_8137489 : Nat := 118140960795 + 8137489 * 2 ^ 59
def prefixEnd_8137489 : Nat := 4983230072969 + 3 ^ 40 * 8137489 * 2
def baseEnd_8137489 : Nat := 4178443177674817770563875

theorem tailTrace_8137489 : CollatzResearch.WordTrace tailWord_8137489 prefixEnd_8137489 4178443177674817770563875 := by
  unfold tailWord_8137489
  simp only [CollatzResearch.WordTrace]
  refine ⟨296798606816274600320871521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197865737877516400213914347 296798606816274600320871521)
  ·
    refine ⟨222598955112205950240653641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296798606816274600320871521 222598955112205950240653641)
    ·
      refine ⟨166949216334154462680490231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222598955112205950240653641 166949216334154462680490231)
      ·
        refine ⟨250423824501231694020735347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166949216334154462680490231 250423824501231694020735347)
        ·
          refine ⟨375635736751847541031103021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250423824501231694020735347 375635736751847541031103021)
          ·
            refine ⟨140863401281942827886663633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375635736751847541031103021 140863401281942827886663633)
            ·
              refine ⟨105647550961457120914997725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140863401281942827886663633 105647550961457120914997725)
              ·
                refine ⟨39617831610546420343124147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105647550961457120914997725 39617831610546420343124147)
                ·
                  refine ⟨59426747415819630514686221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39617831610546420343124147 59426747415819630514686221)
                  ·
                    refine ⟨22285030280932361443007333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59426747415819630514686221 22285030280932361443007333)
                    ·
                      refine ⟨4178443177674817770563875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22285030280932361443007333 4178443177674817770563875)
                      ·
                        rfl

theorem cell23_8137489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_8137489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137489 prefixEnd_8137489 := by exact prefixLift 8137489
  have htrace : WordTrace (prefixWord ++ tailWord_8137489) baseStart_8137489 baseEnd_8137489 := by
    simpa [prefixWord, tailWord_8137489, baseEnd_8137489] using wordTrace_append hprefix tailTrace_8137489
  have hstable : (prefixWord ++ tailWord_8137489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137489).length < 2 ^ (prefixWord ++ tailWord_8137489).sum := by decide
  have hdescent : baseEnd_8137489 < baseStart_8137489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137509 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_8137509 : Nat := 118140960795 + 8137509 * 2 ^ 59
def prefixEnd_8137509 : Nat := 4983230072969 + 3 ^ 40 * 8137509 * 2
def baseEnd_8137509 : Nat := 4178453447287907692313783

theorem tailTrace_8137509 : CollatzResearch.WordTrace tailWord_8137509 prefixEnd_8137509 4178453447287907692313783 := by
  unfold tailWord_8137509
  simp only [CollatzResearch.WordTrace]
  refine ⟨296799336276202143736599581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197866224184134762491066387 296799336276202143736599581)
  ·
    refine ⟨111299751103575803901224843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296799336276202143736599581 111299751103575803901224843)
    ·
      refine ⟨166949626655363705851837265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111299751103575803901224843 166949626655363705851837265)
      ·
        refine ⟨125212219991522779388877949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166949626655363705851837265 125212219991522779388877949)
        ·
          refine ⟨46954582496821042270829231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125212219991522779388877949 46954582496821042270829231)
          ·
            refine ⟨70431873745231563406243847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46954582496821042270829231 70431873745231563406243847)
            ·
              refine ⟨105647810617847345109365771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70431873745231563406243847 105647810617847345109365771)
              ·
                refine ⟨158471715926771017664048657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105647810617847345109365771 158471715926771017664048657)
                ·
                  refine ⟨118853786945078263248036493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158471715926771017664048657 118853786945078263248036493)
                  ·
                    refine ⟨44570170104404348718013685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118853786945078263248036493 44570170104404348718013685)
                    ·
                      refine ⟨4178453447287907692313783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44570170104404348718013685 4178453447287907692313783)
                      ·
                        rfl

theorem cell23_8137509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_8137509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137509 prefixEnd_8137509 := by exact prefixLift 8137509
  have htrace : WordTrace (prefixWord ++ tailWord_8137509) baseStart_8137509 baseEnd_8137509 := by
    simpa [prefixWord, tailWord_8137509, baseEnd_8137509] using wordTrace_append hprefix tailTrace_8137509
  have hstable : (prefixWord ++ tailWord_8137509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137509).length < 2 ^ (prefixWord ++ tailWord_8137509).sum := by decide
  have hdescent : baseEnd_8137509 < baseStart_8137509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137516 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_8137516 : Nat := 118140960795 + 8137516 * 2 ^ 59
def prefixEnd_8137516 : Nat := 4983230072969 + 3 ^ 40 * 8137516 * 2
def baseEnd_8137516 : Nat := 1392819013884163054975417

theorem tailTrace_8137516 : CollatzResearch.WordTrace tailWord_8137516 prefixEnd_8137516 1392819013884163054975417 := by
  unfold tailWord_8137516
  simp only [CollatzResearch.WordTrace]
  refine ⟨148399795793588391966052201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197866394391451189288069601 148399795793588391966052201)
  ·
    refine ⟨111299846845191293974539151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148399795793588391966052201 111299846845191293974539151)
    ·
      refine ⟨166949770267786940961808727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111299846845191293974539151 166949770267786940961808727)
      ·
        refine ⟨250424655401680411442713091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166949770267786940961808727 250424655401680411442713091)
        ·
          refine ⟨375636983102520617164069637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250424655401680411442713091 375636983102520617164069637)
          ·
            refine ⟨70431934331722615718263057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375636983102520617164069637 70431934331722615718263057)
            ·
              refine ⟨52823950748791961788697293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70431934331722615718263057 52823950748791961788697293)
              ·
                refine ⟨19808981530796985670761485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52823950748791961788697293 19808981530796985670761485)
                ·
                  refine ⟨7428368074048869626535557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19808981530796985670761485 7428368074048869626535557)
                  ·
                    refine ⟨1392819013884163054975417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428368074048869626535557 1392819013884163054975417)
                    ·
                      rfl

theorem cell23_8137516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_8137516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137516 prefixEnd_8137516 := by exact prefixLift 8137516
  have htrace : WordTrace (prefixWord ++ tailWord_8137516) baseStart_8137516 baseEnd_8137516 := by
    simpa [prefixWord, tailWord_8137516, baseEnd_8137516] using wordTrace_append hprefix tailTrace_8137516
  have hstable : (prefixWord ++ tailWord_8137516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137516).length < 2 ^ (prefixWord ++ tailWord_8137516).sum := by decide
  have hdescent : baseEnd_8137516 < baseStart_8137516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137523 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 2, 4, 2]
def baseStart_8137523 : Nat := 118140960795 + 8137523 * 2 ^ 59
def prefixEnd_8137523 : Nat := 4983230072969 + 3 ^ 40 * 8137523 * 2
def baseEnd_8137523 : Nat := 4178460636017070637538719

theorem tailTrace_8137523 : CollatzResearch.WordTrace tailWord_8137523 prefixEnd_8137523 4178460636017070637538719 := by
  unfold tailWord_8137523
  simp only [CollatzResearch.WordTrace]
  refine ⟨296799846898151424127609223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197866564598767616085072815 296799846898151424127609223)
  ·
    refine ⟨445199770347227136191413835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296799846898151424127609223 445199770347227136191413835)
    ·
      refine ⟨667799655520840704287120753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445199770347227136191413835 667799655520840704287120753)
      ·
        refine ⟨500849741640630528215340565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667799655520840704287120753 500849741640630528215340565)
        ·
          refine ⟨23477331639404556010094089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 500849741640630528215340565 23477331639404556010094089)
          ·
            refine ⟨17607998729553417007570567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23477331639404556010094089 17607998729553417007570567)
            ·
              refine ⟨26411998094330125511355851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17607998729553417007570567 26411998094330125511355851)
              ·
                refine ⟨39617997141495188267033777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26411998094330125511355851 39617997141495188267033777)
                ·
                  refine ⟨29713497856121391200275333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39617997141495188267033777 29713497856121391200275333)
                  ·
                    refine ⟨5571280848022760850051625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29713497856121391200275333 5571280848022760850051625)
                    ·
                      refine ⟨4178460636017070637538719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571280848022760850051625 4178460636017070637538719)
                      ·
                        rfl

theorem cell23_8137523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4, 2].length) (baseStart_8137523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137523 prefixEnd_8137523 := by exact prefixLift 8137523
  have htrace : WordTrace (prefixWord ++ tailWord_8137523) baseStart_8137523 baseEnd_8137523 := by
    simpa [prefixWord, tailWord_8137523, baseEnd_8137523] using wordTrace_append hprefix tailTrace_8137523
  have hstable : (prefixWord ++ tailWord_8137523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137523).length < 2 ^ (prefixWord ++ tailWord_8137523).sum := by decide
  have hdescent : baseEnd_8137523 < baseStart_8137523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137537 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 2, 5]
def baseStart_8137537 : Nat := 118140960795 + 8137537 * 2 ^ 59
def prefixEnd_8137537 : Nat := 4983230072969 + 3 ^ 40 * 8137537 * 2
def baseEnd_8137537 : Nat := 1392822608248744527587885

theorem tailTrace_8137537 : CollatzResearch.WordTrace tailWord_8137537 prefixEnd_8137537 1392822608248744527587885 := by
  unfold tailWord_8137537
  simp only [CollatzResearch.WordTrace]
  refine ⟨296800357520100704518618865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197866905013400469679079243 296800357520100704518618865)
  ·
    refine ⟨222600268140075528388964149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296800357520100704518618865 222600268140075528388964149)
    ·
      refine ⟨20868775138132080786465389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222600268140075528388964149 20868775138132080786465389)
      ·
        refine ⟨7825790676799530294924521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20868775138132080786465389 7825790676799530294924521)
        ·
          refine ⟨5869343007599647721193391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7825790676799530294924521 5869343007599647721193391)
          ·
            refine ⟨8804014511399471581790087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869343007599647721193391 8804014511399471581790087)
            ·
              refine ⟨13206021767099207372685131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804014511399471581790087 13206021767099207372685131)
              ·
                refine ⟨19809032650648811059027697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13206021767099207372685131 19809032650648811059027697)
                ·
                  refine ⟨14856774487986608294270773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19809032650648811059027697 14856774487986608294270773)
                  ·
                    refine ⟨1392822608248744527587885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14856774487986608294270773 1392822608248744527587885)
                    ·
                      rfl

theorem cell23_8137537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_8137537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137537 prefixEnd_8137537 := by exact prefixLift 8137537
  have htrace : WordTrace (prefixWord ++ tailWord_8137537) baseStart_8137537 baseEnd_8137537 := by
    simpa [prefixWord, tailWord_8137537, baseEnd_8137537] using wordTrace_append hprefix tailTrace_8137537
  have hstable : (prefixWord ++ tailWord_8137537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137537).length < 2 ^ (prefixWord ++ tailWord_8137537).sum := by decide
  have hdescent : baseEnd_8137537 < baseStart_8137537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137540 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_8137540 : Nat := 118140960795 + 8137540 * 2 ^ 59
def prefixEnd_8137540 : Nat := 4983230072969 + 3 ^ 40 * 8137540 * 2
def baseEnd_8137540 : Nat := 4178469365188197071026141

theorem tailTrace_8137540 : CollatzResearch.WordTrace tailWord_8137540 prefixEnd_8137540 4178469365188197071026141 := by
  unfold tailWord_8137540
  simp only [CollatzResearch.WordTrace]
  refine ⟨148400233469544918015489037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197866977959393224020652049 148400233469544918015489037)
  ·
    refine ⟨55650087551079344255808389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148400233469544918015489037 55650087551079344255808389)
    ·
      refine ⟨10434391415827377047964073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55650087551079344255808389 10434391415827377047964073)
      ·
        refine ⟨7825793561870532785973055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10434391415827377047964073 7825793561870532785973055)
        ·
          refine ⟨11738690342805799178959583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825793561870532785973055 11738690342805799178959583)
          ·
            refine ⟨17608035514208698768439375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11738690342805799178959583 17608035514208698768439375)
            ·
              refine ⟨26412053271313048152659063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17608035514208698768439375 26412053271313048152659063)
              ·
                refine ⟨39618079906969572228988595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26412053271313048152659063 39618079906969572228988595)
                ·
                  refine ⟨59427119860454358343482893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39618079906969572228988595 59427119860454358343482893)
                  ·
                    refine ⟨22285169947670384378806085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59427119860454358343482893 22285169947670384378806085)
                    ·
                      refine ⟨4178469365188197071026141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22285169947670384378806085 4178469365188197071026141)
                      ·
                        rfl

theorem cell23_8137540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_8137540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137540 prefixEnd_8137540 := by exact prefixLift 8137540
  have htrace : WordTrace (prefixWord ++ tailWord_8137540) baseStart_8137540 baseEnd_8137540 := by
    simpa [prefixWord, tailWord_8137540, baseEnd_8137540] using wordTrace_append hprefix tailTrace_8137540
  have hstable : (prefixWord ++ tailWord_8137540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137540).length < 2 ^ (prefixWord ++ tailWord_8137540).sum := by decide
  have hdescent : baseEnd_8137540 < baseStart_8137540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137569 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_8137569 : Nat := 118140960795 + 8137569 * 2 ^ 59
def prefixEnd_8137569 : Nat := 4983230072969 + 3 ^ 40 * 8137569 * 2
def baseEnd_8137569 : Nat := 4178484256127177457563507

theorem tailTrace_8137569 : CollatzResearch.WordTrace tailWord_8137569 prefixEnd_8137569 4178484256127177457563507 := by
  unfold tailWord_8137569
  simp only [CollatzResearch.WordTrace]
  refine ⟨296801524655984773983783761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197867683103989849322522507 296801524655984773983783761)
  ·
    refine ⟨222601143491988580487837821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296801524655984773983783761 222601143491988580487837821)
    ·
      refine ⟨83475428809495717682939183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222601143491988580487837821 83475428809495717682939183)
      ·
        refine ⟨125213143214243576524408775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83475428809495717682939183 125213143214243576524408775)
        ·
          refine ⟨187819714821365364786613163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125213143214243576524408775 187819714821365364786613163)
          ·
            refine ⟨281729572232048047179919745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187819714821365364786613163 281729572232048047179919745)
            ·
              refine ⟨211297179174036035384939809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281729572232048047179919745 211297179174036035384939809)
              ·
                refine ⟨158472884380527026538704857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211297179174036035384939809 158472884380527026538704857)
                ·
                  refine ⟨118854663285395269904028643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158472884380527026538704857 118854663285395269904028643)
                  ·
                    refine ⟨178281994928092904856042965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118854663285395269904028643 178281994928092904856042965)
                    ·
                      refine ⟨4178484256127177457563507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178281994928092904856042965 4178484256127177457563507)
                      ·
                        rfl

theorem cell23_8137569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_8137569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137569 prefixEnd_8137569 := by exact prefixLift 8137569
  have htrace : WordTrace (prefixWord ++ tailWord_8137569) baseStart_8137569 baseEnd_8137569 := by
    simpa [prefixWord, tailWord_8137569, baseEnd_8137569] using wordTrace_append hprefix tailTrace_8137569
  have hstable : (prefixWord ++ tailWord_8137569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137569).length < 2 ^ (prefixWord ++ tailWord_8137569).sum := by decide
  have hdescent : baseEnd_8137569 < baseStart_8137569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137573 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_8137573 : Nat := 118140960795 + 8137573 * 2 ^ 59
def prefixEnd_8137573 : Nat := 4983230072969 + 3 ^ 40 * 8137573 * 2
def baseEnd_8137573 : Nat := 4178486310049795441913489

theorem tailTrace_8137573 : CollatzResearch.WordTrace tailWord_8137573 prefixEnd_8137573 4178486310049795441913489 := by
  unfold tailWord_8137573
  simp only [CollatzResearch.WordTrace]
  refine ⟨296801670547970282666929373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197867780365313521777952915 296801670547970282666929373)
  ·
    refine ⟨111300626455488856000098515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296801670547970282666929373 111300626455488856000098515)
    ·
      refine ⟨166950939683233284000147773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111300626455488856000098515 166950939683233284000147773)
      ·
        refine ⟨62606602381212481500055415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166950939683233284000147773 62606602381212481500055415)
        ·
          refine ⟨93909903571818722250083123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62606602381212481500055415 93909903571818722250083123)
          ·
            refine ⟨140864855357728083375124685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93909903571818722250083123 140864855357728083375124685)
            ·
              refine ⟨52824320759148031265671757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140864855357728083375124685 52824320759148031265671757)
              ·
                refine ⟨19809120284680511724626909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52824320759148031265671757 19809120284680511724626909)
                ·
                  refine ⟨7428420106755191896735091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19809120284680511724626909 7428420106755191896735091)
                  ·
                    refine ⟨11142630160132787845102637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7428420106755191896735091 11142630160132787845102637)
                    ·
                      refine ⟨4178486310049795441913489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11142630160132787845102637 4178486310049795441913489)
                      ·
                        rfl

theorem cell23_8137573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_8137573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137573 prefixEnd_8137573 := by exact prefixLift 8137573
  have htrace : WordTrace (prefixWord ++ tailWord_8137573) baseStart_8137573 baseEnd_8137573 := by
    simpa [prefixWord, tailWord_8137573, baseEnd_8137573] using wordTrace_append hprefix tailTrace_8137573
  have hstable : (prefixWord ++ tailWord_8137573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137573).length < 2 ^ (prefixWord ++ tailWord_8137573).sum := by decide
  have hdescent : baseEnd_8137573 < baseStart_8137573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137593 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 1, 5]
def baseStart_8137593 : Nat := 118140960795 + 8137593 * 2 ^ 59
def prefixEnd_8137593 : Nat := 4983230072969 + 3 ^ 40 * 8137593 * 2
def baseEnd_8137593 : Nat := 1392832193220961787887799

theorem tailTrace_8137593 : CollatzResearch.WordTrace tailWord_8137593 prefixEnd_8137593 1392832193220961787887799 := by
  unfold tailWord_8137593
  simp only [CollatzResearch.WordTrace]
  refine ⟨296802400007897826082657433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197868266671931884055104955 296802400007897826082657433)
  ·
    refine ⟨222601800005923369561993075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296802400007897826082657433 222601800005923369561993075)
    ·
      refine ⟨333902700008885054342989613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222601800005923369561993075 333902700008885054342989613)
      ·
        refine ⟨125213512503331895378621105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333902700008885054342989613 125213512503331895378621105)
        ·
          refine ⟨93910134377498921533965829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125213512503331895378621105 93910134377498921533965829)
          ·
            refine ⟨17608150195781047787618593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93910134377498921533965829 17608150195781047787618593)
            ·
              refine ⟨13206112646835785840713945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17608150195781047787618593 13206112646835785840713945)
              ·
                refine ⟨9904584485126839380535459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13206112646835785840713945 9904584485126839380535459)
                ·
                  refine ⟨14856876727690259070803189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9904584485126839380535459 14856876727690259070803189)
                  ·
                    refine ⟨1392832193220961787887799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14856876727690259070803189 1392832193220961787887799)
                    ·
                      rfl

theorem cell23_8137593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_8137593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137593 prefixEnd_8137593 := by exact prefixLift 8137593
  have htrace : WordTrace (prefixWord ++ tailWord_8137593) baseStart_8137593 baseEnd_8137593 := by
    simpa [prefixWord, tailWord_8137593, baseEnd_8137593] using wordTrace_append hprefix tailTrace_8137593
  have hstable : (prefixWord ++ tailWord_8137593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137593).length < 2 ^ (prefixWord ++ tailWord_8137593).sum := by decide
  have hdescent : baseEnd_8137593 < baseStart_8137593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137596 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_8137596 : Nat := 118140960795 + 8137596 * 2 ^ 59
def prefixEnd_8137596 : Nat := 4983230072969 + 3 ^ 40 * 8137596 * 2
def baseEnd_8137596 : Nat := 4178498120104848851925883

theorem tailTrace_8137596 : CollatzResearch.WordTrace tailWord_8137596 prefixEnd_8137596 4178498120104848851925883 := by
  unfold tailWord_8137596
  simp only [CollatzResearch.WordTrace]
  refine ⟨148401254713443478797508321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197868339617924638396677761 148401254713443478797508321)
  ·
    refine ⟨111300941035082609098131241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148401254713443478797508321 111300941035082609098131241)
    ·
      refine ⟨83475705776311956823598431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111300941035082609098131241 83475705776311956823598431)
      ·
        refine ⟨125213558664467935235397647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83475705776311956823598431 125213558664467935235397647)
        ·
          refine ⟨187820337996701902853096471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125213558664467935235397647 187820337996701902853096471)
          ·
            refine ⟨281730506995052854279644707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187820337996701902853096471 281730506995052854279644707)
            ·
              refine ⟨422595760492579281419467061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281730506995052854279644707 422595760492579281419467061)
              ·
                refine ⟨39618352546179307633075037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422595760492579281419467061 39618352546179307633075037)
                ·
                  refine ⟨14856882204817240362403139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39618352546179307633075037 14856882204817240362403139)
                  ·
                    refine ⟨22285323307225860543604709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14856882204817240362403139 22285323307225860543604709)
                    ·
                      refine ⟨4178498120104848851925883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22285323307225860543604709 4178498120104848851925883)
                      ·
                        rfl

theorem cell23_8137596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_8137596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137596 prefixEnd_8137596 := by exact prefixLift 8137596
  have htrace : WordTrace (prefixWord ++ tailWord_8137596) baseStart_8137596 baseEnd_8137596 := by
    simpa [prefixWord, tailWord_8137596, baseEnd_8137596] using wordTrace_append hprefix tailTrace_8137596
  have hstable : (prefixWord ++ tailWord_8137596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137596).length < 2 ^ (prefixWord ++ tailWord_8137596).sum := by decide
  have hdescent : baseEnd_8137596 < baseStart_8137596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137607 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_8137607 : Nat := 118140960795 + 8137607 * 2 ^ 59
def prefixEnd_8137607 : Nat := 4983230072969 + 3 ^ 40 * 8137607 * 2
def baseEnd_8137607 : Nat := 4178503768392048308888333

theorem tailTrace_8137607 : CollatzResearch.WordTrace tailWord_8137607 prefixEnd_8137607 4178503768392048308888333 := by
  unfold tailWord_8137607
  simp only [CollatzResearch.WordTrace]
  refine ⟨296802910629847106473667075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197868607086564737649111383 296802910629847106473667075)
  ·
    refine ⟨445204365944770659710500613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296802910629847106473667075 445204365944770659710500613)
    ·
      refine ⟨83475818614644498695718865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445204365944770659710500613 83475818614644498695718865)
      ·
        refine ⟨62606863960983374021789149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83475818614644498695718865 62606863960983374021789149)
        ·
          refine ⟨23477573985368765258170931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62606863960983374021789149 23477573985368765258170931)
          ·
            refine ⟨35216360978053147887256397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23477573985368765258170931 35216360978053147887256397)
            ·
              refine ⟨13206135366769930457721149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35216360978053147887256397 13206135366769930457721149)
              ·
                refine ⟨4952300762538723921645431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13206135366769930457721149 4952300762538723921645431)
                ·
                  refine ⟨7428451143808085882468147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952300762538723921645431 7428451143808085882468147)
                  ·
                    refine ⟨11142676715712128823702221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7428451143808085882468147 11142676715712128823702221)
                    ·
                      refine ⟨4178503768392048308888333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11142676715712128823702221 4178503768392048308888333)
                      ·
                        rfl

theorem cell23_8137607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_8137607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137607 prefixEnd_8137607 := by exact prefixLift 8137607
  have htrace : WordTrace (prefixWord ++ tailWord_8137607) baseStart_8137607 baseEnd_8137607 := by
    simpa [prefixWord, tailWord_8137607, baseEnd_8137607] using wordTrace_append hprefix tailTrace_8137607
  have hstable : (prefixWord ++ tailWord_8137607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137607).length < 2 ^ (prefixWord ++ tailWord_8137607).sum := by decide
  have hdescent : baseEnd_8137607 < baseStart_8137607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137623 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 2, 4]
def baseStart_8137623 : Nat := 118140960795 + 8137623 * 2 ^ 59
def prefixEnd_8137623 : Nat := 4983230072969 + 3 ^ 40 * 8137623 * 2
def baseEnd_8137623 : Nat := 1392837328027506748762753

theorem tailTrace_8137623 : CollatzResearch.WordTrace tailWord_8137623 prefixEnd_8137623 1392837328027506748762753 := by
  unfold tailWord_8137623
  simp only [CollatzResearch.WordTrace]
  refine ⟨296803494197789141206249523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197868996131859427470833015 296803494197789141206249523)
  ·
    refine ⟨445205241296683711809374285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296803494197789141206249523 445205241296683711809374285)
    ·
      refine ⟨166951965486256391928515357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445205241296683711809374285 166951965486256391928515357)
      ·
        refine ⟨62606987057346146973193259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166951965486256391928515357 62606987057346146973193259)
        ·
          refine ⟨93910480586019220459789889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62606987057346146973193259 93910480586019220459789889)
          ·
            refine ⟨70432860439514415344842417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93910480586019220459789889 70432860439514415344842417)
            ·
              refine ⟨52824645329635811508631813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70432860439514415344842417 52824645329635811508631813)
              ·
                refine ⟨9904620999306714657868465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52824645329635811508631813 9904620999306714657868465)
                ·
                  refine ⟨7428465749480035993401349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9904620999306714657868465 7428465749480035993401349)
                  ·
                    refine ⟨1392837328027506748762753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428465749480035993401349 1392837328027506748762753)
                    ·
                      rfl

theorem cell23_8137623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_8137623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137623 prefixEnd_8137623 := by exact prefixLift 8137623
  have htrace : WordTrace (prefixWord ++ tailWord_8137623) baseStart_8137623 baseEnd_8137623 := by
    simpa [prefixWord, tailWord_8137623, baseEnd_8137623] using wordTrace_append hprefix tailTrace_8137623
  have hstable : (prefixWord ++ tailWord_8137623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137623).length < 2 ^ (prefixWord ++ tailWord_8137623).sum := by decide
  have hdescent : baseEnd_8137623 < baseStart_8137623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137633 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_8137633 : Nat := 118140960795 + 8137633 * 2 ^ 59
def prefixEnd_8137633 : Nat := 4983230072969 + 3 ^ 40 * 8137633 * 2
def baseEnd_8137633 : Nat := 4178517118889065207163213

theorem tailTrace_8137633 : CollatzResearch.WordTrace tailWord_8137633 prefixEnd_8137633 4178517118889065207163213 := by
  unfold tailWord_8137633
  simp only [CollatzResearch.WordTrace]
  refine ⟨296803858927752912914113553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197869239285168608609409035 296803858927752912914113553)
  ·
    refine ⟨222602894195814684685585165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296803858927752912914113553 222602894195814684685585165)
    ·
      refine ⟨83476085323430506757094437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222602894195814684685585165 83476085323430506757094437)
      ·
        refine ⟨15651765998143220016955207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83476085323430506757094437 15651765998143220016955207)
        ·
          refine ⟨23477648997214830025432811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651765998143220016955207 23477648997214830025432811)
          ·
            refine ⟨35216473495822245038149217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23477648997214830025432811 35216473495822245038149217)
            ·
              refine ⟨26412355121866683778611913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35216473495822245038149217 26412355121866683778611913)
              ·
                refine ⟨19809266341400012833958935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26412355121866683778611913 19809266341400012833958935)
                ·
                  refine ⟨29713899512100019250938403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19809266341400012833958935 29713899512100019250938403)
                  ·
                    refine ⟨44570849268150028876407605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29713899512100019250938403 44570849268150028876407605)
                    ·
                      refine ⟨4178517118889065207163213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44570849268150028876407605 4178517118889065207163213)
                      ·
                        rfl

theorem cell23_8137633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_8137633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137633 prefixEnd_8137633 := by exact prefixLift 8137633
  have htrace : WordTrace (prefixWord ++ tailWord_8137633) baseStart_8137633 baseEnd_8137633 := by
    simpa [prefixWord, tailWord_8137633, baseEnd_8137633] using wordTrace_append hprefix tailTrace_8137633
  have hstable : (prefixWord ++ tailWord_8137633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137633).length < 2 ^ (prefixWord ++ tailWord_8137633).sum := by decide
  have hdescent : baseEnd_8137633 < baseStart_8137633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137636 : List Nat := [2, 3, 1, 2, 1, 2, 4, 8]
def baseStart_8137636 : Nat := 118140960795 + 8137636 * 2 ^ 59
def prefixEnd_8137636 : Nat := 4983230072969 + 3 ^ 40 * 8137636 * 2
def baseEnd_8137636 : Nat := 154759950345593655386137

theorem tailTrace_8137636 : CollatzResearch.WordTrace tailWord_8137636 prefixEnd_8137636 154759950345593655386137 := by
  unfold tailWord_8137636
  simp only [CollatzResearch.WordTrace]
  refine ⟨148401984173371022213236381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197869312231161362950981841 148401984173371022213236381)
  ·
    refine ⟨55650744065014133329963643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148401984173371022213236381 55650744065014133329963643)
    ·
      refine ⟨83476116097521199994945465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55650744065014133329963643 83476116097521199994945465)
      ·
        refine ⟨62607087073140899996209099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83476116097521199994945465 62607087073140899996209099)
        ·
          refine ⟨93910630609711349994313649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62607087073140899996209099 93910630609711349994313649)
          ·
            refine ⟨70432972957283512495735237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93910630609711349994313649 70432972957283512495735237)
            ·
              refine ⟨13206182429490658592950357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70432972957283512495735237 13206182429490658592950357)
              ·
                refine ⟨154759950345593655386137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13206182429490658592950357 154759950345593655386137)
                ·
                  rfl

theorem cell23_8137636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 8].length) (baseStart_8137636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137636 prefixEnd_8137636 := by exact prefixLift 8137636
  have htrace : WordTrace (prefixWord ++ tailWord_8137636) baseStart_8137636 baseEnd_8137636 := by
    simpa [prefixWord, tailWord_8137636, baseEnd_8137636] using wordTrace_append hprefix tailTrace_8137636
  have hstable : (prefixWord ++ tailWord_8137636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137636).length < 2 ^ (prefixWord ++ tailWord_8137636).sum := by decide
  have hdescent : baseEnd_8137636 < baseStart_8137636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137663 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 3]
def baseStart_8137663 : Nat := 118140960795 + 8137663 * 2 ^ 59
def prefixEnd_8137663 : Nat := 4983230072969 + 3 ^ 40 * 8137663 * 2
def baseEnd_8137663 : Nat := 4178532523308700089788075

theorem tailTrace_8137663 : CollatzResearch.WordTrace tailWord_8137663 prefixEnd_8137663 4178532523308700089788075 := by
  unfold tailWord_8137663
  simp only [CollatzResearch.WordTrace]
  refine ⟨296804953117644228037705643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197869968745096152025137095 296804953117644228037705643)
  ·
    refine ⟨445207429676466342056558465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296804953117644228037705643 445207429676466342056558465)
    ·
      refine ⟨333905572257349756542418849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445207429676466342056558465 333905572257349756542418849)
      ·
        refine ⟨250429179193012317406814137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333905572257349756542418849 250429179193012317406814137)
        ·
          refine ⟨187821884394759238055110603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250429179193012317406814137 187821884394759238055110603)
          ·
            refine ⟨281732826592138857082665905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187821884394759238055110603 281732826592138857082665905)
            ·
              refine ⟨211299619944104142811999429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281732826592138857082665905 211299619944104142811999429)
              ·
                refine ⟨39618678739519526777249893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211299619944104142811999429 39618678739519526777249893)
                ·
                  refine ⟨7428502263659911270734355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39618678739519526777249893 7428502263659911270734355)
                  ·
                    refine ⟨11142753395489866906101533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7428502263659911270734355 11142753395489866906101533)
                    ·
                      refine ⟨4178532523308700089788075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11142753395489866906101533 4178532523308700089788075)
                      ·
                        rfl

theorem cell23_8137663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_8137663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137663 prefixEnd_8137663 := by exact prefixLift 8137663
  have htrace : WordTrace (prefixWord ++ tailWord_8137663) baseStart_8137663 baseEnd_8137663 := by
    simpa [prefixWord, tailWord_8137663, baseEnd_8137663] using wordTrace_append hprefix tailTrace_8137663
  have hstable : (prefixWord ++ tailWord_8137663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137663).length < 2 ^ (prefixWord ++ tailWord_8137663).sum := by decide
  have hdescent : baseEnd_8137663 < baseStart_8137663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
