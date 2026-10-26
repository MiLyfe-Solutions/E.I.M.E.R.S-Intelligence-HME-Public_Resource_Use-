import V185TrunkScan22Chunk206

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1845285 : List Nat := [1, 3, 1, 2, 2, 4, 1, 8]
def baseStart_1845285 : Nat := 118140960795 + 1845285 * 2 ^ 59
def prefixEnd_1845285 : Nat := 4983230072969 + 3 ^ 40 * 1845285 * 2
def baseEnd_1845285 : Nat := 70186529594956892418607

theorem tailTrace_1845285 : CollatzResearch.WordTrace tailWord_1845285 prefixEnd_1845285 70186529594956892418607 := by
  unfold tailWord_1845285
  simp only [CollatzResearch.WordTrace]
  refine ⟨67303073119855069432769309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44868715413236712955179539 67303073119855069432769309)
  ·
    refine ⟨25238652419945651037288491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67303073119855069432769309 25238652419945651037288491)
    ·
      refine ⟨37857978629918476555932737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25238652419945651037288491 37857978629918476555932737)
      ·
        refine ⟨28393483972438857416949553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37857978629918476555932737 28393483972438857416949553)
        ·
          refine ⟨21295112979329143062712165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28393483972438857416949553 21295112979329143062712165)
          ·
            refine ⟨3992833683624214324258531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21295112979329143062712165 3992833683624214324258531)
            ·
              refine ⟨5989250525436321486387797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992833683624214324258531 5989250525436321486387797)
              ·
                refine ⟨70186529594956892418607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5989250525436321486387797 70186529594956892418607)
                ·
                  rfl

theorem cell22_1845285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 8].length) (baseStart_1845285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845285 prefixEnd_1845285 := by exact prefixLift 1845285
  have htrace : WordTrace (prefixWord ++ tailWord_1845285) baseStart_1845285 baseEnd_1845285 := by
    simpa [prefixWord, tailWord_1845285, baseEnd_1845285] using wordTrace_append hprefix tailTrace_1845285
  have hstable : (prefixWord ++ tailWord_1845285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845285).length < 2 ^ (prefixWord ++ tailWord_1845285).sum := by decide
  have hdescent : baseEnd_1845285 < baseStart_1845285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845345 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1845345 : Nat := 118140960795 + 1845345 * 2 ^ 59
def prefixEnd_1845345 : Nat := 4983230072969 + 3 ^ 40 * 1845345 * 2
def baseEnd_1845345 : Nat := 631699305580791875267279

theorem tailTrace_1845345 : CollatzResearch.WordTrace tailWord_1845345 prefixEnd_1845345 631699305580791875267279 := by
  unfold tailWord_1845345
  simp only [CollatzResearch.WordTrace]
  refine ⟨67305261499637699679953489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44870174333091799786635659 67305261499637699679953489)
  ·
    refine ⟨50478946124728274759965117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67305261499637699679953489 50478946124728274759965117)
    ·
      refine ⟨18929604796773103034986919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50478946124728274759965117 18929604796773103034986919)
      ·
        refine ⟨28394407195159654552480379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18929604796773103034986919 28394407195159654552480379)
        ·
          refine ⟨42591610792739481828720569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28394407195159654552480379 42591610792739481828720569)
          ·
            refine ⟨31943708094554611371540427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42591610792739481828720569 31943708094554611371540427)
            ·
              refine ⟨47915562141831917057310641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31943708094554611371540427 47915562141831917057310641)
              ·
                refine ⟨35936671606373937792982981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47915562141831917057310641 35936671606373937792982981)
                ·
                  refine ⟨6738125926195113336184309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35936671606373937792982981 6738125926195113336184309)
                  ·
                    refine ⟨631699305580791875267279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6738125926195113336184309 631699305580791875267279)
                    ·
                      rfl

theorem cell22_1845345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1845345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845345 prefixEnd_1845345 := by exact prefixLift 1845345
  have htrace : WordTrace (prefixWord ++ tailWord_1845345) baseStart_1845345 baseEnd_1845345 := by
    simpa [prefixWord, tailWord_1845345, baseEnd_1845345] using wordTrace_append hprefix tailTrace_1845345
  have hstable : (prefixWord ++ tailWord_1845345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845345).length < 2 ^ (prefixWord ++ tailWord_1845345).sum := by decide
  have hdescent : baseEnd_1845345 < baseStart_1845345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845394 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1845394 : Nat := 118140960795 + 1845394 * 2 ^ 59
def prefixEnd_1845394 : Nat := 4983230072969 + 3 ^ 40 * 1845394 * 2
def baseEnd_1845394 : Nat := 631716079282172080792129

theorem tailTrace_1845394 : CollatzResearch.WordTrace tailWord_1845394 prefixEnd_1845394 631716079282172080792129 := by
  unfold tailWord_1845394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16826762169115045262121809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44871365784306787365658157 16826762169115045262121809)
  ·
    refine ⟨12620071626836283946591357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16826762169115045262121809 12620071626836283946591357)
    ·
      refine ⟨4732526860063606479971759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12620071626836283946591357 4732526860063606479971759)
      ·
        refine ⟨7098790290095409719957639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732526860063606479971759 7098790290095409719957639)
        ·
          refine ⟨10648185435143114579936459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098790290095409719957639 10648185435143114579936459)
          ·
            refine ⟨15972278152714671869904689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648185435143114579936459 15972278152714671869904689)
            ·
              refine ⟨11979208614536003902428517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15972278152714671869904689 11979208614536003902428517)
              ·
                refine ⟨2246101615225500731705347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11979208614536003902428517 2246101615225500731705347)
                ·
                  refine ⟨3369152422838251097558021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246101615225500731705347 3369152422838251097558021)
                  ·
                    refine ⟨631716079282172080792129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3369152422838251097558021 631716079282172080792129)
                    ·
                      rfl

theorem cell22_1845394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1845394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845394 prefixEnd_1845394 := by exact prefixLift 1845394
  have htrace : WordTrace (prefixWord ++ tailWord_1845394) baseStart_1845394 baseEnd_1845394 := by
    simpa [prefixWord, tailWord_1845394, baseEnd_1845394] using wordTrace_append hprefix tailTrace_1845394
  have hstable : (prefixWord ++ tailWord_1845394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845394).length < 2 ^ (prefixWord ++ tailWord_1845394).sum := by decide
  have hdescent : baseEnd_1845394 < baseStart_1845394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845409 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 4]
def baseStart_1845409 : Nat := 118140960795 + 1845409 * 2 ^ 59
def prefixEnd_1845409 : Nat := 4983230072969 + 3 ^ 40 * 1845409 * 2
def baseEnd_1845409 : Nat := 210573738029572347222361

theorem tailTrace_1845409 : CollatzResearch.WordTrace tailWord_1845409 prefixEnd_1845409 210573738029572347222361 := by
  unfold tailWord_1845409
  simp only [CollatzResearch.WordTrace]
  refine ⟨67307595771405838610283281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44871730514270559073522187 67307595771405838610283281)
  ·
    refine ⟨50480696828554378957712461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67307595771405838610283281 50480696828554378957712461)
    ·
      refine ⟨18930261310707892109142173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50480696828554378957712461 18930261310707892109142173)
      ·
        refine ⟨7098847991515459540928315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18930261310707892109142173 7098847991515459540928315)
        ·
          refine ⟨10648271987273189311392473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098847991515459540928315 10648271987273189311392473)
          ·
            refine ⟨7986203990454891983544355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10648271987273189311392473 7986203990454891983544355)
            ·
              refine ⟨11979305985682337975316533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986203990454891983544355 11979305985682337975316533)
              ·
                refine ⟨1123059936157719185185925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11979305985682337975316533 1123059936157719185185925)
                ·
                  refine ⟨210573738029572347222361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123059936157719185185925 210573738029572347222361)
                  ·
                    rfl

theorem cell22_1845409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_1845409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845409 prefixEnd_1845409 := by exact prefixLift 1845409
  have htrace : WordTrace (prefixWord ++ tailWord_1845409) baseStart_1845409 baseEnd_1845409 := by
    simpa [prefixWord, tailWord_1845409, baseEnd_1845409] using wordTrace_append hprefix tailTrace_1845409
  have hstable : (prefixWord ++ tailWord_1845409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845409).length < 2 ^ (prefixWord ++ tailWord_1845409).sum := by decide
  have hdescent : baseEnd_1845409 < baseStart_1845409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845454 : List Nat := [4, 1, 1, 1, 4, 1, 4, 6]
def baseStart_1845454 : Nat := 118140960795 + 1845454 * 2 ^ 59
def prefixEnd_1845454 : Nat := 4983230072969 + 3 ^ 40 * 1845454 * 2
def baseEnd_1845454 : Nat := 70192957612039102699105

theorem tailTrace_1845454 : CollatzResearch.WordTrace tailWord_1845454 prefixEnd_1845454 70192957612039102699105 := by
  unfold tailWord_1845454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413654632030351411958927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44872824704161874197114277 8413654632030351411958927)
  ·
    refine ⟨12620481948045527117938391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8413654632030351411958927 12620481948045527117938391)
    ·
      refine ⟨18930722922068290676907587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12620481948045527117938391 18930722922068290676907587)
      ·
        refine ⟨28396084383102436015361381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18930722922068290676907587 28396084383102436015361381)
        ·
          refine ⟨5324265821831706752880259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28396084383102436015361381 5324265821831706752880259)
          ·
            refine ⟨7986398732747560129320389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324265821831706752880259 7986398732747560129320389)
            ·
              refine ⟨1497449762390167524247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7986398732747560129320389 1497449762390167524247573)
              ·
                refine ⟨70192957612039102699105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1497449762390167524247573 70192957612039102699105)
                ·
                  rfl

theorem cell22_1845454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_1845454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845454 prefixEnd_1845454 := by exact prefixLift 1845454
  have htrace : WordTrace (prefixWord ++ tailWord_1845454) baseStart_1845454 baseEnd_1845454 := by
    simpa [prefixWord, tailWord_1845454, baseEnd_1845454] using wordTrace_append hprefix tailTrace_1845454
  have hstable : (prefixWord ++ tailWord_1845454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845454).length < 2 ^ (prefixWord ++ tailWord_1845454).sum := by decide
  have hdescent : baseEnd_1845454 < baseStart_1845454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845482 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_1845482 : Nat := 118140960795 + 1845482 * 2 ^ 59
def prefixEnd_1845482 : Nat := 4983230072969 + 3 ^ 40 * 1845482 * 2
def baseEnd_1845482 : Nat := 210582067826856394863953

theorem tailTrace_1845482 : CollatzResearch.WordTrace tailWord_1845482 prefixEnd_1845482 210582067826856394863953 := by
  unfold tailWord_1845482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827564575035343019422675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44873505533427581385127133 16827564575035343019422675)
  ·
    refine ⟨25241346862553014529134013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16827564575035343019422675 25241346862553014529134013)
    ·
      refine ⟨9465505073457380448425255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25241346862553014529134013 9465505073457380448425255)
      ·
        refine ⟨14198257610186070672637883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465505073457380448425255 14198257610186070672637883)
        ·
          refine ⟨21297386415279106008956825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14198257610186070672637883 21297386415279106008956825)
          ·
            refine ⟨15973039811459329506717619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21297386415279106008956825 15973039811459329506717619)
            ·
              refine ⟨23959559717188994260076429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15973039811459329506717619 23959559717188994260076429)
              ·
                refine ⟨8984834893945872847528661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23959559717188994260076429 8984834893945872847528661)
                ·
                  refine ⟨210582067826856394863953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8984834893945872847528661 210582067826856394863953)
                  ·
                    rfl

theorem cell22_1845482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_1845482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845482 prefixEnd_1845482 := by exact prefixLift 1845482
  have htrace : WordTrace (prefixWord ++ tailWord_1845482) baseStart_1845482 baseEnd_1845482 := by
    simpa [prefixWord, tailWord_1845482, baseEnd_1845482] using wordTrace_append hprefix tailTrace_1845482
  have hstable : (prefixWord ++ tailWord_1845482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845482).length < 2 ^ (prefixWord ++ tailWord_1845482).sum := by decide
  have hdescent : baseEnd_1845482 < baseStart_1845482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845589 : List Nat := [1, 3, 2, 2, 4, 1, 9]
def baseStart_1845589 : Nat := 118140960795 + 1845589 * 2 ^ 59
def prefixEnd_1845589 : Nat := 4983230072969 + 3 ^ 40 * 1845589 * 2
def baseEnd_1845589 : Nat := 23399364139528021191353

theorem tailTrace_1845589 : CollatzResearch.WordTrace tailWord_1845589 prefixEnd_1845589 23399364139528021191353 := by
  unfold tailWord_1845589
  simp only [CollatzResearch.WordTrace]
  refine ⟨67314160910753729351835821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44876107273835819567890547 67314160910753729351835821)
  ·
    refine ⟨25242810341532648506938433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67314160910753729351835821 25242810341532648506938433)
    ·
      refine ⟨18932107756149486380203825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25242810341532648506938433 18932107756149486380203825)
      ·
        refine ⟨14199080817112114785152869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18932107756149486380203825 14199080817112114785152869)
        ·
          refine ⟨2662327653208521522216163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14199080817112114785152869 2662327653208521522216163)
          ·
            refine ⟨3993491479812782283324245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662327653208521522216163 3993491479812782283324245)
            ·
              refine ⟨23399364139528021191353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3993491479812782283324245 23399364139528021191353)
              ·
                rfl

theorem cell22_1845589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 9].length) (baseStart_1845589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845589 prefixEnd_1845589 := by exact prefixLift 1845589
  have htrace : WordTrace (prefixWord ++ tailWord_1845589) baseStart_1845589 baseEnd_1845589 := by
    simpa [prefixWord, tailWord_1845589, baseEnd_1845589] using wordTrace_append hprefix tailTrace_1845589
  have hstable : (prefixWord ++ tailWord_1845589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845589).length < 2 ^ (prefixWord ++ tailWord_1845589).sum := by decide
  have hdescent : baseEnd_1845589 < baseStart_1845589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845610 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_1845610 : Nat := 118140960795 + 1845610 * 2 ^ 59
def prefixEnd_1845610 : Nat := 4983230072969 + 3 ^ 40 * 1845610 * 2
def baseEnd_1845610 : Nat := 631790020496419517391467

theorem tailTrace_1845610 : CollatzResearch.WordTrace tailWord_1845610 prefixEnd_1845610 631790020496419517391467 := by
  unfold tailWord_1845610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16828731710919412484587571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44876617895785099958900189 16828731710919412484587571)
  ·
    refine ⟨25243097566379118726881357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16828731710919412484587571 25243097566379118726881357)
    ·
      refine ⟨9466161587392169522580509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25243097566379118726881357 9466161587392169522580509)
      ·
        refine ⟨3549810595272063570967691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9466161587392169522580509 3549810595272063570967691)
        ·
          refine ⟨5324715892908095356451537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549810595272063570967691 5324715892908095356451537)
          ·
            refine ⟨3993536919681071517338653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5324715892908095356451537 3993536919681071517338653)
            ·
              refine ⟨1497576344880401819001995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3993536919681071517338653 1497576344880401819001995)
              ·
                refine ⟨2246364517320602728502993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497576344880401819001995 2246364517320602728502993)
                ·
                  refine ⟨1684773387990452046377245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2246364517320602728502993 1684773387990452046377245)
                  ·
                    refine ⟨631790020496419517391467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1684773387990452046377245 631790020496419517391467)
                    ·
                      rfl

theorem cell22_1845610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_1845610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845610 prefixEnd_1845610 := by exact prefixLift 1845610
  have htrace : WordTrace (prefixWord ++ tailWord_1845610) baseStart_1845610 baseEnd_1845610 := by
    simpa [prefixWord, tailWord_1845610, baseEnd_1845610] using wordTrace_append hprefix tailTrace_1845610
  have hstable : (prefixWord ++ tailWord_1845610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845610).length < 2 ^ (prefixWord ++ tailWord_1845610).sum := by decide
  have hdescent : baseEnd_1845610 < baseStart_1845610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845681 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1845681 : Nat := 118140960795 + 1845681 * 2 ^ 59
def prefixEnd_1845681 : Nat := 4983230072969 + 3 ^ 40 * 1845681 * 2
def baseEnd_1845681 : Nat := 631814325247398998866249

theorem tailTrace_1845681 : CollatzResearch.WordTrace tailWord_1845681 prefixEnd_1845681 631814325247398998866249 := by
  unfold tailWord_1845681
  simp only [CollatzResearch.WordTrace]
  refine ⟨67317516426420429064184897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44878344284280286042789931 67317516426420429064184897)
  ·
    refine ⟨50488137319815321798138673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67317516426420429064184897 50488137319815321798138673)
    ·
      refine ⟨37866102989861491348604005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50488137319815321798138673 37866102989861491348604005)
      ·
        refine ⟨7099894310599029627863251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37866102989861491348604005 7099894310599029627863251)
        ·
          refine ⟨10649841465898544441794877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099894310599029627863251 10649841465898544441794877)
          ·
            refine ⟨3993690549711954165673079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10649841465898544441794877 3993690549711954165673079)
            ·
              refine ⟨5990535824567931248509619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993690549711954165673079 5990535824567931248509619)
              ·
                refine ⟨8985803736851896872764429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990535824567931248509619 8985803736851896872764429)
                ·
                  refine ⟨3369676401319461327286661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8985803736851896872764429 3369676401319461327286661)
                  ·
                    refine ⟨631814325247398998866249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3369676401319461327286661 631814325247398998866249)
                    ·
                      rfl

theorem cell22_1845681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1845681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845681 prefixEnd_1845681 := by exact prefixLift 1845681
  have htrace : WordTrace (prefixWord ++ tailWord_1845681) baseStart_1845681 baseEnd_1845681 := by
    simpa [prefixWord, tailWord_1845681, baseEnd_1845681] using wordTrace_append hprefix tailTrace_1845681
  have hstable : (prefixWord ++ tailWord_1845681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845681).length < 2 ^ (prefixWord ++ tailWord_1845681).sum := by decide
  have hdescent : baseEnd_1845681 < baseStart_1845681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845696 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 4]
def baseStart_1845696 : Nat := 118140960795 + 1845696 * 2 ^ 59
def prefixEnd_1845696 : Nat := 4983230072969 + 3 ^ 40 * 1845696 * 2
def baseEnd_1845696 : Nat := 210606486684647986580401

theorem tailTrace_1845696 : CollatzResearch.WordTrace tailWord_1845696 prefixEnd_1845696 210606486684647986580401 := by
  unfold tailWord_1845696
  simp only [CollatzResearch.WordTrace]
  refine ⟨33659031760683043312990471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44878709014244057750653961 33659031760683043312990471)
  ·
    refine ⟨50488547641024564969485707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33659031760683043312990471 50488547641024564969485707)
    ·
      refine ⟨75732821461536847454228561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50488547641024564969485707 75732821461536847454228561)
      ·
        refine ⟨56799616096152635590671421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75732821461536847454228561 56799616096152635590671421)
        ·
          refine ⟨21299856036057238346501783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56799616096152635590671421 21299856036057238346501783)
          ·
            refine ⟨31949784054085857519752675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21299856036057238346501783 31949784054085857519752675)
            ·
              refine ⟨47924676081128786279629013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31949784054085857519752675 47924676081128786279629013)
              ·
                refine ⟨1123234595651455928428805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47924676081128786279629013 1123234595651455928428805)
                ·
                  refine ⟨210606486684647986580401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123234595651455928428805 210606486684647986580401)
                  ·
                    rfl

theorem cell22_1845696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_1845696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845696 prefixEnd_1845696 := by exact prefixLift 1845696
  have htrace : WordTrace (prefixWord ++ tailWord_1845696) baseStart_1845696 baseEnd_1845696 := by
    simpa [prefixWord, tailWord_1845696, baseEnd_1845696] using wordTrace_append hprefix tailTrace_1845696
  have hstable : (prefixWord ++ tailWord_1845696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845696).length < 2 ^ (prefixWord ++ tailWord_1845696).sum := by decide
  have hdescent : baseEnd_1845696 < baseStart_1845696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845730 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1845730 : Nat := 118140960795 + 1845730 * 2 ^ 59
def prefixEnd_1845730 : Nat := 4983230072969 + 3 ^ 40 * 1845730 * 2
def baseEnd_1845730 : Nat := 210610366316259734797033

theorem tailTrace_1845730 : CollatzResearch.WordTrace tailWord_1845730 prefixEnd_1845730 210610366316259734797033 := by
  unfold tailWord_1845730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829825900810727608179661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44879535735495273621812429 16829825900810727608179661)
  ·
    refine ⟨6311184712804022853067373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16829825900810727608179661 6311184712804022853067373)
    ·
      refine ⟨2366694267301508569900265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6311184712804022853067373 2366694267301508569900265)
      ·
        refine ⟨1775020700476131427425199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2366694267301508569900265 1775020700476131427425199)
        ·
          refine ⟨2662531050714197141137799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775020700476131427425199 2662531050714197141137799)
          ·
            refine ⟨3993796576071295711706699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662531050714197141137799 3993796576071295711706699)
            ·
              refine ⟨5990694864106943567560049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993796576071295711706699 5990694864106943567560049)
              ·
                refine ⟨4493021148080207675670037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5990694864106943567560049 4493021148080207675670037)
                ·
                  refine ⟨210610366316259734797033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4493021148080207675670037 210610366316259734797033)
                  ·
                    rfl

theorem cell22_1845730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1845730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845730 prefixEnd_1845730 := by exact prefixLift 1845730
  have htrace : WordTrace (prefixWord ++ tailWord_1845730) baseStart_1845730 baseEnd_1845730 := by
    simpa [prefixWord, tailWord_1845730, baseEnd_1845730] using wordTrace_append hprefix tailTrace_1845730
  have hstable : (prefixWord ++ tailWord_1845730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845730).length < 2 ^ (prefixWord ++ tailWord_1845730).sum := by decide
  have hdescent : baseEnd_1845730 < baseStart_1845730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845749 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1845749 : Nat := 118140960795 + 1845749 * 2 ^ 59
def prefixEnd_1845749 : Nat := 4983230072969 + 3 ^ 40 * 1845749 * 2
def baseEnd_1845749 : Nat := 631837603037069488166041

theorem tailTrace_1845749 : CollatzResearch.WordTrace tailWord_1845749 prefixEnd_1845749 631837603037069488166041 := by
  unfold tailWord_1845749
  simp only [CollatzResearch.WordTrace]
  refine ⟨67319996590174076677660301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44879997726782717785106867 67319996590174076677660301)
  ·
    refine ⟨25244998721315278754122613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67319996590174076677660301 25244998721315278754122613)
    ·
      refine ⟨2366718630123307383198995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25244998721315278754122613 2366718630123307383198995)
      ·
        refine ⟨3550077945184961074798493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366718630123307383198995 3550077945184961074798493)
        ·
          refine ⟨1331279229444360403049435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3550077945184961074798493 1331279229444360403049435)
          ·
            refine ⟨1996918844166540604574153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331279229444360403049435 1996918844166540604574153)
            ·
              refine ⟨1497689133124905453430615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996918844166540604574153 1497689133124905453430615)
              ·
                refine ⟨2246533699687358180145923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497689133124905453430615 2246533699687358180145923)
                ·
                  refine ⟨3369800549531037270218885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246533699687358180145923 3369800549531037270218885)
                  ·
                    refine ⟨631837603037069488166041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3369800549531037270218885 631837603037069488166041)
                    ·
                      rfl

theorem cell22_1845749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1845749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845749 prefixEnd_1845749 := by exact prefixLift 1845749
  have htrace : WordTrace (prefixWord ++ tailWord_1845749) baseStart_1845749 baseEnd_1845749 := by
    simpa [prefixWord, tailWord_1845749, baseEnd_1845749] using wordTrace_append hprefix tailTrace_1845749
  have hstable : (prefixWord ++ tailWord_1845749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845749).length < 2 ^ (prefixWord ++ tailWord_1845749).sum := by decide
  have hdescent : baseEnd_1845749 < baseStart_1845749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845754 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1845754 : Nat := 118140960795 + 1845754 * 2 ^ 59
def prefixEnd_1845754 : Nat := 4983230072969 + 3 ^ 40 * 1845754 * 2
def baseEnd_1845754 : Nat := 631839314639251141791025

theorem tailTrace_1845754 : CollatzResearch.WordTrace tailWord_1845754 prefixEnd_1845754 631839314639251141791025 := by
  unfold tailWord_1845754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830044738788990632898079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44880119303437308354394877 16830044738788990632898079)
  ·
    refine ⟨25245067108183485949347119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16830044738788990632898079 25245067108183485949347119)
    ·
      refine ⟨37867600662275228924020679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25245067108183485949347119 37867600662275228924020679)
      ·
        refine ⟨56801400993412843386031019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37867600662275228924020679 56801400993412843386031019)
        ·
          refine ⟨85202101490119265079046529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56801400993412843386031019 85202101490119265079046529)
          ·
            refine ⟨63901576117589448809284897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85202101490119265079046529 63901576117589448809284897)
            ·
              refine ⟨47926182088192086606963673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63901576117589448809284897 47926182088192086606963673)
              ·
                refine ⟨35944636566144064955222755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47926182088192086606963673 35944636566144064955222755)
                ·
                  refine ⟨53916954849216097432834133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35944636566144064955222755 53916954849216097432834133)
                  ·
                    refine ⟨631839314639251141791025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53916954849216097432834133 631839314639251141791025)
                    ·
                      rfl

theorem cell22_1845754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1845754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845754 prefixEnd_1845754 := by exact prefixLift 1845754
  have htrace : WordTrace (prefixWord ++ tailWord_1845754) baseStart_1845754 baseEnd_1845754 := by
    simpa [prefixWord, tailWord_1845754, baseEnd_1845754] using wordTrace_append hprefix tailTrace_1845754
  have hstable : (prefixWord ++ tailWord_1845754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845754).length < 2 ^ (prefixWord ++ tailWord_1845754).sum := by decide
  have hdescent : baseEnd_1845754 < baseStart_1845754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845756 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1845756 : Nat := 118140960795 + 1845756 * 2 ^ 59
def prefixEnd_1845756 : Nat := 4983230072969 + 3 ^ 40 * 1845756 * 2
def baseEnd_1845756 : Nat := 631839999280123803241019

theorem tailTrace_1845756 : CollatzResearch.WordTrace tailWord_1845756 prefixEnd_1845756 631839999280123803241019 := by
  unfold tailWord_1845756
  simp only [CollatzResearch.WordTrace]
  refine ⟨33660125950574358436582561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44880167934099144582110081 33660125950574358436582561)
  ·
    refine ⟨25245094462930768827436921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33660125950574358436582561 25245094462930768827436921)
    ·
      refine ⟨18933820847198076620577691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25245094462930768827436921 18933820847198076620577691)
      ·
        refine ⟨28400731270797114930866537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18933820847198076620577691 28400731270797114930866537)
        ·
          refine ⟨21300548453097836198149903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28400731270797114930866537 21300548453097836198149903)
          ·
            refine ⟨31950822679646754297224855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21300548453097836198149903 31950822679646754297224855)
            ·
              refine ⟨47926234019470131445837283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31950822679646754297224855 47926234019470131445837283)
              ·
                refine ⟨71889351029205197168755925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47926234019470131445837283 71889351029205197168755925)
                ·
                  refine ⟨1684906664746996808642717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 71889351029205197168755925 1684906664746996808642717)
                  ·
                    refine ⟨631839999280123803241019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1684906664746996808642717 631839999280123803241019)
                    ·
                      rfl

theorem cell22_1845756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1845756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845756 prefixEnd_1845756 := by exact prefixLift 1845756
  have htrace : WordTrace (prefixWord ++ tailWord_1845756) baseStart_1845756 baseEnd_1845756 := by
    simpa [prefixWord, tailWord_1845756, baseEnd_1845756] using wordTrace_append hprefix tailTrace_1845756
  have hstable : (prefixWord ++ tailWord_1845756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845756).length < 2 ^ (prefixWord ++ tailWord_1845756).sum := by decide
  have hdescent : baseEnd_1845756 < baseStart_1845756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845786 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_1845786 : Nat := 118140960795 + 1845786 * 2 ^ 59
def prefixEnd_1845786 : Nat := 4983230072969 + 3 ^ 40 * 1845786 * 2
def baseEnd_1845786 : Nat := 210616756297737908330309

theorem tailTrace_1845786 : CollatzResearch.WordTrace tailWord_1845786 prefixEnd_1845786 210616756297737908330309 := by
  unfold tailWord_1845786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830336522760007999189303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44880897394026687997838141 16830336522760007999189303)
  ·
    refine ⟨25245504784140011998783955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16830336522760007999189303 25245504784140011998783955)
    ·
      refine ⟨37868257176210017998175933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25245504784140011998783955 37868257176210017998175933)
      ·
        refine ⟨14200596441078756749315975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37868257176210017998175933 14200596441078756749315975)
        ·
          refine ⟨21300894661618135123973963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14200596441078756749315975 21300894661618135123973963)
          ·
            refine ⟨31951341992427202685960945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21300894661618135123973963 31951341992427202685960945)
            ·
              refine ⟨23963506494320402014470709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31951341992427202685960945 23963506494320402014470709)
              ·
                refine ⟨2246578733842537688856629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23963506494320402014470709 2246578733842537688856629)
                ·
                  refine ⟨210616756297737908330309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2246578733842537688856629 210616756297737908330309)
                  ·
                    rfl

theorem cell22_1845786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_1845786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845786 prefixEnd_1845786 := by exact prefixLift 1845786
  have htrace : WordTrace (prefixWord ++ tailWord_1845786) baseStart_1845786 baseEnd_1845786 := by
    simpa [prefixWord, tailWord_1845786, baseEnd_1845786] using wordTrace_append hprefix tailTrace_1845786
  have hstable : (prefixWord ++ tailWord_1845786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845786).length < 2 ^ (prefixWord ++ tailWord_1845786).sum := by decide
  have hdescent : baseEnd_1845786 < baseStart_1845786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845837 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1845837 : Nat := 118140960795 + 1845837 * 2 ^ 59
def prefixEnd_1845837 : Nat := 4983230072969 + 3 ^ 40 * 1845837 * 2
def baseEnd_1845837 : Nat := 210622575745155530655257

theorem tailTrace_1845837 : CollatzResearch.WordTrace tailWord_1845837 prefixEnd_1845837 210622575745155530655257 := by
  unfold tailWord_1845837
  simp only [CollatzResearch.WordTrace]
  refine ⟨67323206213855267706863765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44882137475903511804575843 67323206213855267706863765)
  ·
    refine ⟨3155775291274465673759239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67323206213855267706863765 3155775291274465673759239)
    ·
      refine ⟨4733662936911698510638859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155775291274465673759239 4733662936911698510638859)
      ·
        refine ⟨7100494405367547765958289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733662936911698510638859 7100494405367547765958289)
        ·
          refine ⟨5325370804025660824468717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100494405367547765958289 5325370804025660824468717)
          ·
            refine ⟨1997014051509622809175769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5325370804025660824468717 1997014051509622809175769)
            ·
              refine ⟨1497760538632217106881827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997014051509622809175769 1497760538632217106881827)
              ·
                refine ⟨2246640807948325660322741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497760538632217106881827 2246640807948325660322741)
                ·
                  refine ⟨210622575745155530655257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2246640807948325660322741 210622575745155530655257)
                  ·
                    rfl

theorem cell22_1845837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1845837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845837 prefixEnd_1845837 := by exact prefixLift 1845837
  have htrace : WordTrace (prefixWord ++ tailWord_1845837) baseStart_1845837 baseEnd_1845837 := by
    simpa [prefixWord, tailWord_1845837, baseEnd_1845837] using wordTrace_append hprefix tailTrace_1845837
  have hstable : (prefixWord ++ tailWord_1845837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845837).length < 2 ^ (prefixWord ++ tailWord_1845837).sum := by decide
  have hdescent : baseEnd_1845837 < baseStart_1845837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845893 : List Nat := [1, 3, 1, 1, 4, 4, 1, 7]
def baseStart_1845893 : Nat := 118140960795 + 1845893 * 2 ^ 59
def prefixEnd_1845893 : Nat := 4983230072969 + 3 ^ 40 * 1845893 * 2
def baseEnd_1845893 : Nat := 70209655242211234729511

theorem tailTrace_1845893 : CollatzResearch.WordTrace tailWord_1845893 prefixEnd_1845893 70209655242211234729511 := by
  unfold tailWord_1845893
  simp only [CollatzResearch.WordTrace]
  refine ⟨67325248701652389270902333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44883499134434926180601555 67325248701652389270902333)
  ·
    refine ⟨25246968263119645976588375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67325248701652389270902333 25246968263119645976588375)
    ·
      refine ⟨37870452394679468964882563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25246968263119645976588375 37870452394679468964882563)
      ·
        refine ⟨56805678592019203447323845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37870452394679468964882563 56805678592019203447323845)
        ·
          refine ⟨10651064736003600646373221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56805678592019203447323845 10651064736003600646373221)
          ·
            refine ⟨1997074638000675121194979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10651064736003600646373221 1997074638000675121194979)
            ·
              refine ⟨2995611957001012681792469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997074638000675121194979 2995611957001012681792469)
              ·
                refine ⟨70209655242211234729511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2995611957001012681792469 70209655242211234729511)
                ·
                  rfl

theorem cell22_1845893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 7].length) (baseStart_1845893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845893 prefixEnd_1845893 := by exact prefixLift 1845893
  have htrace : WordTrace (prefixWord ++ tailWord_1845893) baseStart_1845893 baseEnd_1845893 := by
    simpa [prefixWord, tailWord_1845893, baseEnd_1845893] using wordTrace_append hprefix tailTrace_1845893
  have hstable : (prefixWord ++ tailWord_1845893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845893).length < 2 ^ (prefixWord ++ tailWord_1845893).sum := by decide
  have hdescent : baseEnd_1845893 < baseStart_1845893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845985 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1845985 : Nat := 118140960795 + 1845985 * 2 ^ 59
def prefixEnd_1845985 : Nat := 4983230072969 + 3 ^ 40 * 1845985 * 2
def baseEnd_1845985 : Nat := 631918390660043539265317

theorem tailTrace_1845985 : CollatzResearch.WordTrace tailWord_1845985 prefixEnd_1845985 631918390660043539265317 := by
  unfold tailWord_1845985
  simp only [CollatzResearch.WordTrace]
  refine ⟨67328604217319088983251409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44885736144879392655500939 67328604217319088983251409)
  ·
    refine ⟨50496453162989316737438557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67328604217319088983251409 50496453162989316737438557)
    ·
      refine ⟨18936169936120993776539459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50496453162989316737438557 18936169936120993776539459)
      ·
        refine ⟨28404254904181490664809189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18936169936120993776539459 28404254904181490664809189)
        ·
          refine ⟨5325797794534029499651723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28404254904181490664809189 5325797794534029499651723)
          ·
            refine ⟨7988696691801044249477585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325797794534029499651723 7988696691801044249477585)
            ·
              refine ⟨5991522518850783187108189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7988696691801044249477585 5991522518850783187108189)
              ·
                refine ⟨2246820944569043695165571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5991522518850783187108189 2246820944569043695165571)
                ·
                  refine ⟨3370231416853565542748357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246820944569043695165571 3370231416853565542748357)
                  ·
                    refine ⟨631918390660043539265317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370231416853565542748357 631918390660043539265317)
                    ·
                      rfl

theorem cell22_1845985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1845985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845985 prefixEnd_1845985 := by exact prefixLift 1845985
  have htrace : WordTrace (prefixWord ++ tailWord_1845985) baseStart_1845985 baseEnd_1845985 := by
    simpa [prefixWord, tailWord_1845985, baseEnd_1845985] using wordTrace_append hprefix tailTrace_1845985
  have hstable : (prefixWord ++ tailWord_1845985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845985).length < 2 ^ (prefixWord ++ tailWord_1845985).sum := by decide
  have hdescent : baseEnd_1845985 < baseStart_1845985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846013 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1846013 : Nat := 118140960795 + 1846013 * 2 ^ 59
def prefixEnd_1846013 : Nat := 4983230072969 + 3 ^ 40 * 1846013 * 2
def baseEnd_1846013 : Nat := 631927975632260799565231

theorem tailTrace_1846013 : CollatzResearch.WordTrace tailWord_1846013 prefixEnd_1846013 631927975632260799565231 := by
  unfold tailWord_1846013
  simp only [CollatzResearch.WordTrace]
  refine ⟨67329625461217649765270693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44886416974145099843513795 67329625461217649765270693)
  ·
    refine ⟨12624304773978309330988255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67329625461217649765270693 12624304773978309330988255)
    ·
      refine ⟨18936457160967463996482383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12624304773978309330988255 18936457160967463996482383)
      ·
        refine ⟨28404685741451195994723575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18936457160967463996482383 28404685741451195994723575)
        ·
          refine ⟨42607028612176793992085363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28404685741451195994723575 42607028612176793992085363)
          ·
            refine ⟨63910542918265190988128045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42607028612176793992085363 63910542918265190988128045)
            ·
              refine ⟨23966453594349446620548017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63910542918265190988128045 23966453594349446620548017)
              ·
                refine ⟨17974840195762084965411013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23966453594349446620548017 17974840195762084965411013)
                ·
                  refine ⟨3370282536705390931014565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17974840195762084965411013 3370282536705390931014565)
                  ·
                    refine ⟨631927975632260799565231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370282536705390931014565 631927975632260799565231)
                    ·
                      rfl

theorem cell22_1846013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1846013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846013 prefixEnd_1846013 := by exact prefixLift 1846013
  have htrace : WordTrace (prefixWord ++ tailWord_1846013) baseStart_1846013 baseEnd_1846013 := by
    simpa [prefixWord, tailWord_1846013, baseEnd_1846013] using wordTrace_append hprefix tailTrace_1846013
  have hstable : (prefixWord ++ tailWord_1846013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846013).length < 2 ^ (prefixWord ++ tailWord_1846013).sum := by decide
  have hdescent : baseEnd_1846013 < baseStart_1846013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846045 : List Nat := [1, 4, 2, 4, 1, 10]
def baseStart_1846045 : Nat := 118140960795 + 1846045 * 2 ^ 59
def prefixEnd_1846045 : Nat := 4983230072969 + 3 ^ 40 * 1846045 * 2
def baseEnd_1846045 : Nat := 7801715183780535589693

theorem tailTrace_1846045 : CollatzResearch.WordTrace tailWord_1846045 prefixEnd_1846045 7801715183780535589693 := by
  unfold tailWord_1846045
  simp only [CollatzResearch.WordTrace]
  refine ⟨67330792597101719230435589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44887195064734479486957059 67330792597101719230435589)
  ·
    refine ⟨12624523611956572355706673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67330792597101719230435589 12624523611956572355706673)
    ·
      refine ⟨9468392708967429266780005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12624523611956572355706673 9468392708967429266780005)
      ·
        refine ⟨1775323632931392987521251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9468392708967429266780005 1775323632931392987521251)
        ·
          refine ⟨2662985449397089481281877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775323632931392987521251 2662985449397089481281877)
          ·
            refine ⟨7801715183780535589693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2662985449397089481281877 7801715183780535589693)
            ·
              rfl

theorem cell22_1846045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 10].length) (baseStart_1846045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846045 prefixEnd_1846045 := by exact prefixLift 1846045
  have htrace : WordTrace (prefixWord ++ tailWord_1846045) baseStart_1846045 baseEnd_1846045 := by
    simpa [prefixWord, tailWord_1846045, baseEnd_1846045] using wordTrace_append hprefix tailTrace_1846045
  have hstable : (prefixWord ++ tailWord_1846045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846045).length < 2 ^ (prefixWord ++ tailWord_1846045).sum := by decide
  have hdescent : baseEnd_1846045 < baseStart_1846045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846060 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_1846060 : Nat := 118140960795 + 1846060 * 2 ^ 59
def prefixEnd_1846060 : Nat := 4983230072969 + 3 ^ 40 * 1846060 * 2
def baseEnd_1846060 : Nat := 631944064692768343640087

theorem tailTrace_1846060 : CollatzResearch.WordTrace tailWord_1846060 prefixEnd_1846060 631944064692768343640087 := by
  unfold tailWord_1846060
  simp only [CollatzResearch.WordTrace]
  refine ⟨33665669846023688396115817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44887559794698251194821089 33665669846023688396115817)
  ·
    refine ⟨25249252384517766297086863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33665669846023688396115817 25249252384517766297086863)
    ·
      refine ⟨37873878576776649445630295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25249252384517766297086863 37873878576776649445630295)
      ·
        refine ⟨56810817865164974168445443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37873878576776649445630295 56810817865164974168445443)
        ·
          refine ⟨85216226797747461252668165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56810817865164974168445443 85216226797747461252668165)
          ·
            refine ⟨15978042524577648984875281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85216226797747461252668165 15978042524577648984875281)
            ·
              refine ⟨11983531893433236738656461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15978042524577648984875281 11983531893433236738656461)
              ·
                refine ⟨4493824460037463776996173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11983531893433236738656461 4493824460037463776996173)
                ·
                  refine ⟨1685184172514048916373565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4493824460037463776996173 1685184172514048916373565)
                  ·
                    refine ⟨631944064692768343640087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685184172514048916373565 631944064692768343640087)
                    ·
                      rfl

theorem cell22_1846060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_1846060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846060 prefixEnd_1846060 := by exact prefixLift 1846060
  have htrace : WordTrace (prefixWord ++ tailWord_1846060) baseStart_1846060 baseEnd_1846060 := by
    simpa [prefixWord, tailWord_1846060, baseEnd_1846060] using wordTrace_append hprefix tailTrace_1846060
  have hstable : (prefixWord ++ tailWord_1846060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846060).length < 2 ^ (prefixWord ++ tailWord_1846060).sum := by decide
  have hdescent : baseEnd_1846060 < baseStart_1846060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846062 : List Nat := [4, 1, 3, 2, 1, 3, 1, 7]
def baseStart_1846062 : Nat := 118140960795 + 1846062 * 2 ^ 59
def prefixEnd_1846062 : Nat := 4983230072969 + 3 ^ 40 * 1846062 * 2
def baseEnd_1846062 : Nat := 70216083259293445010009

theorem tailTrace_1846062 : CollatzResearch.WordTrace tailWord_1846062 prefixEnd_1846062 70216083259293445010009 := by
  unfold tailWord_1846062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416426579755016391725555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44887608425360087422536293 8416426579755016391725555)
  ·
    refine ⟨12624639869632524587588333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416426579755016391725555 12624639869632524587588333)
    ·
      refine ⟨4734239951112196720345625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12624639869632524587588333 4734239951112196720345625)
      ·
        refine ⟨3550679963334147540259219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4734239951112196720345625 3550679963334147540259219)
        ·
          refine ⟨5326019945001221310388829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550679963334147540259219 5326019945001221310388829)
          ·
            refine ⟨1997257479375457991395811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5326019945001221310388829 1997257479375457991395811)
            ·
              refine ⟨2995886219063186987093717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997257479375457991395811 2995886219063186987093717)
              ·
                refine ⟨70216083259293445010009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2995886219063186987093717 70216083259293445010009)
                ·
                  rfl

theorem cell22_1846062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_1846062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846062 prefixEnd_1846062 := by exact prefixLift 1846062
  have htrace : WordTrace (prefixWord ++ tailWord_1846062) baseStart_1846062 baseEnd_1846062 := by
    simpa [prefixWord, tailWord_1846062, baseEnd_1846062] using wordTrace_append hprefix tailTrace_1846062
  have hstable : (prefixWord ++ tailWord_1846062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846062).length < 2 ^ (prefixWord ++ tailWord_1846062).sum := by decide
  have hdescent : baseEnd_1846062 < baseStart_1846062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846081 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1846081 : Nat := 118140960795 + 1846081 * 2 ^ 59
def prefixEnd_1846081 : Nat := 4983230072969 + 3 ^ 40 * 1846081 * 2
def baseEnd_1846081 : Nat := 631951253421931288865023

theorem tailTrace_1846081 : CollatzResearch.WordTrace tailWord_1846081 prefixEnd_1846081 631951253421931288865023 := by
  unfold tailWord_1846081
  simp only [CollatzResearch.WordTrace]
  refine ⟨67332105624971297378746097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44888070416647531585830731 67332105624971297378746097)
  ·
    refine ⟨50499079218728473034059573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67332105624971297378746097 50499079218728473034059573)
    ·
      refine ⟨4734288676755794346943085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50499079218728473034059573 4734288676755794346943085)
      ·
        refine ⟨1775358253783422880103657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4734288676755794346943085 1775358253783422880103657)
        ·
          refine ⟨1331518690337567160077743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775358253783422880103657 1331518690337567160077743)
          ·
            refine ⟨1997278035506350740116615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331518690337567160077743 1997278035506350740116615)
            ·
              refine ⟨2995917053259526110174923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997278035506350740116615 2995917053259526110174923)
              ·
                refine ⟨4493875579889289165262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995917053259526110174923 4493875579889289165262385)
                ·
                  refine ⟨3370406684916966873946789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493875579889289165262385 3370406684916966873946789)
                  ·
                    refine ⟨631951253421931288865023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370406684916966873946789 631951253421931288865023)
                    ·
                      rfl

theorem cell22_1846081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1846081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846081 prefixEnd_1846081 := by exact prefixLift 1846081
  have htrace : WordTrace (prefixWord ++ tailWord_1846081) baseStart_1846081 baseEnd_1846081 := by
    simpa [prefixWord, tailWord_1846081, baseEnd_1846081] using wordTrace_append hprefix tailTrace_1846081
  have hstable : (prefixWord ++ tailWord_1846081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846081).length < 2 ^ (prefixWord ++ tailWord_1846081).sum := by decide
  have hdescent : baseEnd_1846081 < baseStart_1846081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846088 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_1846088 : Nat := 118140960795 + 1846088 * 2 ^ 59
def prefixEnd_1846088 : Nat := 4983230072969 + 3 ^ 40 * 1846088 * 2
def baseEnd_1846088 : Nat := 631953649664985603940001

theorem tailTrace_1846088 : CollatzResearch.WordTrace tailWord_1846088 prefixEnd_1846088 631953649664985603940001 := by
  unfold tailWord_1846088
  simp only [CollatzResearch.WordTrace]
  refine ⟨33666180467972968787125459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44888240623963958382833945 33666180467972968787125459)
  ·
    refine ⟨50499270701959453180688189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33666180467972968787125459 50499270701959453180688189)
    ·
      refine ⟨18937226513234794942758071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50499270701959453180688189 18937226513234794942758071)
      ·
        refine ⟨28405839769852192414137107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18937226513234794942758071 28405839769852192414137107)
        ·
          refine ⟨42608759654778288621205661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28405839769852192414137107 42608759654778288621205661)
          ·
            refine ⟨15978284870541858232952123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42608759654778288621205661 15978284870541858232952123)
            ·
              refine ⟨23967427305812787349428185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15978284870541858232952123 23967427305812787349428185)
              ·
                refine ⟨17975570479359590512071139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23967427305812787349428185 17975570479359590512071139)
                ·
                  refine ⟨26963355719039385768106709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17975570479359590512071139 26963355719039385768106709)
                  ·
                    refine ⟨631953649664985603940001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26963355719039385768106709 631953649664985603940001)
                    ·
                      rfl

theorem cell22_1846088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_1846088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846088 prefixEnd_1846088 := by exact prefixLift 1846088
  have htrace : WordTrace (prefixWord ++ tailWord_1846088) baseStart_1846088 baseEnd_1846088 := by
    simpa [prefixWord, tailWord_1846088, baseEnd_1846088] using wordTrace_append hprefix tailTrace_1846088
  have hstable : (prefixWord ++ tailWord_1846088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846088).length < 2 ^ (prefixWord ++ tailWord_1846088).sum := by decide
  have hdescent : baseEnd_1846088 < baseStart_1846088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846137 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_1846137 : Nat := 118140960795 + 1846137 * 2 ^ 59
def prefixEnd_1846137 : Nat := 4983230072969 + 3 ^ 40 * 1846137 * 2
def baseEnd_1846137 : Nat := 631970423366365809464851

theorem tailTrace_1846137 : CollatzResearch.WordTrace tailWord_1846137 prefixEnd_1846137 631970423366365809464851 := by
  unfold tailWord_1846137
  simp only [CollatzResearch.WordTrace]
  refine ⟨67334148112768418942784665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44889432075178945961856443 67334148112768418942784665)
  ·
    refine ⟨50500611084576314207088499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67334148112768418942784665 50500611084576314207088499)
    ·
      refine ⟨75750916626864471310632749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50500611084576314207088499 75750916626864471310632749)
      ·
        refine ⟨28406593735074176741487281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75750916626864471310632749 28406593735074176741487281)
        ·
          refine ⟨21304945301305632556115461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28406593735074176741487281 21304945301305632556115461)
          ·
            refine ⟨3994677243994806104271649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21304945301305632556115461 3994677243994806104271649)
            ·
              refine ⟨2996007932996104578203737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994677243994806104271649 2996007932996104578203737)
              ·
                refine ⟨2247005949747078433652803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996007932996104578203737 2247005949747078433652803)
                ·
                  refine ⟨3370508924620617650479205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247005949747078433652803 3370508924620617650479205)
                  ·
                    refine ⟨631970423366365809464851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370508924620617650479205 631970423366365809464851)
                    ·
                      rfl

theorem cell22_1846137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_1846137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846137 prefixEnd_1846137 := by exact prefixLift 1846137
  have htrace : WordTrace (prefixWord ++ tailWord_1846137) baseStart_1846137 baseEnd_1846137 := by
    simpa [prefixWord, tailWord_1846137, baseEnd_1846137] using wordTrace_append hprefix tailTrace_1846137
  have hstable : (prefixWord ++ tailWord_1846137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846137).length < 2 ^ (prefixWord ++ tailWord_1846137).sum := by decide
  have hdescent : baseEnd_1846137 < baseStart_1846137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846165 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1846165 : Nat := 118140960795 + 1846165 * 2 ^ 59
def prefixEnd_1846165 : Nat := 4983230072969 + 3 ^ 40 * 1846165 * 2
def baseEnd_1846165 : Nat := 631980008338583069764765

theorem tailTrace_1846165 : CollatzResearch.WordTrace tailWord_1846165 prefixEnd_1846165 631980008338583069764765 := by
  unfold tailWord_1846165
  simp only [CollatzResearch.WordTrace]
  refine ⟨67335169356666979724803949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44890112904444653149869299 67335169356666979724803949)
  ·
    refine ⟨25250688508750117396801481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67335169356666979724803949 25250688508750117396801481)
    ·
      refine ⟨18938016381562588047601111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25250688508750117396801481 18938016381562588047601111)
      ·
        refine ⟨28407024572343882071401667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18938016381562588047601111 28407024572343882071401667)
        ·
          refine ⟨42610536858515823107102501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28407024572343882071401667 42610536858515823107102501)
          ·
            refine ⟨7989475660971716832581719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42610536858515823107102501 7989475660971716832581719)
            ·
              refine ⟨11984213491457575248872579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989475660971716832581719 11984213491457575248872579)
              ·
                refine ⟨17976320237186362873308869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11984213491457575248872579 17976320237186362873308869)
                ·
                  refine ⟨3370560044472443038745413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17976320237186362873308869 3370560044472443038745413)
                  ·
                    refine ⟨631980008338583069764765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370560044472443038745413 631980008338583069764765)
                    ·
                      rfl

theorem cell22_1846165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1846165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846165 prefixEnd_1846165 := by exact prefixLift 1846165
  have htrace : WordTrace (prefixWord ++ tailWord_1846165) baseStart_1846165 baseEnd_1846165 := by
    simpa [prefixWord, tailWord_1846165, baseEnd_1846165] using wordTrace_append hprefix tailTrace_1846165
  have hstable : (prefixWord ++ tailWord_1846165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846165).length < 2 ^ (prefixWord ++ tailWord_1846165).sum := by decide
  have hdescent : baseEnd_1846165 < baseStart_1846165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846167 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 2, 3]
def baseStart_1846167 : Nat := 118140960795 + 1846167 * 2 ^ 59
def prefixEnd_1846167 : Nat := 4983230072969 + 3 ^ 40 * 1846167 * 2
def baseEnd_1846167 : Nat := 631980692979455731214759

theorem tailTrace_1846167 : CollatzResearch.WordTrace tailWord_1846167 prefixEnd_1846167 631980692979455731214759 := by
  unfold tailWord_1846167
  simp only [CollatzResearch.WordTrace]
  refine ⟨67335242302659734066376755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44890161535106489377584503 67335242302659734066376755)
  ·
    refine ⟨101002863453989601099565133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67335242302659734066376755 101002863453989601099565133)
    ·
      refine ⟨37876073795246100412336925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101002863453989601099565133 37876073795246100412336925)
      ·
        refine ⟨14203527673217287654626347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37876073795246100412336925 14203527673217287654626347)
        ·
          refine ⟨21305291509825931481939521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14203527673217287654626347 21305291509825931481939521)
          ·
            refine ⟨15978968632369448611454641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21305291509825931481939521 15978968632369448611454641)
            ·
              refine ⟨11984226474277086458590981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15978968632369448611454641 11984226474277086458590981)
              ·
                refine ⟨2247042463926953710985809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11984226474277086458590981 2247042463926953710985809)
                ·
                  refine ⟨1685281847945215283239357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2247042463926953710985809 1685281847945215283239357)
                  ·
                    refine ⟨631980692979455731214759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685281847945215283239357 631980692979455731214759)
                    ·
                      rfl

theorem cell22_1846167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_1846167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846167 prefixEnd_1846167 := by exact prefixLift 1846167
  have htrace : WordTrace (prefixWord ++ tailWord_1846167) baseStart_1846167 baseEnd_1846167 := by
    simpa [prefixWord, tailWord_1846167, baseEnd_1846167] using wordTrace_append hprefix tailTrace_1846167
  have hstable : (prefixWord ++ tailWord_1846167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846167).length < 2 ^ (prefixWord ++ tailWord_1846167).sum := by decide
  have hdescent : baseEnd_1846167 < baseStart_1846167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846180 : List Nat := [2, 3, 1, 2, 1, 2, 4, 7]
def baseStart_1846180 : Nat := 118140960795 + 1846180 * 2 ^ 59
def prefixEnd_1846180 : Nat := 4983230072969 + 3 ^ 40 * 1846180 * 2
def baseEnd_1846180 : Nat := 70220571460569781182191

theorem tailTrace_1846180 : CollatzResearch.WordTrace tailWord_1846180 prefixEnd_1846180 70220571460569781182191 := by
  unfold tailWord_1846180
  simp only [CollatzResearch.WordTrace]
  refine ⟨33667858225806318643299997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44890477634408424857733329 33667858225806318643299997)
  ·
    refine ⟨12625446834677369491237499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33667858225806318643299997 12625446834677369491237499)
    ·
      refine ⟨18938170252016054236856249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12625446834677369491237499 18938170252016054236856249)
      ·
        refine ⟨14203627689012040677642187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18938170252016054236856249 14203627689012040677642187)
        ·
          refine ⟨21305441533518061016463281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14203627689012040677642187 21305441533518061016463281)
          ·
            refine ⟨15979081150138545762347461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21305441533518061016463281 15979081150138545762347461)
            ·
              refine ⟨2996077715650977330440149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15979081150138545762347461 2996077715650977330440149)
              ·
                refine ⟨70220571460569781182191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2996077715650977330440149 70220571460569781182191)
                ·
                  rfl

theorem cell22_1846180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_1846180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846180 prefixEnd_1846180 := by exact prefixLift 1846180
  have htrace : WordTrace (prefixWord ++ tailWord_1846180) baseStart_1846180 baseEnd_1846180 := by
    simpa [prefixWord, tailWord_1846180, baseEnd_1846180] using wordTrace_append hprefix tailTrace_1846180
  have hstable : (prefixWord ++ tailWord_1846180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846180).length < 2 ^ (prefixWord ++ tailWord_1846180).sum := by decide
  have hdescent : baseEnd_1846180 < baseStart_1846180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846315 : List Nat := [1, 1, 1, 1, 2, 1, 7, 8]
def baseStart_1846315 : Nat := 118140960795 + 1846315 * 2 ^ 59
def prefixEnd_1846315 : Nat := 4983230072969 + 3 ^ 40 * 1846315 * 2
def baseEnd_1846315 : Nat := 70225706267114742057145

theorem tailTrace_1846315 : CollatzResearch.WordTrace tailWord_1846315 prefixEnd_1846315 70225706267114742057145 := by
  unfold tailWord_1846315
  simp only [CollatzResearch.WordTrace]
  refine ⟨67340640306123555342764399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44893760204082370228509599 67340640306123555342764399)
  ·
    refine ⟨101010960459185333014146599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67340640306123555342764399 101010960459185333014146599)
    ·
      refine ⟨151516440688777999521219899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101010960459185333014146599 151516440688777999521219899)
      ·
        refine ⟨227274661033166999281829849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151516440688777999521219899 227274661033166999281829849)
        ·
          refine ⟨170455995774875249461372387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227274661033166999281829849 170455995774875249461372387)
          ·
            refine ⟨255683993662312874192058581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170455995774875249461372387 255683993662312874192058581)
            ·
              refine ⟨5992593601460457988876373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 255683993662312874192058581 5992593601460457988876373)
              ·
                refine ⟨70225706267114742057145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5992593601460457988876373 70225706267114742057145)
                ·
                  rfl

theorem cell22_1846315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 8].length) (baseStart_1846315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846315 prefixEnd_1846315 := by exact prefixLift 1846315
  have htrace : WordTrace (prefixWord ++ tailWord_1846315) baseStart_1846315 baseEnd_1846315 := by
    simpa [prefixWord, tailWord_1846315, baseEnd_1846315] using wordTrace_append hprefix tailTrace_1846315
  have hstable : (prefixWord ++ tailWord_1846315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846315).length < 2 ^ (prefixWord ++ tailWord_1846315).sum := by decide
  have hdescent : baseEnd_1846315 < baseStart_1846315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846332 : List Nat := [2, 2, 2, 2, 2, 4, 8]
def baseStart_1846332 : Nat := 118140960795 + 1846332 * 2 ^ 59
def prefixEnd_1846332 : Nat := 4983230072969 + 3 ^ 40 * 1846332 * 2
def baseEnd_1846332 : Nat := 23408784290794455586639

theorem tailTrace_1846332 : CollatzResearch.WordTrace tailWord_1846332 prefixEnd_1846332 23408784290794455586639 := by
  unfold tailWord_1846332
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670630173530983623066625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44894173564707978164088833 33670630173530983623066625)
  ·
    refine ⟨25252972630148237717299969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33670630173530983623066625 25252972630148237717299969)
    ·
      refine ⟨18939729472611178287974977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25252972630148237717299969 18939729472611178287974977)
      ·
        refine ⟨14204797104458383715981233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18939729472611178287974977 14204797104458383715981233)
        ·
          refine ⟨10653597828343787786985925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14204797104458383715981233 10653597828343787786985925)
          ·
            refine ⟨1997549592814460210059861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10653597828343787786985925 1997549592814460210059861)
            ·
              refine ⟨23408784290794455586639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1997549592814460210059861 23408784290794455586639)
              ·
                rfl

theorem cell22_1846332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 8].length) (baseStart_1846332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846332 prefixEnd_1846332 := by exact prefixLift 1846332
  have htrace : WordTrace (prefixWord ++ tailWord_1846332) baseStart_1846332 baseEnd_1846332 := by
    simpa [prefixWord, tailWord_1846332, baseEnd_1846332] using wordTrace_append hprefix tailTrace_1846332
  have hstable : (prefixWord ++ tailWord_1846332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846332).length < 2 ^ (prefixWord ++ tailWord_1846332).sum := by decide
  have hdescent : baseEnd_1846332 < baseStart_1846332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846334 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1846334 : Nat := 118140960795 + 1846334 * 2 ^ 59
def prefixEnd_1846334 : Nat := 4983230072969 + 3 ^ 40 * 1846334 * 2
def baseEnd_1846334 : Nat := 632037860492322962289247

theorem tailTrace_1846334 : CollatzResearch.WordTrace tailWord_1846334 prefixEnd_1846334 632037860492322962289247 := by
  unfold tailWord_1846334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417666661631840198463257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44894222195369814391804037 8417666661631840198463257)
  ·
    refine ⟨6313249996223880148847443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8417666661631840198463257 6313249996223880148847443)
    ·
      refine ⟨9469874994335820223271165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6313249996223880148847443 9469874994335820223271165)
      ·
        refine ⟨3551203122875932583726687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9469874994335820223271165 3551203122875932583726687)
        ·
          refine ⟨5326804684313898875590031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551203122875932583726687 5326804684313898875590031)
          ·
            refine ⟨7990207026470848313385047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326804684313898875590031 7990207026470848313385047)
            ·
              refine ⟨11985310539706272470077571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990207026470848313385047 11985310539706272470077571)
              ·
                refine ⟨17977965809559408705116357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985310539706272470077571 17977965809559408705116357)
                ·
                  refine ⟨3370868589292389132209317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17977965809559408705116357 3370868589292389132209317)
                  ·
                    refine ⟨632037860492322962289247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370868589292389132209317 632037860492322962289247)
                    ·
                      rfl

theorem cell22_1846334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1846334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846334 prefixEnd_1846334 := by exact prefixLift 1846334
  have htrace : WordTrace (prefixWord ++ tailWord_1846334) baseStart_1846334 baseEnd_1846334 := by
    simpa [prefixWord, tailWord_1846334, baseEnd_1846334] using wordTrace_append hprefix tailTrace_1846334
  have hstable : (prefixWord ++ tailWord_1846334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846334).length < 2 ^ (prefixWord ++ tailWord_1846334).sum := by decide
  have hdescent : baseEnd_1846334 < baseStart_1846334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846349 : List Nat := [1, 6, 1, 1, 1, 3, 2, 7]
def baseStart_1846349 : Nat := 118140960795 + 1846349 * 2 ^ 59
def prefixEnd_1846349 : Nat := 4983230072969 + 3 ^ 40 * 1846349 * 2
def baseEnd_1846349 : Nat := 70226999477651991462689

theorem tailTrace_1846349 : CollatzResearch.WordTrace tailWord_1846349 prefixEnd_1846349 70226999477651991462689 := by
  unfold tailWord_1846349
  simp only [CollatzResearch.WordTrace]
  refine ⟨67341880388000379149502101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44894586925333586099668067 67341880388000379149502101)
  ·
    refine ⟨3156650643187517772632911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67341880388000379149502101 3156650643187517772632911)
    ·
      refine ⟨4734975964781276658949367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156650643187517772632911 4734975964781276658949367)
      ·
        refine ⟨7102463947171914988424051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734975964781276658949367 7102463947171914988424051)
        ·
          refine ⟨10653695920757872482636077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7102463947171914988424051 10653695920757872482636077)
          ·
            refine ⟨3995135970284202180988529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10653695920757872482636077 3995135970284202180988529)
            ·
              refine ⟨2996351977713151635741397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3995135970284202180988529 2996351977713151635741397)
              ·
                refine ⟨70226999477651991462689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2996351977713151635741397 70226999477651991462689)
                ·
                  rfl

theorem cell22_1846349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 7].length) (baseStart_1846349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846349 prefixEnd_1846349 := by exact prefixLift 1846349
  have htrace : WordTrace (prefixWord ++ tailWord_1846349) baseStart_1846349 baseEnd_1846349 := by
    simpa [prefixWord, tailWord_1846349, baseEnd_1846349] using wordTrace_append hprefix tailTrace_1846349
  have hstable : (prefixWord ++ tailWord_1846349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846349).length < 2 ^ (prefixWord ++ tailWord_1846349).sum := by decide
  have hdescent : baseEnd_1846349 < baseStart_1846349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846364 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1846364 : Nat := 118140960795 + 1846364 * 2 ^ 59
def prefixEnd_1846364 : Nat := 4983230072969 + 3 ^ 40 * 1846364 * 2
def baseEnd_1846364 : Nat := 632048130105412884039155

theorem tailTrace_1846364 : CollatzResearch.WordTrace tailWord_1846364 prefixEnd_1846364 632048130105412884039155 := by
  unfold tailWord_1846364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33671213741473018355649073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44894951655297357807532097 33671213741473018355649073)
  ·
    refine ⟨25253410306104763766736805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33671213741473018355649073 25253410306104763766736805)
    ·
      refine ⟨4735014432394643206263151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25253410306104763766736805 4735014432394643206263151)
      ·
        refine ⟨7102521648591964809394727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4735014432394643206263151 7102521648591964809394727)
        ·
          refine ⟨10653782472887947214092091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7102521648591964809394727 10653782472887947214092091)
          ·
            refine ⟨15980673709331920821138137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653782472887947214092091 15980673709331920821138137)
            ·
              refine ⟨11985505281998940615853603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15980673709331920821138137 11985505281998940615853603)
              ·
                refine ⟨17978257922998410923780405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985505281998940615853603 17978257922998410923780405)
                ·
                  refine ⟨1685461680281101024104413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17978257922998410923780405 1685461680281101024104413)
                  ·
                    refine ⟨632048130105412884039155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685461680281101024104413 632048130105412884039155)
                    ·
                      rfl

theorem cell22_1846364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1846364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846364 prefixEnd_1846364 := by exact prefixLift 1846364
  have htrace : WordTrace (prefixWord ++ tailWord_1846364) baseStart_1846364 baseEnd_1846364 := by
    simpa [prefixWord, tailWord_1846364, baseEnd_1846364] using wordTrace_append hprefix tailTrace_1846364
  have hstable : (prefixWord ++ tailWord_1846364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846364).length < 2 ^ (prefixWord ++ tailWord_1846364).sum := by decide
  have hdescent : baseEnd_1846364 < baseStart_1846364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846366 : List Nat := [4, 4, 1, 1, 1, 1, 2, 8]
def baseStart_1846366 : Nat := 118140960795 + 1846366 * 2 ^ 59
def prefixEnd_1846366 : Nat := 4983230072969 + 3 ^ 40 * 1846366 * 2
def baseEnd_1846366 : Nat := 70227646082920616165461

theorem tailTrace_1846366 : CollatzResearch.WordTrace tailWord_1846366 prefixEnd_1846366 70227646082920616165461 := by
  unfold tailWord_1846366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417812553617348881608869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44895000285959194035247301 8417812553617348881608869)
  ·
    refine ⟨1578339853803252915301663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8417812553617348881608869 1578339853803252915301663)
    ·
      refine ⟨2367509780704879372952495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578339853803252915301663 2367509780704879372952495)
      ·
        refine ⟨3551264671057319059428743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367509780704879372952495 3551264671057319059428743)
        ·
          refine ⟨5326897006585978589143115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551264671057319059428743 5326897006585978589143115)
          ·
            refine ⟨7990345509878967883714673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326897006585978589143115 7990345509878967883714673)
            ·
              refine ⟨5992759132409225912786005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990345509878967883714673 5992759132409225912786005)
              ·
                refine ⟨70227646082920616165461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5992759132409225912786005 70227646082920616165461)
                ·
                  rfl

theorem cell22_1846366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_1846366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846366 prefixEnd_1846366 := by exact prefixLift 1846366
  have htrace : WordTrace (prefixWord ++ tailWord_1846366) baseStart_1846366 baseEnd_1846366 := by
    simpa [prefixWord, tailWord_1846366, baseEnd_1846366] using wordTrace_append hprefix tailTrace_1846366
  have hstable : (prefixWord ++ tailWord_1846366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846366).length < 2 ^ (prefixWord ++ tailWord_1846366).sum := by decide
  have hdescent : baseEnd_1846366 < baseStart_1846366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846424 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_1846424 : Nat := 118140960795 + 1846424 * 2 ^ 59
def prefixEnd_1846424 : Nat := 4983230072969 + 3 ^ 40 * 1846424 * 2
def baseEnd_1846424 : Nat := 632068669331592727538971

theorem tailTrace_1846424 : CollatzResearch.WordTrace tailWord_1846424 prefixEnd_1846424 632068669331592727538971 := by
  unfold tailWord_1846424
  simp only [CollatzResearch.WordTrace]
  refine ⟨33672307931364333479241163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44896410575152444638988217 33672307931364333479241163)
  ·
    refine ⟨50508461897046500218861745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33672307931364333479241163 50508461897046500218861745)
    ·
      refine ⟨37881346422784875164146309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50508461897046500218861745 37881346422784875164146309)
      ·
        refine ⟨7102752454272164093277433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37881346422784875164146309 7102752454272164093277433)
        ·
          refine ⟨5327064340704123069958075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7102752454272164093277433 5327064340704123069958075)
          ·
            refine ⟨7990596511056184604937113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5327064340704123069958075 7990596511056184604937113)
            ·
              refine ⟨5992947383292138453702835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990596511056184604937113 5992947383292138453702835)
              ·
                refine ⟨8989421074938207680554253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992947383292138453702835 8989421074938207680554253)
                ·
                  refine ⟨3371032903101827880207845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8989421074938207680554253 3371032903101827880207845)
                  ·
                    refine ⟨632068669331592727538971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371032903101827880207845 632068669331592727538971)
                    ·
                      rfl

theorem cell22_1846424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_1846424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846424 prefixEnd_1846424 := by exact prefixLift 1846424
  have htrace : WordTrace (prefixWord ++ tailWord_1846424) baseStart_1846424 baseEnd_1846424 := by
    simpa [prefixWord, tailWord_1846424, baseEnd_1846424] using wordTrace_append hprefix tailTrace_1846424
  have hstable : (prefixWord ++ tailWord_1846424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846424).length < 2 ^ (prefixWord ++ tailWord_1846424).sum := by decide
  have hdescent : baseEnd_1846424 < baseStart_1846424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846501 : List Nat := [1, 3, 1, 4, 4, 1, 8]
def baseStart_1846501 : Nat := 118140960795 + 1846501 * 2 ^ 59
def prefixEnd_1846501 : Nat := 4983230072969 + 3 ^ 40 * 1846501 * 2
def baseEnd_1846501 : Nat := 23410926963155192346805

theorem tailTrace_1846501 : CollatzResearch.WordTrace tailWord_1846501 prefixEnd_1846501 23410926963155192346805 := by
  unfold tailWord_1846501
  simp only [CollatzResearch.WordTrace]
  refine ⟨67347424283449709109035357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44898282855633139406023571 67347424283449709109035357)
  ·
    refine ⟨25255284106293640915888259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67347424283449709109035357 25255284106293640915888259)
    ·
      refine ⟨37882926159440461373832389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25255284106293640915888259 37882926159440461373832389)
      ·
        refine ⟨7103048654895086507593573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37882926159440461373832389 7103048654895086507593573)
        ·
          refine ⟨1331821622792828720173795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7103048654895086507593573 1331821622792828720173795)
          ·
            refine ⟨1997732434189243080260693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331821622792828720173795 1997732434189243080260693)
            ·
              refine ⟨23410926963155192346805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1997732434189243080260693 23410926963155192346805)
              ·
                rfl

theorem cell22_1846501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 8].length) (baseStart_1846501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846501 prefixEnd_1846501 := by exact prefixLift 1846501
  have htrace : WordTrace (prefixWord ++ tailWord_1846501) baseStart_1846501 baseEnd_1846501 := by
    simpa [prefixWord, tailWord_1846501, baseEnd_1846501] using wordTrace_append hprefix tailTrace_1846501
  have hstable : (prefixWord ++ tailWord_1846501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846501).length < 2 ^ (prefixWord ++ tailWord_1846501).sum := by decide
  have hdescent : baseEnd_1846501 < baseStart_1846501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846606 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_1846606 : Nat := 118140960795 + 1846606 * 2 ^ 59
def prefixEnd_1846606 : Nat := 4983230072969 + 3 ^ 40 * 1846606 * 2
def baseEnd_1846606 : Nat := 632130971651004919488413

theorem tailTrace_1846606 : CollatzResearch.WordTrace tailWord_1846606 prefixEnd_1846606 632130971651004919488413 := by
  unfold tailWord_1846606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8418906743508664005200959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44900835965379541361071781 8418906743508664005200959)
  ·
    refine ⟨12628360115262996007801439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8418906743508664005200959 12628360115262996007801439)
    ·
      refine ⟨18942540172894494011702159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12628360115262996007801439 18942540172894494011702159)
      ·
        refine ⟨28413810259341741017553239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18942540172894494011702159 28413810259341741017553239)
        ·
          refine ⟨42620715389012611526329859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28413810259341741017553239 42620715389012611526329859)
          ·
            refine ⟨63931073083518917289494789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42620715389012611526329859 63931073083518917289494789)
            ·
              refine ⟨11987076203159796991780273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63931073083518917289494789 11987076203159796991780273)
              ·
                refine ⟨8990307152369847743835205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11987076203159796991780273 8990307152369847743835205)
                ·
                  refine ⟨1685682591069346451969101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8990307152369847743835205 1685682591069346451969101)
                  ·
                    refine ⟨632130971651004919488413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685682591069346451969101 632130971651004919488413)
                    ·
                      rfl

theorem cell22_1846606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_1846606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846606 prefixEnd_1846606 := by exact prefixLift 1846606
  have htrace : WordTrace (prefixWord ++ tailWord_1846606) baseStart_1846606 baseEnd_1846606 := by
    simpa [prefixWord, tailWord_1846606, baseEnd_1846606] using wordTrace_append hprefix tailTrace_1846606
  have hstable : (prefixWord ++ tailWord_1846606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846606).length < 2 ^ (prefixWord ++ tailWord_1846606).sum := by decide
  have hdescent : baseEnd_1846606 < baseStart_1846606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846614 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1846614 : Nat := 118140960795 + 1846614 * 2 ^ 59
def prefixEnd_1846614 : Nat := 4983230072969 + 3 ^ 40 * 1846614 * 2
def baseEnd_1846614 : Nat := 210711236738165188429463

theorem tailTrace_1846614 : CollatzResearch.WordTrace tailWord_1846614 prefixEnd_1846614 210711236738165188429463 := by
  unfold tailWord_1846614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209471608252520587993681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44901030488026886271932597 4209471608252520587993681)
  ·
    refine ⟨3157103706189390440995261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4209471608252520587993681 3157103706189390440995261)
    ·
      refine ⟨1183913889821021415373223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3157103706189390440995261 1183913889821021415373223)
      ·
        refine ⟨1775870834731532123059835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183913889821021415373223 1775870834731532123059835)
        ·
          refine ⟨2663806252097298184589753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775870834731532123059835 2663806252097298184589753)
          ·
            refine ⟨1997854689072973638442315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2663806252097298184589753 1997854689072973638442315)
            ·
              refine ⟨2996782033609460457663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997854689072973638442315 2996782033609460457663473)
              ·
                refine ⟨2247586525207095343247605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996782033609460457663473 2247586525207095343247605)
                ·
                  refine ⟨210711236738165188429463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2247586525207095343247605 210711236738165188429463)
                  ·
                    rfl

theorem cell22_1846614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1846614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846614 prefixEnd_1846614 := by exact prefixLift 1846614
  have htrace : WordTrace (prefixWord ++ tailWord_1846614) baseStart_1846614 baseEnd_1846614 := by
    simpa [prefixWord, tailWord_1846614, baseEnd_1846614] using wordTrace_append hprefix tailTrace_1846614
  have hstable : (prefixWord ++ tailWord_1846614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846614).length < 2 ^ (prefixWord ++ tailWord_1846614).sum := by decide
  have hdescent : baseEnd_1846614 < baseStart_1846614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846649 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_1846649 : Nat := 118140960795 + 1846649 * 2 ^ 59
def prefixEnd_1846649 : Nat := 4983230072969 + 3 ^ 40 * 1846649 * 2
def baseEnd_1846649 : Nat := 632145691429767140663281

theorem tailTrace_1846649 : CollatzResearch.WordTrace tailWord_1846649 prefixEnd_1846649 632145691429767140663281 := by
  unfold tailWord_1846649
  simp only [CollatzResearch.WordTrace]
  refine ⟨67352822286913530385423001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44901881524609020256948667 67352822286913530385423001)
  ·
    refine ⟨50514616715185147789067251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67352822286913530385423001 50514616715185147789067251)
    ·
      refine ⟨75771925072777721683600877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50514616715185147789067251 75771925072777721683600877)
      ·
        refine ⟨28414471902291645631350329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75771925072777721683600877 28414471902291645631350329)
        ·
          refine ⟨21310853926718734223512747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28414471902291645631350329 21310853926718734223512747)
          ·
            refine ⟨31966280890078101335269121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21310853926718734223512747 31966280890078101335269121)
            ·
              refine ⟨23974710667558576001451841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31966280890078101335269121 23974710667558576001451841)
              ·
                refine ⟨17981033000668932001088881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23974710667558576001451841 17981033000668932001088881)
                ·
                  refine ⟨13485774750501699000816661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17981033000668932001088881 13485774750501699000816661)
                  ·
                    refine ⟨632145691429767140663281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13485774750501699000816661 632145691429767140663281)
                    ·
                      rfl

theorem cell22_1846649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_1846649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846649 prefixEnd_1846649 := by exact prefixLift 1846649
  have htrace : WordTrace (prefixWord ++ tailWord_1846649) baseStart_1846649 baseEnd_1846649 := by
    simpa [prefixWord, tailWord_1846649, baseEnd_1846649] using wordTrace_append hprefix tailTrace_1846649
  have hstable : (prefixWord ++ tailWord_1846649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846649).length < 2 ^ (prefixWord ++ tailWord_1846649).sum := by decide
  have hdescent : baseEnd_1846649 < baseStart_1846649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846651 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 3, 3]
def baseStart_1846651 : Nat := 118140960795 + 1846651 * 2 ^ 59
def prefixEnd_1846651 : Nat := 4983230072969 + 3 ^ 40 * 1846651 * 2
def baseEnd_1846651 : Nat := 632146376070639802113275

theorem tailTrace_1846651 : CollatzResearch.WordTrace tailWord_1846651 prefixEnd_1846651 632146376070639802113275 := by
  unfold tailWord_1846651
  simp only [CollatzResearch.WordTrace]
  refine ⟨67352895232906284726995807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44901930155270856484663871 67352895232906284726995807)
  ·
    refine ⟨101029342849359427090493711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67352895232906284726995807 101029342849359427090493711)
    ·
      refine ⟨151544014274039140635740567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101029342849359427090493711 151544014274039140635740567)
      ·
        refine ⟨227316021411058710953610851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151544014274039140635740567 227316021411058710953610851)
        ·
          refine ⟨340974032116588066430416277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227316021411058710953610851 340974032116588066430416277)
          ·
            refine ⟨15983157755465065613925763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340974032116588066430416277 15983157755465065613925763)
            ·
              refine ⟨23974736633197598420888645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15983157755465065613925763 23974736633197598420888645)
              ·
                refine ⟨4495263118724549703916621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23974736633197598420888645 4495263118724549703916621)
                ·
                  refine ⟨1685723669521706138968733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4495263118724549703916621 1685723669521706138968733)
                  ·
                    refine ⟨632146376070639802113275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685723669521706138968733 632146376070639802113275)
                    ·
                      rfl

theorem cell22_1846651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 3].length) (baseStart_1846651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846651 prefixEnd_1846651 := by exact prefixLift 1846651
  have htrace : WordTrace (prefixWord ++ tailWord_1846651) baseStart_1846651 baseEnd_1846651 := by
    simpa [prefixWord, tailWord_1846651, baseEnd_1846651] using wordTrace_append hprefix tailTrace_1846651
  have hstable : (prefixWord ++ tailWord_1846651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846651).length < 2 ^ (prefixWord ++ tailWord_1846651).sum := by decide
  have hdescent : baseEnd_1846651 < baseStart_1846651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846685 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1846685 : Nat := 118140960795 + 1846685 * 2 ^ 59
def prefixEnd_1846685 : Nat := 4983230072969 + 3 ^ 40 * 1846685 * 2
def baseEnd_1846685 : Nat := 632158014965475046763171

theorem tailTrace_1846685 : CollatzResearch.WordTrace tailWord_1846685 prefixEnd_1846685 632158014965475046763171 := by
  unfold tailWord_1846685
  simp only [CollatzResearch.WordTrace]
  refine ⟨67354135314783108533733509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44902756876522072355822339 67354135314783108533733509)
  ·
    refine ⟨12628900371521832850075033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67354135314783108533733509 12628900371521832850075033)
    ·
      refine ⟨9471675278641374637556275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12628900371521832850075033 9471675278641374637556275)
      ·
        refine ⟨14207512917962061956334413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9471675278641374637556275 14207512917962061956334413)
        ·
          refine ⟨5327817344235773233625405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14207512917962061956334413 5327817344235773233625405)
          ·
            refine ⟨1997931504088414962609527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5327817344235773233625405 1997931504088414962609527)
            ·
              refine ⟨2996897256132622443914291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997931504088414962609527 2996897256132622443914291)
              ·
                refine ⟨4495345884198933665871437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996897256132622443914291 4495345884198933665871437)
                ·
                  refine ⟨1685754706574600124701789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4495345884198933665871437 1685754706574600124701789)
                  ·
                    refine ⟨632158014965475046763171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685754706574600124701789 632158014965475046763171)
                    ·
                      rfl

theorem cell22_1846685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1846685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846685 prefixEnd_1846685 := by exact prefixLift 1846685
  have htrace : WordTrace (prefixWord ++ tailWord_1846685) baseStart_1846685 baseEnd_1846685 := by
    simpa [prefixWord, tailWord_1846685, baseEnd_1846685] using wordTrace_append hprefix tailTrace_1846685
  have hstable : (prefixWord ++ tailWord_1846685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846685).length < 2 ^ (prefixWord ++ tailWord_1846685).sum := by decide
  have hdescent : baseEnd_1846685 < baseStart_1846685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846711 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1846711 : Nat := 118140960795 + 1846711 * 2 ^ 59
def prefixEnd_1846711 : Nat := 4983230072969 + 3 ^ 40 * 1846711 * 2
def baseEnd_1846711 : Nat := 632166915296819645613091

theorem tailTrace_1846711 : CollatzResearch.WordTrace tailWord_1846711 prefixEnd_1846711 632166915296819645613091 := by
  unfold tailWord_1846711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67355083612688914974179987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44903389075125943316119991 67355083612688914974179987)
  ·
    refine ⟨101032625419033372461269981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67355083612688914974179987 101032625419033372461269981)
    ·
      refine ⟨37887234532137514672976243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101032625419033372461269981 37887234532137514672976243)
      ·
        refine ⟨56830851798206272009464365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37887234532137514672976243 56830851798206272009464365)
        ·
          refine ⟨21311569424327352003549137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56830851798206272009464365 21311569424327352003549137)
          ·
            refine ⟨15983677068245514002661853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21311569424327352003549137 15983677068245514002661853)
            ·
              refine ⟨5993878900592067750998195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15983677068245514002661853 5993878900592067750998195)
              ·
                refine ⟨8990818350888101626497293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5993878900592067750998195 8990818350888101626497293)
                ·
                  refine ⟨3371556881583038109936485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8990818350888101626497293 3371556881583038109936485)
                  ·
                    refine ⟨632166915296819645613091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371556881583038109936485 632166915296819645613091)
                    ·
                      rfl

theorem cell22_1846711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1846711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846711 prefixEnd_1846711 := by exact prefixLift 1846711
  have htrace : WordTrace (prefixWord ++ tailWord_1846711) baseStart_1846711 baseEnd_1846711 := by
    simpa [prefixWord, tailWord_1846711, baseEnd_1846711] using wordTrace_append hprefix tailTrace_1846711
  have hstable : (prefixWord ++ tailWord_1846711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846711).length < 2 ^ (prefixWord ++ tailWord_1846711).sum := by decide
  have hdescent : baseEnd_1846711 < baseStart_1846711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846741 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1846741 : Nat := 118140960795 + 1846741 * 2 ^ 59
def prefixEnd_1846741 : Nat := 4983230072969 + 3 ^ 40 * 1846741 * 2
def baseEnd_1846741 : Nat := 632177184909909567362999

theorem tailTrace_1846741 : CollatzResearch.WordTrace tailWord_1846741 prefixEnd_1846741 632177184909909567362999 := by
  unfold tailWord_1846741
  simp only [CollatzResearch.WordTrace]
  refine ⟨67356177802580230097772077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44904118535053486731848051 67356177802580230097772077)
  ·
    refine ⟨25258566675967586286664529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67356177802580230097772077 25258566675967586286664529)
    ·
      refine ⟨18943925006975689714998397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25258566675967586286664529 18943925006975689714998397)
      ·
        refine ⟨7103971877615883643124399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18943925006975689714998397 7103971877615883643124399)
        ·
          refine ⟨10655957816423825464686599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7103971877615883643124399 10655957816423825464686599)
          ·
            refine ⟨15983936724635738197029899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10655957816423825464686599 15983936724635738197029899)
            ·
              refine ⟨23975905086953607295544849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15983936724635738197029899 23975905086953607295544849)
              ·
                refine ⟨17981928815215205471658637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23975905086953607295544849 17981928815215205471658637)
                ·
                  refine ⟨6743223305705702051871989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17981928815215205471658637 6743223305705702051871989)
                  ·
                    refine ⟨632177184909909567362999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6743223305705702051871989 632177184909909567362999)
                    ·
                      rfl

theorem cell22_1846741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1846741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846741 prefixEnd_1846741 := by exact prefixLift 1846741
  have htrace : WordTrace (prefixWord ++ tailWord_1846741) baseStart_1846741 baseEnd_1846741 := by
    simpa [prefixWord, tailWord_1846741, baseEnd_1846741] using wordTrace_append hprefix tailTrace_1846741
  have hstable : (prefixWord ++ tailWord_1846741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846741).length < 2 ^ (prefixWord ++ tailWord_1846741).sum := by decide
  have hdescent : baseEnd_1846741 < baseStart_1846741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846756 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1846756 : Nat := 118140960795 + 1846756 * 2 ^ 59
def prefixEnd_1846756 : Nat := 4983230072969 + 3 ^ 40 * 1846756 * 2
def baseEnd_1846756 : Nat := 632182319716454528237953

theorem tailTrace_1846756 : CollatzResearch.WordTrace tailWord_1846756 prefixEnd_1846756 632182319716454528237953 := by
  unfold tailWord_1846756
  simp only [CollatzResearch.WordTrace]
  refine ⟨33678362448762943829784061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44904483265017258439712081 33678362448762943829784061)
  ·
    refine ⟨12629385918286103936169023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33678362448762943829784061 12629385918286103936169023)
    ·
      refine ⟨18944078877429155904253535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12629385918286103936169023 18944078877429155904253535)
      ·
        refine ⟨28416118316143733856380303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944078877429155904253535 28416118316143733856380303)
        ·
          refine ⟨42624177474215600784570455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416118316143733856380303 42624177474215600784570455)
          ·
            refine ⟨63936266211323401176855683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42624177474215600784570455 63936266211323401176855683)
            ·
              refine ⟨95904399316985101765283525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63936266211323401176855683 95904399316985101765283525)
              ·
                refine ⟨17982074871934706580990661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95904399316985101765283525 17982074871934706580990661)
                ·
                  refine ⟨3371639038487757483935749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17982074871934706580990661 3371639038487757483935749)
                  ·
                    refine ⟨632182319716454528237953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371639038487757483935749 632182319716454528237953)
                    ·
                      rfl

theorem cell22_1846756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1846756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846756 prefixEnd_1846756 := by exact prefixLift 1846756
  have htrace : WordTrace (prefixWord ++ tailWord_1846756) baseStart_1846756 baseEnd_1846756 := by
    simpa [prefixWord, tailWord_1846756, baseEnd_1846756] using wordTrace_append hprefix tailTrace_1846756
  have hstable : (prefixWord ++ tailWord_1846756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846756).length < 2 ^ (prefixWord ++ tailWord_1846756).sum := by decide
  have hdescent : baseEnd_1846756 < baseStart_1846756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846788 : List Nat := [2, 3, 2, 3, 2, 1, 9]
def baseStart_1846788 : Nat := 118140960795 + 1846788 * 2 ^ 59
def prefixEnd_1846788 : Nat := 4983230072969 + 3 ^ 40 * 1846788 * 2
def baseEnd_1846788 : Nat := 23414565702608041164365

theorem tailTrace_1846788 : CollatzResearch.WordTrace tailWord_1846788 prefixEnd_1846788 23414565702608041164365 := by
  unfold tailWord_1846788
  simp only [CollatzResearch.WordTrace]
  refine ⟨33678946016704978562366509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44905261355606638083155345 33678946016704978562366509)
  ·
    refine ⟨12629604756264366960887441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33678946016704978562366509 12629604756264366960887441)
    ·
      refine ⟨9472203567198275220665581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12629604756264366960887441 9472203567198275220665581)
      ·
        refine ⟨3552076337699353207749593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9472203567198275220665581 3552076337699353207749593)
        ·
          refine ⟨2664057253274514905812195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552076337699353207749593 2664057253274514905812195)
          ·
            refine ⟨3996085879911772358718293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664057253274514905812195 3996085879911772358718293)
            ·
              refine ⟨23414565702608041164365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3996085879911772358718293 23414565702608041164365)
              ·
                rfl

theorem cell22_1846788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 9].length) (baseStart_1846788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846788 prefixEnd_1846788 := by exact prefixLift 1846788
  have htrace : WordTrace (prefixWord ++ tailWord_1846788) baseStart_1846788 baseEnd_1846788 := by
    simpa [prefixWord, tailWord_1846788, baseEnd_1846788] using wordTrace_append hprefix tailTrace_1846788
  have hstable : (prefixWord ++ tailWord_1846788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846788).length < 2 ^ (prefixWord ++ tailWord_1846788).sum := by decide
  have hdescent : baseEnd_1846788 < baseStart_1846788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846803 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 3, 3]
def baseStart_1846803 : Nat := 118140960795 + 1846803 * 2 ^ 59
def prefixEnd_1846803 : Nat := 4983230072969 + 3 ^ 40 * 1846803 * 2
def baseEnd_1846803 : Nat := 632198408776962072312809

theorem tailTrace_1846803 : CollatzResearch.WordTrace tailWord_1846803 prefixEnd_1846803 632198408776962072312809 := by
  unfold tailWord_1846803
  simp only [CollatzResearch.WordTrace]
  refine ⟨67358439128355614686529063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44905626085570409791019375 67358439128355614686529063)
  ·
    refine ⟨101037658692533422029793595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67358439128355614686529063 101037658692533422029793595)
    ·
      refine ⟨151556488038800133044690393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101037658692533422029793595 151556488038800133044690393)
      ·
        refine ⟨113667366029100099783517795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151556488038800133044690393 113667366029100099783517795)
        ·
          refine ⟨170501049043650149675276693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113667366029100099783517795 170501049043650149675276693)
          ·
            refine ⟨7992236673921100766028595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170501049043650149675276693 7992236673921100766028595)
            ·
              refine ⟨11988355010881651149042893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992236673921100766028595 11988355010881651149042893)
              ·
                refine ⟨4495633129080619180891085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11988355010881651149042893 4495633129080619180891085)
                ·
                  refine ⟨1685862423405232192834157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4495633129080619180891085 1685862423405232192834157)
                  ·
                    refine ⟨632198408776962072312809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685862423405232192834157 632198408776962072312809)
                    ·
                      rfl

theorem cell22_1846803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 3].length) (baseStart_1846803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846803 prefixEnd_1846803 := by exact prefixLift 1846803
  have htrace : WordTrace (prefixWord ++ tailWord_1846803) baseStart_1846803 baseEnd_1846803 := by
    simpa [prefixWord, tailWord_1846803, baseEnd_1846803] using wordTrace_append hprefix tailTrace_1846803
  have hstable : (prefixWord ++ tailWord_1846803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846803).length < 2 ^ (prefixWord ++ tailWord_1846803).sum := by decide
  have hdescent : baseEnd_1846803 < baseStart_1846803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846837 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1846837 : Nat := 118140960795 + 1846837 * 2 ^ 59
def prefixEnd_1846837 : Nat := 4983230072969 + 3 ^ 40 * 1846837 * 2
def baseEnd_1846837 : Nat := 632210047671797316962705

theorem tailTrace_1846837 : CollatzResearch.WordTrace tailWord_1846837 prefixEnd_1846837 632210047671797316962705 := by
  unfold tailWord_1846837
  simp only [CollatzResearch.WordTrace]
  refine ⟨67359679210232438493266765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44906452806821625662177843 67359679210232438493266765)
  ·
    refine ⟨25259879703837164434975037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67359679210232438493266765 25259879703837164434975037)
    ·
      refine ⟨9472454888938936663115639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25259879703837164434975037 9472454888938936663115639)
      ·
        refine ⟨14208682333408404994673459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9472454888938936663115639 14208682333408404994673459)
        ·
          refine ⟨21313023500112607492010189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14208682333408404994673459 21313023500112607492010189)
          ·
            refine ⟨7992383812542227809503821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21313023500112607492010189 7992383812542227809503821)
            ·
              refine ⟨2997143929703335428563933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7992383812542227809503821 2997143929703335428563933)
              ·
                refine ⟨1123928973638750785711475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2997143929703335428563933 1123928973638750785711475)
                ·
                  refine ⟨1685893460458126178567213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123928973638750785711475 1685893460458126178567213)
                  ·
                    refine ⟨632210047671797316962705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1685893460458126178567213 632210047671797316962705)
                    ·
                      rfl

theorem cell22_1846837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1846837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846837 prefixEnd_1846837 := by exact prefixLift 1846837
  have htrace : WordTrace (prefixWord ++ tailWord_1846837) baseStart_1846837 baseEnd_1846837 := by
    simpa [prefixWord, tailWord_1846837, baseEnd_1846837] using wordTrace_append hprefix tailTrace_1846837
  have hstable : (prefixWord ++ tailWord_1846837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846837).length < 2 ^ (prefixWord ++ tailWord_1846837).sum := by decide
  have hdescent : baseEnd_1846837 < baseStart_1846837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846891 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_1846891 : Nat := 118140960795 + 1846891 * 2 ^ 59
def prefixEnd_1846891 : Nat := 4983230072969 + 3 ^ 40 * 1846891 * 2
def baseEnd_1846891 : Nat := 632228532975359176112539

theorem tailTrace_1846891 : CollatzResearch.WordTrace tailWord_1846891 prefixEnd_1846891 632228532975359176112539 := by
  unfold tailWord_1846891
  simp only [CollatzResearch.WordTrace]
  refine ⟨67361648752036805715732527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44907765834691203810488351 67361648752036805715732527)
  ·
    refine ⟨101042473128055208573598791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67361648752036805715732527 101042473128055208573598791)
    ·
      refine ⟨151563709692082812860398187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101042473128055208573598791 151563709692082812860398187)
      ·
        refine ⟨227345564538124219290597281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151563709692082812860398187 227345564538124219290597281)
        ·
          refine ⟨170509173403593164467947961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227345564538124219290597281 170509173403593164467947961)
          ·
            refine ⟨127881880052694873350960971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170509173403593164467947961 127881880052694873350960971)
            ·
              refine ⟨191822820079042310026441457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127881880052694873350960971 191822820079042310026441457)
              ·
                refine ⟨143867115059281732519831093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191822820079042310026441457 143867115059281732519831093)
                ·
                  refine ⟨13487542036807662423734165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143867115059281732519831093 13487542036807662423734165)
                  ·
                    refine ⟨632228532975359176112539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13487542036807662423734165 632228532975359176112539)
                    ·
                      rfl

theorem cell22_1846891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_1846891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846891 prefixEnd_1846891 := by exact prefixLift 1846891
  have htrace : WordTrace (prefixWord ++ tailWord_1846891) baseStart_1846891 baseEnd_1846891 := by
    simpa [prefixWord, tailWord_1846891, baseEnd_1846891] using wordTrace_append hprefix tailTrace_1846891
  have hstable : (prefixWord ++ tailWord_1846891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846891).length < 2 ^ (prefixWord ++ tailWord_1846891).sum := by decide
  have hdescent : baseEnd_1846891 < baseStart_1846891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846942 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1846942 : Nat := 118140960795 + 1846942 * 2 ^ 59
def prefixEnd_1846942 : Nat := 4983230072969 + 3 ^ 40 * 1846942 * 2
def baseEnd_1846942 : Nat := 632245991317612043087383

theorem tailTrace_1846942 : CollatzResearch.WordTrace tailWord_1846942 prefixEnd_1846942 632245991317612043087383 := by
  unfold tailWord_1846942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420438609356505178229885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44909005916568027617226053 8420438609356505178229885)
  ·
    refine ⟨3157664478508689441836207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8420438609356505178229885 3157664478508689441836207)
    ·
      refine ⟨4736496717763034162754311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157664478508689441836207 4736496717763034162754311)
      ·
        refine ⟨7104745076644551244131467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736496717763034162754311 7104745076644551244131467)
        ·
          refine ⟨10657117614966826866197201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104745076644551244131467 10657117614966826866197201)
          ·
            refine ⟨7992838211225120149647901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10657117614966826866197201 7992838211225120149647901)
            ·
              refine ⟨2997314329209420056117963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7992838211225120149647901 2997314329209420056117963)
              ·
                refine ⟨4495971493814130084176945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997314329209420056117963 4495971493814130084176945)
                ·
                  refine ⟨3371978620360597563132709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4495971493814130084176945 3371978620360597563132709)
                  ·
                    refine ⟨632245991317612043087383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371978620360597563132709 632245991317612043087383)
                    ·
                      rfl

theorem cell22_1846942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1846942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846942 prefixEnd_1846942 := by exact prefixLift 1846942
  have htrace : WordTrace (prefixWord ++ tailWord_1846942) baseStart_1846942 baseEnd_1846942 := by
    simpa [prefixWord, tailWord_1846942, baseEnd_1846942] using wordTrace_append hprefix tailTrace_1846942
  have hstable : (prefixWord ++ tailWord_1846942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846942).length < 2 ^ (prefixWord ++ tailWord_1846942).sum := by decide
  have hdescent : baseEnd_1846942 < baseStart_1846942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846972 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_1846972 : Nat := 118140960795 + 1846972 * 2 ^ 59
def prefixEnd_1846972 : Nat := 4983230072969 + 3 ^ 40 * 1846972 * 2
def baseEnd_1846972 : Nat := 632256260930701964837291

theorem tailTrace_1846972 : CollatzResearch.WordTrace tailWord_1846972 prefixEnd_1846972 632256260930701964837291 := by
  unfold tailWord_1846972
  simp only [CollatzResearch.WordTrace]
  refine ⟨33682301532371678274715585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44909735376495571032954113 33682301532371678274715585)
  ·
    refine ⟨25261726149278758706036689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33682301532371678274715585 25261726149278758706036689)
    ·
      refine ⟨18946294611959069029527517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25261726149278758706036689 18946294611959069029527517)
      ·
        refine ⟨7104860479484650886072819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18946294611959069029527517 7104860479484650886072819)
        ·
          refine ⟨10657290719226976329109229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104860479484650886072819 10657290719226976329109229)
          ·
            refine ⟨3996484019710116123415961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10657290719226976329109229 3996484019710116123415961)
            ·
              refine ⟨2997363014782587092561971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996484019710116123415961 2997363014782587092561971)
              ·
                refine ⟨4496044522173880638842957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997363014782587092561971 4496044522173880638842957)
                ·
                  refine ⟨1686016695815205239566109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4496044522173880638842957 1686016695815205239566109)
                  ·
                    refine ⟨632256260930701964837291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686016695815205239566109 632256260930701964837291)
                    ·
                      rfl

theorem cell22_1846972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_1846972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846972 prefixEnd_1846972 := by exact prefixLift 1846972
  have htrace : WordTrace (prefixWord ++ tailWord_1846972) baseStart_1846972 baseEnd_1846972 := by
    simpa [prefixWord, tailWord_1846972, baseEnd_1846972] using wordTrace_append hprefix tailTrace_1846972
  have hstable : (prefixWord ++ tailWord_1846972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846972).length < 2 ^ (prefixWord ++ tailWord_1846972).sum := by decide
  have hdescent : baseEnd_1846972 < baseStart_1846972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846978 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1846978 : Nat := 118140960795 + 1846978 * 2 ^ 59
def prefixEnd_1846978 : Nat := 4983230072969 + 3 ^ 40 * 1846978 * 2
def baseEnd_1846978 : Nat := 632258314853319949187273

theorem tailTrace_1846978 : CollatzResearch.WordTrace tailWord_1846978 prefixEnd_1846978 632258314853319949187273 := by
  unfold tailWord_1846978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841205475680404893537397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44909881268481079716099725 16841205475680404893537397)
  ·
    refine ⟨1578863013345037958769131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16841205475680404893537397 1578863013345037958769131)
    ·
      refine ⟨2368294520017556938153697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578863013345037958769131 2368294520017556938153697)
      ·
        refine ⟨1776220890013167703615273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368294520017556938153697 1776220890013167703615273)
        ·
          refine ⟨1332165667509875777711455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1776220890013167703615273 1332165667509875777711455)
          ·
            refine ⟨1998248501264813666567183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332165667509875777711455 1998248501264813666567183)
            ·
              refine ⟨2997372751897220499850775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998248501264813666567183 2997372751897220499850775)
              ·
                refine ⟨4496059127845830749776163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997372751897220499850775 4496059127845830749776163)
                ·
                  refine ⟨6744088691768746124664245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496059127845830749776163 6744088691768746124664245)
                  ·
                    refine ⟨632258314853319949187273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6744088691768746124664245 632258314853319949187273)
                    ·
                      rfl

theorem cell22_1846978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1846978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846978 prefixEnd_1846978 := by exact prefixLift 1846978
  have htrace : WordTrace (prefixWord ++ tailWord_1846978) baseStart_1846978 baseEnd_1846978 := by
    simpa [prefixWord, tailWord_1846978, baseEnd_1846978] using wordTrace_append hprefix tailTrace_1846978
  have hstable : (prefixWord ++ tailWord_1846978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846978).length < 2 ^ (prefixWord ++ tailWord_1846978).sum := by decide
  have hdescent : baseEnd_1846978 < baseStart_1846978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846983 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1846983 : Nat := 118140960795 + 1846983 * 2 ^ 59
def prefixEnd_1846983 : Nat := 4983230072969 + 3 ^ 40 * 1846983 * 2
def baseEnd_1846983 : Nat := 632260026455501602812257

theorem tailTrace_1846983 : CollatzResearch.WordTrace tailWord_1846983 prefixEnd_1846983 632260026455501602812257 := by
  unfold tailWord_1846983
  simp only [CollatzResearch.WordTrace]
  refine ⟨67365004267703505428081603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44910002845135670285387735 67365004267703505428081603)
  ·
    refine ⟨101047506401555258142122405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67365004267703505428081603 101047506401555258142122405)
    ·
      refine ⟨18946407450291610901647951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101047506401555258142122405 18946407450291610901647951)
      ·
        refine ⟨28419611175437416352471927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18946407450291610901647951 28419611175437416352471927)
        ·
          refine ⟨42629416763156124528707891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28419611175437416352471927 42629416763156124528707891)
          ·
            refine ⟨63944125144734186793061837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42629416763156124528707891 63944125144734186793061837)
            ·
              refine ⟨23979046929275320047398189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63944125144734186793061837 23979046929275320047398189)
              ·
                refine ⟨8992142598478245017774321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23979046929275320047398189 8992142598478245017774321)
                ·
                  refine ⟨6744106948858683763330741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8992142598478245017774321 6744106948858683763330741)
                  ·
                    refine ⟨632260026455501602812257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6744106948858683763330741 632260026455501602812257)
                    ·
                      rfl

theorem cell22_1846983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1846983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846983 prefixEnd_1846983 := by exact prefixLift 1846983
  have htrace : WordTrace (prefixWord ++ tailWord_1846983) baseStart_1846983 baseEnd_1846983 := by
    simpa [prefixWord, tailWord_1846983, baseEnd_1846983] using wordTrace_append hprefix tailTrace_1846983
  have hstable : (prefixWord ++ tailWord_1846983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846983).length < 2 ^ (prefixWord ++ tailWord_1846983).sum := by decide
  have hdescent : baseEnd_1846983 < baseStart_1846983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846989 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1846989 : Nat := 118140960795 + 1846989 * 2 ^ 59
def prefixEnd_1846989 : Nat := 4983230072969 + 3 ^ 40 * 1846989 * 2
def baseEnd_1846989 : Nat := 632262080378119587162239

theorem tailTrace_1846989 : CollatzResearch.WordTrace tailWord_1846989 prefixEnd_1846989 632262080378119587162239 := by
  unfold tailWord_1846989
  simp only [CollatzResearch.WordTrace]
  refine ⟨67365223105681768452800021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44910148737121178968533347 67365223105681768452800021)
  ·
    refine ⟨3157744833078832896225001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67365223105681768452800021 3157744833078832896225001)
    ·
      refine ⟨2368308624809124672168751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157744833078832896225001 2368308624809124672168751)
      ·
        refine ⟨3552462937213687008253127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368308624809124672168751 3552462937213687008253127)
        ·
          refine ⟨5328694405820530512379691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552462937213687008253127 5328694405820530512379691)
          ·
            refine ⟨7993041608730795768569537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328694405820530512379691 7993041608730795768569537)
            ·
              refine ⟨5994781206548096826427153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7993041608730795768569537 5994781206548096826427153)
              ·
                refine ⟨4496085904911072619820365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994781206548096826427153 4496085904911072619820365)
                ·
                  refine ⟨1686032214341652232432637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4496085904911072619820365 1686032214341652232432637)
                  ·
                    refine ⟨632262080378119587162239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686032214341652232432637 632262080378119587162239)
                    ·
                      rfl

theorem cell22_1846989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1846989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1846989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1846989 prefixEnd_1846989 := by exact prefixLift 1846989
  have htrace : WordTrace (prefixWord ++ tailWord_1846989) baseStart_1846989 baseEnd_1846989 := by
    simpa [prefixWord, tailWord_1846989, baseEnd_1846989] using wordTrace_append hprefix tailTrace_1846989
  have hstable : (prefixWord ++ tailWord_1846989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846989).length < 2 ^ (prefixWord ++ tailWord_1846989).sum := by decide
  have hdescent : baseEnd_1846989 < baseStart_1846989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847043 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_1847043 : Nat := 118140960795 + 1847043 * 2 ^ 59
def prefixEnd_1847043 : Nat := 4983230072969 + 3 ^ 40 * 1847043 * 2
def baseEnd_1847043 : Nat := 632280565681681446312073

theorem tailTrace_1847043 : CollatzResearch.WordTrace tailWord_1847043 prefixEnd_1847043 632280565681681446312073 := by
  unfold tailWord_1847043
  simp only [CollatzResearch.WordTrace]
  refine ⟨67367192647486135675265783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44911461764990757116843855 67367192647486135675265783)
  ·
    refine ⟨101050788971229203512898675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67367192647486135675265783 101050788971229203512898675)
    ·
      refine ⟨151576183456843805269348013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101050788971229203512898675 151576183456843805269348013)
      ·
        refine ⟨56841068796316426976005505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151576183456843805269348013 56841068796316426976005505)
        ·
          refine ⟨42630801597237320232004129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56841068796316426976005505 42630801597237320232004129)
          ·
            refine ⟨31973101197927990174003097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42630801597237320232004129 31973101197927990174003097)
            ·
              refine ⟨23979825898445992630502323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31973101197927990174003097 23979825898445992630502323)
              ·
                refine ⟨35969738847668988945753485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23979825898445992630502323 35969738847668988945753485)
                ·
                  refine ⟨13488652067875870854657557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35969738847668988945753485 13488652067875870854657557)
                  ·
                    refine ⟨632280565681681446312073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13488652067875870854657557 632280565681681446312073)
                    ·
                      rfl

theorem cell22_1847043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_1847043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847043 prefixEnd_1847043 := by exact prefixLift 1847043
  have htrace : WordTrace (prefixWord ++ tailWord_1847043) baseStart_1847043 baseEnd_1847043 := by
    simpa [prefixWord, tailWord_1847043, baseEnd_1847043] using wordTrace_append hprefix tailTrace_1847043
  have hstable : (prefixWord ++ tailWord_1847043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847043).length < 2 ^ (prefixWord ++ tailWord_1847043).sum := by decide
  have hdescent : baseEnd_1847043 < baseStart_1847043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847092 : List Nat := [2, 5, 1, 1, 2, 1, 3, 7]
def baseStart_1847092 : Nat := 118140960795 + 1847092 * 2 ^ 59
def prefixEnd_1847092 : Nat := 4983230072969 + 3 ^ 40 * 1847092 * 2
def baseEnd_1847092 : Nat := 70255259931451294648547

theorem tailTrace_1847092 : CollatzResearch.WordTrace tailWord_1847092 prefixEnd_1847092 70255259931451294648547 := by
  unfold tailWord_1847092
  simp only [CollatzResearch.WordTrace]
  refine ⟨33684489912154308521899765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44912653216205744695866353 33684489912154308521899765)
  ·
    refine ⟨3157920929264466423928103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33684489912154308521899765 3157920929264466423928103)
    ·
      refine ⟨4736881393896699635892155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157920929264466423928103 4736881393896699635892155)
      ·
        refine ⟨7105322090845049453838233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736881393896699635892155 7105322090845049453838233)
        ·
          refine ⟨5328991568133787090378675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7105322090845049453838233 5328991568133787090378675)
          ·
            refine ⟨7993487352200680635568013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328991568133787090378675 7993487352200680635568013)
            ·
              refine ⟨2997557757075255238338005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7993487352200680635568013 2997557757075255238338005)
              ·
                refine ⟨70255259931451294648547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2997557757075255238338005 70255259931451294648547)
                ·
                  rfl

theorem cell22_1847092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_1847092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847092 prefixEnd_1847092 := by exact prefixLift 1847092
  have htrace : WordTrace (prefixWord ++ tailWord_1847092) baseStart_1847092 baseEnd_1847092 := by
    simpa [prefixWord, tailWord_1847092, baseEnd_1847092] using wordTrace_append hprefix tailTrace_1847092
  have hstable : (prefixWord ++ tailWord_1847092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847092).length < 2 ^ (prefixWord ++ tailWord_1847092).sum := by decide
  have hdescent : baseEnd_1847092 < baseStart_1847092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847107 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 3, 3]
def baseStart_1847107 : Nat := 118140960795 + 1847107 * 2 ^ 59
def prefixEnd_1847107 : Nat := 4983230072969 + 3 ^ 40 * 1847107 * 2
def baseEnd_1847107 : Nat := 632302474189606612711877

theorem tailTrace_1847107 : CollatzResearch.WordTrace tailWord_1847107 prefixEnd_1847107 632302474189606612711877 := by
  unfold tailWord_1847107
  simp only [CollatzResearch.WordTrace]
  refine ⟨67369526919254274605595575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44913017946169516403730383 67369526919254274605595575)
  ·
    refine ⟨101054290378881411908393363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67369526919254274605595575 101054290378881411908393363)
    ·
      refine ⟨151581435568322117862590045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101054290378881411908393363 151581435568322117862590045)
      ·
        refine ⟨56843038338120794198471267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151581435568322117862590045 56843038338120794198471267)
        ·
          refine ⟨85264557507181191297706901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56843038338120794198471267 85264557507181191297706901)
          ·
            refine ⟨3996776133149118342080011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85264557507181191297706901 3996776133149118342080011)
            ·
              refine ⟨5995164199723677513120017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996776133149118342080011 5995164199723677513120017)
              ·
                refine ⟨4496373149792758134840013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5995164199723677513120017 4496373149792758134840013)
                ·
                  refine ⟨1686139931172284300565005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4496373149792758134840013 1686139931172284300565005)
                  ·
                    refine ⟨632302474189606612711877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686139931172284300565005 632302474189606612711877)
                    ·
                      rfl

theorem cell22_1847107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 3].length) (baseStart_1847107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847107 prefixEnd_1847107 := by exact prefixLift 1847107
  have htrace : WordTrace (prefixWord ++ tailWord_1847107) baseStart_1847107 baseEnd_1847107 := by
    simpa [prefixWord, tailWord_1847107, baseEnd_1847107] using wordTrace_append hprefix tailTrace_1847107
  have hstable : (prefixWord ++ tailWord_1847107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847107).length < 2 ^ (prefixWord ++ tailWord_1847107).sum := by decide
  have hdescent : baseEnd_1847107 < baseStart_1847107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847135 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_1847135 : Nat := 118140960795 + 1847135 * 2 ^ 59
def prefixEnd_1847135 : Nat := 4983230072969 + 3 ^ 40 * 1847135 * 2
def baseEnd_1847135 : Nat := 632312059161823873011791

theorem tailTrace_1847135 : CollatzResearch.WordTrace tailWord_1847135 prefixEnd_1847135 632312059161823873011791 := by
  unfold tailWord_1847135
  simp only [CollatzResearch.WordTrace]
  refine ⟨67370548163152835387614859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44913698775435223591743239 67370548163152835387614859)
  ·
    refine ⟨101055822244729253081422289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67370548163152835387614859 101055822244729253081422289)
    ·
      refine ⟨75791866683546939811066717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101055822244729253081422289 75791866683546939811066717)
      ·
        refine ⟨28421950006330102429150019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75791866683546939811066717 28421950006330102429150019)
        ·
          refine ⟨42632925009495153643725029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28421950006330102429150019 42632925009495153643725029)
          ·
            refine ⟨7993673439280341308198443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42632925009495153643725029 7993673439280341308198443)
            ·
              refine ⟨11990510158920511962297665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993673439280341308198443 11990510158920511962297665)
              ·
                refine ⟨8992882619190383971723249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11990510158920511962297665 8992882619190383971723249)
                ·
                  refine ⟨6744661964392787978792437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8992882619190383971723249 6744661964392787978792437)
                  ·
                    refine ⟨632312059161823873011791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6744661964392787978792437 632312059161823873011791)
                    ·
                      rfl

theorem cell22_1847135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_1847135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847135 prefixEnd_1847135 := by exact prefixLift 1847135
  have htrace : WordTrace (prefixWord ++ tailWord_1847135) baseStart_1847135 baseEnd_1847135 := by
    simpa [prefixWord, tailWord_1847135, baseEnd_1847135] using wordTrace_append hprefix tailTrace_1847135
  have hstable : (prefixWord ++ tailWord_1847135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847135).length < 2 ^ (prefixWord ++ tailWord_1847135).sum := by decide
  have hdescent : baseEnd_1847135 < baseStart_1847135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847180 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_1847180 : Nat := 118140960795 + 1847180 * 2 ^ 59
def prefixEnd_1847180 : Nat := 4983230072969 + 3 ^ 40 * 1847180 * 2
def baseEnd_1847180 : Nat := 632327463581458755636653

theorem tailTrace_1847180 : CollatzResearch.WordTrace tailWord_1847180 prefixEnd_1847180 632327463581458755636653 := by
  unfold tailWord_1847180
  simp only [CollatzResearch.WordTrace]
  refine ⟨33686094723994904036501497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44914792965326538715335329 33686094723994904036501497)
  ·
    refine ⟨25264571042996178027376123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33686094723994904036501497 25264571042996178027376123)
    ·
      refine ⟨37896856564494267041064185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25264571042996178027376123 37896856564494267041064185)
      ·
        refine ⟨28422642423370700280798139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37896856564494267041064185 28422642423370700280798139)
        ·
          refine ⟨42633963635056050421197209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28422642423370700280798139 42633963635056050421197209)
          ·
            refine ⟨31975472726292037815897907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42633963635056050421197209 31975472726292037815897907)
            ·
              refine ⟨47963209089438056723846861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31975472726292037815897907 47963209089438056723846861)
              ·
                refine ⟨17986203408539271271442573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47963209089438056723846861 17986203408539271271442573)
                ·
                  refine ⟨6744826278202226726790965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17986203408539271271442573 6744826278202226726790965)
                  ·
                    refine ⟨632327463581458755636653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6744826278202226726790965 632327463581458755636653)
                    ·
                      rfl

theorem cell22_1847180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_1847180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847180 prefixEnd_1847180 := by exact prefixLift 1847180
  have htrace : WordTrace (prefixWord ++ tailWord_1847180) baseStart_1847180 baseEnd_1847180 := by
    simpa [prefixWord, tailWord_1847180, baseEnd_1847180] using wordTrace_append hprefix tailTrace_1847180
  have hstable : (prefixWord ++ tailWord_1847180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847180).length < 2 ^ (prefixWord ++ tailWord_1847180).sum := by decide
  have hdescent : baseEnd_1847180 < baseStart_1847180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847199 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 6]
def baseStart_1847199 : Nat := 118140960795 + 1847199 * 2 ^ 59
def prefixEnd_1847199 : Nat := 4983230072969 + 3 ^ 40 * 1847199 * 2
def baseEnd_1847199 : Nat := 210777989223249679803865

theorem tailTrace_1847199 : CollatzResearch.WordTrace tailWord_1847199 prefixEnd_1847199 210777989223249679803865 := by
  unfold tailWord_1847199
  simp only [CollatzResearch.WordTrace]
  refine ⟨67372882434920974317944651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44915254956613982878629767 67372882434920974317944651)
  ·
    refine ⟨101059323652381461476916977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67372882434920974317944651 101059323652381461476916977)
    ·
      refine ⟨75794492739286096107687733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101059323652381461476916977 75794492739286096107687733)
      ·
        refine ⟨7105733694308071510095725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75794492739286096107687733 7105733694308071510095725)
        ·
          refine ⟨2664650135365526816285897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7105733694308071510095725 2664650135365526816285897)
          ·
            refine ⟨1998487601524145112214423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664650135365526816285897 1998487601524145112214423)
            ·
              refine ⟨2997731402286217668321635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998487601524145112214423 2997731402286217668321635)
              ·
                refine ⟨4496597103429326502482453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997731402286217668321635 4496597103429326502482453)
                ·
                  refine ⟨210777989223249679803865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4496597103429326502482453 210777989223249679803865)
                  ·
                    rfl

theorem cell22_1847199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 6].length) (baseStart_1847199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847199 prefixEnd_1847199 := by exact prefixLift 1847199
  have htrace : WordTrace (prefixWord ++ tailWord_1847199) baseStart_1847199 baseEnd_1847199 := by
    simpa [prefixWord, tailWord_1847199, baseEnd_1847199] using wordTrace_append hprefix tailTrace_1847199
  have hstable : (prefixWord ++ tailWord_1847199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847199).length < 2 ^ (prefixWord ++ tailWord_1847199).sum := by decide
  have hdescent : baseEnd_1847199 < baseStart_1847199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847229 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1847229 : Nat := 118140960795 + 1847229 * 2 ^ 59
def prefixEnd_1847229 : Nat := 4983230072969 + 3 ^ 40 * 1847229 * 2
def baseEnd_1847229 : Nat := 632344237282838961161503

theorem tailTrace_1847229 : CollatzResearch.WordTrace tailWord_1847229 prefixEnd_1847229 632344237282838961161503 := by
  unfold tailWord_1847229
  simp only [CollatzResearch.WordTrace]
  refine ⟨67373976624812289441536741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44915984416541526294357827 67373976624812289441536741)
  ·
    refine ⟨12632620617152304270288139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67373976624812289441536741 12632620617152304270288139)
    ·
      refine ⟨18948930925728456405432209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632620617152304270288139 18948930925728456405432209)
      ·
        refine ⟨14211698194296342304074157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18948930925728456405432209 14211698194296342304074157)
        ·
          refine ⟨5329386822861128364027809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14211698194296342304074157 5329386822861128364027809)
          ·
            refine ⟨3997040117145846273020857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5329386822861128364027809 3997040117145846273020857)
            ·
              refine ⟨2997780087859384704765643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3997040117145846273020857 2997780087859384704765643)
              ·
                refine ⟨4496670131789077057148465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997780087859384704765643 4496670131789077057148465)
                ·
                  refine ⟨3372502598841807792861349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4496670131789077057148465 3372502598841807792861349)
                  ·
                    refine ⟨632344237282838961161503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3372502598841807792861349 632344237282838961161503)
                    ·
                      rfl

theorem cell22_1847229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1847229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847229 prefixEnd_1847229 := by exact prefixLift 1847229
  have htrace : WordTrace (prefixWord ++ tailWord_1847229) baseStart_1847229 baseEnd_1847229 := by
    simpa [prefixWord, tailWord_1847229, baseEnd_1847229] using wordTrace_append hprefix tailTrace_1847229
  have hstable : (prefixWord ++ tailWord_1847229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847229).length < 2 ^ (prefixWord ++ tailWord_1847229).sum := by decide
  have hdescent : baseEnd_1847229 < baseStart_1847229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847250 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_1847250 : Nat := 118140960795 + 1847250 * 2 ^ 59
def prefixEnd_1847250 : Nat := 4983230072969 + 3 ^ 40 * 1847250 * 2
def baseEnd_1847250 : Nat := 210783808670667302128813

theorem tailTrace_1847250 : CollatzResearch.WordTrace tailWord_1847250 prefixEnd_1847250 210783808670667302128813 := by
  unfold tailWord_1847250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843685639434052507012801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44916495038490806685367469 16843685639434052507012801)
  ·
    refine ⟨12632764229575539380259601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16843685639434052507012801 12632764229575539380259601)
    ·
      refine ⟨9474573172181654535194701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12632764229575539380259601 9474573172181654535194701)
      ·
        refine ⟨3552964939568120450698013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9474573172181654535194701 3552964939568120450698013)
        ·
          refine ⟨1332361852338045169011755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3552964939568120450698013 1332361852338045169011755)
          ·
            refine ⟨1998542778507067753517633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332361852338045169011755 1998542778507067753517633)
            ·
              refine ⟨1498907083880300815138225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1998542778507067753517633 1498907083880300815138225)
              ·
                refine ⟨1124180312910225611353669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498907083880300815138225 1124180312910225611353669)
                ·
                  refine ⟨210783808670667302128813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1124180312910225611353669 210783808670667302128813)
                  ·
                    rfl

theorem cell22_1847250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_1847250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847250 prefixEnd_1847250 := by exact prefixLift 1847250
  have htrace : WordTrace (prefixWord ++ tailWord_1847250) baseStart_1847250 baseEnd_1847250 := by
    simpa [prefixWord, tailWord_1847250, baseEnd_1847250] using wordTrace_append hprefix tailTrace_1847250
  have hstable : (prefixWord ++ tailWord_1847250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847250).length < 2 ^ (prefixWord ++ tailWord_1847250).sum := by decide
  have hdescent : baseEnd_1847250 < baseStart_1847250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847261 : List Nat := [1, 4, 3, 1, 4, 1, 1, 7]
def baseStart_1847261 : Nat := 118140960795 + 1847261 * 2 ^ 59
def prefixEnd_1847261 : Nat := 4983230072969 + 3 ^ 40 * 1847261 * 2
def baseEnd_1847261 : Nat := 70261687948533504929045

theorem tailTrace_1847261 : CollatzResearch.WordTrace tailWord_1847261 prefixEnd_1847261 70261687948533504929045 := by
  unfold tailWord_1847261
  simp only [CollatzResearch.WordTrace]
  refine ⟨67375143760696358906701637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44916762507130905937801091 67375143760696358906701637)
  ·
    refine ⟨12632839455130567295006557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67375143760696358906701637 12632839455130567295006557)
    ·
      refine ⟨4737314795673962735627459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12632839455130567295006557 4737314795673962735627459)
      ·
        refine ⟨7105972193510944103441189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737314795673962735627459 7105972193510944103441189)
        ·
          refine ⟨1332369786283302019395223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7105972193510944103441189 1332369786283302019395223)
          ·
            refine ⟨1998554679424953029092835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332369786283302019395223 1998554679424953029092835)
            ·
              refine ⟨2997832019137429543639253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998554679424953029092835 2997832019137429543639253)
              ·
                refine ⟨70261687948533504929045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2997832019137429543639253 70261687948533504929045)
                ·
                  rfl

theorem cell22_1847261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 7].length) (baseStart_1847261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847261 prefixEnd_1847261 := by exact prefixLift 1847261
  have htrace : WordTrace (prefixWord ++ tailWord_1847261) baseStart_1847261 baseEnd_1847261 := by
    simpa [prefixWord, tailWord_1847261, baseEnd_1847261] using wordTrace_append hprefix tailTrace_1847261
  have hstable : (prefixWord ++ tailWord_1847261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847261).length < 2 ^ (prefixWord ++ tailWord_1847261).sum := by decide
  have hdescent : baseEnd_1847261 < baseStart_1847261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847306 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_1847306 : Nat := 118140960795 + 1847306 * 2 ^ 59
def prefixEnd_1847306 : Nat := 4983230072969 + 3 ^ 40 * 1847306 * 2
def baseEnd_1847306 : Nat := 210790198652145475662089

theorem tailTrace_1847306 : CollatzResearch.WordTrace tailWord_1847306 prefixEnd_1847306 210790198652145475662089 := by
  unfold tailWord_1847306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16844196261383332898022443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44917856697022221061393181 16844196261383332898022443)
  ·
    refine ⟨25266294392074999347033665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16844196261383332898022443 25266294392074999347033665)
    ·
      refine ⟨18949720794056249510275249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25266294392074999347033665 18949720794056249510275249)
      ·
        refine ⟨14212290595542187132706437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18949720794056249510275249 14212290595542187132706437)
        ·
          refine ⟨2664804486664160087382457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14212290595542187132706437 2664804486664160087382457)
          ·
            refine ⟨1998603364998120065536843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664804486664160087382457 1998603364998120065536843)
            ·
              refine ⟨2997905047497180098305265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998603364998120065536843 2997905047497180098305265)
              ·
                refine ⟨2248428785622885073728949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997905047497180098305265 2248428785622885073728949)
                ·
                  refine ⟨210790198652145475662089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2248428785622885073728949 210790198652145475662089)
                  ·
                    rfl

theorem cell22_1847306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_1847306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847306 prefixEnd_1847306 := by exact prefixLift 1847306
  have htrace : WordTrace (prefixWord ++ tailWord_1847306) baseStart_1847306 baseEnd_1847306 := by
    simpa [prefixWord, tailWord_1847306, baseEnd_1847306] using wordTrace_append hprefix tailTrace_1847306
  have hstable : (prefixWord ++ tailWord_1847306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847306).length < 2 ^ (prefixWord ++ tailWord_1847306).sum := by decide
  have hdescent : baseEnd_1847306 < baseStart_1847306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847347 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 1, 6]
def baseStart_1847347 : Nat := 118140960795 + 1847347 * 2 ^ 59
def prefixEnd_1847347 : Nat := 4983230072969 + 3 ^ 40 * 1847347 * 2
def baseEnd_1847347 : Nat := 632384631094325986711141

theorem tailTrace_1847347 : CollatzResearch.WordTrace tailWord_1847347 prefixEnd_1847347 632384631094325986711141 := by
  unfold tailWord_1847347
  simp only [CollatzResearch.WordTrace]
  refine ⟨67378280438384795594332295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44918853625589863729554863 67378280438384795594332295)
  ·
    refine ⟨101067420657577193391498443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67378280438384795594332295 101067420657577193391498443)
    ·
      refine ⟨151601130986365790087247665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101067420657577193391498443 151601130986365790087247665)
      ·
        refine ⟨113700848239774342565435749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151601130986365790087247665 113700848239774342565435749)
        ·
          refine ⟨21318909044957689231019203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113700848239774342565435749 21318909044957689231019203)
          ·
            refine ⟨31978363567436533846528805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21318909044957689231019203 31978363567436533846528805)
            ·
              refine ⟨5995943168894350096224151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31978363567436533846528805 5995943168894350096224151)
              ·
                refine ⟨8993914753341525144336227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995943168894350096224151 8993914753341525144336227)
                ·
                  refine ⟨13490872130012287716504341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8993914753341525144336227 13490872130012287716504341)
                  ·
                    refine ⟨632384631094325986711141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13490872130012287716504341 632384631094325986711141)
                    ·
                      rfl

theorem cell22_1847347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_1847347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847347 prefixEnd_1847347 := by exact prefixLift 1847347
  have htrace : WordTrace (prefixWord ++ tailWord_1847347) baseStart_1847347 baseEnd_1847347 := by
    simpa [prefixWord, tailWord_1847347, baseEnd_1847347] using wordTrace_append hprefix tailTrace_1847347
  have hstable : (prefixWord ++ tailWord_1847347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847347).length < 2 ^ (prefixWord ++ tailWord_1847347).sum := by decide
  have hdescent : baseEnd_1847347 < baseStart_1847347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847349 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1847349 : Nat := 118140960795 + 1847349 * 2 ^ 59
def prefixEnd_1847349 : Nat := 4983230072969 + 3 ^ 40 * 1847349 * 2
def baseEnd_1847349 : Nat := 632385315735198648161135

theorem tailTrace_1847349 : CollatzResearch.WordTrace tailWord_1847349 prefixEnd_1847349 632385315735198648161135 := by
  unfold tailWord_1847349
  simp only [CollatzResearch.WordTrace]
  refine ⟨67378353384377549935905101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44918902256251699957270067 67378353384377549935905101)
  ·
    refine ⟨25266882519141581225964413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67378353384377549935905101 25266882519141581225964413)
    ·
      refine ⟨9475080944678092959736655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25266882519141581225964413 9475080944678092959736655)
      ·
        refine ⟨14212621417017139439604983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9475080944678092959736655 14212621417017139439604983)
        ·
          refine ⟨21318932125525709159407475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212621417017139439604983 21318932125525709159407475)
          ·
            refine ⟨31978398188288563739111213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21318932125525709159407475 31978398188288563739111213)
            ·
              refine ⟨11991899320608211402166705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31978398188288563739111213 11991899320608211402166705)
              ·
                refine ⟨8993924490456158551625029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11991899320608211402166705 8993924490456158551625029)
                ·
                  refine ⟨1686360841960529728429693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8993924490456158551625029 1686360841960529728429693)
                  ·
                    refine ⟨632385315735198648161135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686360841960529728429693 632385315735198648161135)
                    ·
                      rfl

theorem cell22_1847349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1847349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847349 prefixEnd_1847349 := by exact prefixLift 1847349
  have htrace : WordTrace (prefixWord ++ tailWord_1847349) baseStart_1847349 baseEnd_1847349 := by
    simpa [prefixWord, tailWord_1847349, baseEnd_1847349] using wordTrace_append hprefix tailTrace_1847349
  have hstable : (prefixWord ++ tailWord_1847349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847349).length < 2 ^ (prefixWord ++ tailWord_1847349).sum := by decide
  have hdescent : baseEnd_1847349 < baseStart_1847349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847428 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1847428 : Nat := 118140960795 + 1847428 * 2 ^ 59
def prefixEnd_1847428 : Nat := 4983230072969 + 3 ^ 40 * 1847428 * 2
def baseEnd_1847428 : Nat := 632412359049668775435893

theorem tailTrace_1847428 : CollatzResearch.WordTrace tailWord_1847428 prefixEnd_1847428 632412359049668775435893 := by
  unfold tailWord_1847428
  simp only [CollatzResearch.WordTrace]
  refine ⟨33690617375545673214015469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44920823167394230952020625 33690617375545673214015469)
  ·
    refine ⟨12633981515829627455255801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33690617375545673214015469 12633981515829627455255801)
    ·
      refine ⟨9475486136872220591441851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12633981515829627455255801 9475486136872220591441851)
      ·
        refine ⟨14213229205308330887162777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9475486136872220591441851 14213229205308330887162777)
        ·
          refine ⟨10659921903981248165372083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14213229205308330887162777 10659921903981248165372083)
          ·
            refine ⟨15989882855971872248058125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10659921903981248165372083 15989882855971872248058125)
            ·
              refine ⟨5996206070989452093021797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15989882855971872248058125 5996206070989452093021797)
              ·
                refine ⟨1124288638310522267441587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5996206070989452093021797 1124288638310522267441587)
                ·
                  refine ⟨1686432957465783401162381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124288638310522267441587 1686432957465783401162381)
                  ·
                    refine ⟨632412359049668775435893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686432957465783401162381 632412359049668775435893)
                    ·
                      rfl

theorem cell22_1847428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1847428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847428 prefixEnd_1847428 := by exact prefixLift 1847428
  have htrace : WordTrace (prefixWord ++ tailWord_1847428) baseStart_1847428 baseEnd_1847428 := by
    simpa [prefixWord, tailWord_1847428, baseEnd_1847428] using wordTrace_append hprefix tailTrace_1847428
  have hstable : (prefixWord ++ tailWord_1847428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847428).length < 2 ^ (prefixWord ++ tailWord_1847428).sum := by decide
  have hdescent : baseEnd_1847428 < baseStart_1847428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847467 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_1847467 : Nat := 118140960795 + 1847467 * 2 ^ 59
def prefixEnd_1847467 : Nat := 4983230072969 + 3 ^ 40 * 1847467 * 2
def baseEnd_1847467 : Nat := 632425709546685673710773

theorem tailTrace_1847467 : CollatzResearch.WordTrace tailWord_1847467 prefixEnd_1847467 632425709546685673710773 := by
  unfold tailWord_1847467
  simp only [CollatzResearch.WordTrace]
  refine ⟨67382657197950056088700655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44921771465300037392467103 67382657197950056088700655)
  ·
    refine ⟨101073985796925084133050983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67382657197950056088700655 101073985796925084133050983)
    ·
      refine ⟨151610978695387626199576475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101073985796925084133050983 151610978695387626199576475)
      ·
        refine ⟨227416468043081439299364713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151610978695387626199576475 227416468043081439299364713)
        ·
          refine ⟨170562351032311079474523535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227416468043081439299364713 170562351032311079474523535)
          ·
            refine ⟨255843526548466619211785303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170562351032311079474523535 255843526548466619211785303)
            ·
              refine ⟨383765289822699928817677955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255843526548466619211785303 383765289822699928817677955)
              ·
                refine ⟨575647934734049893226516933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383765289822699928817677955 575647934734049893226516933)
                ·
                  refine ⟨107933987762634354979971925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575647934734049893226516933 107933987762634354979971925)
                  ·
                    refine ⟨632425709546685673710773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107933987762634354979971925 632425709546685673710773)
                    ·
                      rfl

theorem cell22_1847467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_1847467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847467 prefixEnd_1847467 := by exact prefixLift 1847467
  have htrace : WordTrace (prefixWord ++ tailWord_1847467) baseStart_1847467 baseEnd_1847467 := by
    simpa [prefixWord, tailWord_1847467, baseEnd_1847467] using wordTrace_append hprefix tailTrace_1847467
  have hstable : (prefixWord ++ tailWord_1847467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847467).length < 2 ^ (prefixWord ++ tailWord_1847467).sum := by decide
  have hdescent : baseEnd_1847467 < baseStart_1847467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847533 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1847533 : Nat := 118140960795 + 1847533 * 2 ^ 59
def prefixEnd_1847533 : Nat := 4983230072969 + 3 ^ 40 * 1847533 * 2
def baseEnd_1847533 : Nat := 632448302695483501560571

theorem tailTrace_1847533 : CollatzResearch.WordTrace tailWord_1847533 prefixEnd_1847533 632448302695483501560571 := by
  unfold tailWord_1847533
  simp only [CollatzResearch.WordTrace]
  refine ⟨67385064415710949360603253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44923376277140632907068835 67385064415710949360603253)
  ·
    refine ⟨6317349788972901502556555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67385064415710949360603253 6317349788972901502556555)
    ·
      refine ⟨9476024683459352253834833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6317349788972901502556555 9476024683459352253834833)
      ·
        refine ⟨7107018512594514190376125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9476024683459352253834833 7107018512594514190376125)
        ·
          refine ⟨2665131942222942821391047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7107018512594514190376125 2665131942222942821391047)
          ·
            refine ⟨3997697913334414232086571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665131942222942821391047 3997697913334414232086571)
            ·
              refine ⟨5996546870001621348129857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997697913334414232086571 5996546870001621348129857)
              ·
                refine ⟨4497410152501216011097393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996546870001621348129857 4497410152501216011097393)
                ·
                  refine ⟨3373057614375912008323045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4497410152501216011097393 3373057614375912008323045)
                  ·
                    refine ⟨632448302695483501560571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373057614375912008323045 632448302695483501560571)
                    ·
                      rfl

theorem cell22_1847533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1847533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847533 prefixEnd_1847533 := by exact prefixLift 1847533
  have htrace : WordTrace (prefixWord ++ tailWord_1847533) baseStart_1847533 baseEnd_1847533 := by
    simpa [prefixWord, tailWord_1847533, baseEnd_1847533] using wordTrace_append hprefix tailTrace_1847533
  have hstable : (prefixWord ++ tailWord_1847533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847533).length < 2 ^ (prefixWord ++ tailWord_1847533).sum := by decide
  have hdescent : baseEnd_1847533 < baseStart_1847533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847651 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 4, 4]
def baseStart_1847651 : Nat := 118140960795 + 1847651 * 2 ^ 59
def prefixEnd_1847651 : Nat := 4983230072969 + 3 ^ 40 * 1847651 * 2
def baseEnd_1847651 : Nat := 632488696506970527110209

theorem tailTrace_1847651 : CollatzResearch.WordTrace tailWord_1847651 prefixEnd_1847651 632488696506970527110209 := by
  unfold tailWord_1847651
  simp only [CollatzResearch.WordTrace]
  refine ⟨67389368229283455513398807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44926245486188970342265871 67389368229283455513398807)
  ·
    refine ⟨101084052343925183270098211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67389368229283455513398807 101084052343925183270098211)
    ·
      refine ⟨151626078515887774905147317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101084052343925183270098211 151626078515887774905147317)
      ·
        refine ⟨14214944860864478897357561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151626078515887774905147317 14214944860864478897357561)
        ·
          refine ⟨10661208645648359173018171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14214944860864478897357561 10661208645648359173018171)
          ·
            refine ⟨15991812968472538759527257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661208645648359173018171 15991812968472538759527257)
            ·
              refine ⟨11993859726354404069645443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15991812968472538759527257 11993859726354404069645443)
              ·
                refine ⟨17990789589531606104468165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11993859726354404069645443 17990789589531606104468165)
                ·
                  refine ⟨3373273048037176144587781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17990789589531606104468165 3373273048037176144587781)
                  ·
                    refine ⟨632488696506970527110209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373273048037176144587781 632488696506970527110209)
                    ·
                      rfl

theorem cell22_1847651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_1847651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847651 prefixEnd_1847651 := by exact prefixLift 1847651
  have htrace : WordTrace (prefixWord ++ tailWord_1847651) baseStart_1847651 baseEnd_1847651 := by
    simpa [prefixWord, tailWord_1847651, baseEnd_1847651] using wordTrace_append hprefix tailTrace_1847651
  have hstable : (prefixWord ++ tailWord_1847651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847651).length < 2 ^ (prefixWord ++ tailWord_1847651).sum := by decide
  have hdescent : baseEnd_1847651 < baseStart_1847651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847653 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_1847653 : Nat := 118140960795 + 1847653 * 2 ^ 59
def prefixEnd_1847653 : Nat := 4983230072969 + 3 ^ 40 * 1847653 * 2
def baseEnd_1847653 : Nat := 632489381147843188560203

theorem tailTrace_1847653 : CollatzResearch.WordTrace tailWord_1847653 prefixEnd_1847653 632489381147843188560203 := by
  unfold tailWord_1847653
  simp only [CollatzResearch.WordTrace]
  refine ⟨67389441175276209854971613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44926294116850806569981075 67389441175276209854971613)
  ·
    refine ⟨25271040440728578695614355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67389441175276209854971613 25271040440728578695614355)
    ·
      refine ⟨37906560661092868043421533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25271040440728578695614355 37906560661092868043421533)
      ·
        refine ⟨14214960247909825516283075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37906560661092868043421533 14214960247909825516283075)
        ·
          refine ⟨21322440371864738274424613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14214960247909825516283075 21322440371864738274424613)
          ·
            refine ⟨3997957569724638426454615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21322440371864738274424613 3997957569724638426454615)
            ·
              refine ⟨5996936354586957639681923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997957569724638426454615 5996936354586957639681923)
              ·
                refine ⟨8995404531880436459522885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996936354586957639681923 8995404531880436459522885)
                ·
                  refine ⟨1686638349727581836160541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8995404531880436459522885 1686638349727581836160541)
                  ·
                    refine ⟨632489381147843188560203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686638349727581836160541 632489381147843188560203)
                    ·
                      rfl

theorem cell22_1847653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_1847653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847653 prefixEnd_1847653 := by exact prefixLift 1847653
  have htrace : WordTrace (prefixWord ++ tailWord_1847653) baseStart_1847653 baseEnd_1847653 := by
    simpa [prefixWord, tailWord_1847653, baseEnd_1847653] using wordTrace_append hprefix tailTrace_1847653
  have hstable : (prefixWord ++ tailWord_1847653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847653).length < 2 ^ (prefixWord ++ tailWord_1847653).sum := by decide
  have hdescent : baseEnd_1847653 < baseStart_1847653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847700 : List Nat := [2, 4, 2, 1, 4, 1, 8]
def baseStart_1847700 : Nat := 118140960795 + 1847700 * 2 ^ 59
def prefixEnd_1847700 : Nat := 4983230072969 + 3 ^ 40 * 1847700 * 2
def baseEnd_1847700 : Nat := 23426128526235212319817

theorem tailTrace_1847700 : CollatzResearch.WordTrace tailWord_1847700 prefixEnd_1847700 23426128526235212319817 := by
  unfold tailWord_1847700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33695577703052968440966277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44927436937403957921288369 33695577703052968440966277)
  ·
    refine ⟨6317920819322431582681177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33695577703052968440966277 6317920819322431582681177)
    ·
      refine ⟨4738440614491823687010883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6317920819322431582681177 4738440614491823687010883)
      ·
        refine ⟨7107660921737735530516325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738440614491823687010883 7107660921737735530516325)
        ·
          refine ⟨1332686422825825411971811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7107660921737735530516325 1332686422825825411971811)
          ·
            refine ⟨1999029634238738117957717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332686422825825411971811 1999029634238738117957717)
            ·
              refine ⟨23426128526235212319817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1999029634238738117957717 23426128526235212319817)
              ·
                rfl

theorem cell22_1847700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 8].length) (baseStart_1847700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847700 prefixEnd_1847700 := by exact prefixLift 1847700
  have htrace : WordTrace (prefixWord ++ tailWord_1847700) baseStart_1847700 baseEnd_1847700 := by
    simpa [prefixWord, tailWord_1847700, baseEnd_1847700] using wordTrace_append hprefix tailTrace_1847700
  have hstable : (prefixWord ++ tailWord_1847700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847700).length < 2 ^ (prefixWord ++ tailWord_1847700).sum := by decide
  have hdescent : baseEnd_1847700 < baseStart_1847700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847711 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 7]
def baseStart_1847711 : Nat := 118140960795 + 1847711 * 2 ^ 59
def prefixEnd_1847711 : Nat := 4983230072969 + 3 ^ 40 * 1847711 * 2
def baseEnd_1847711 : Nat := 210836411911050123536675

theorem tailTrace_1847711 : CollatzResearch.WordTrace tailWord_1847711 prefixEnd_1847711 210836411911050123536675 := by
  unfold tailWord_1847711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67391556609066085760582987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44927704406044057173721991 67391556609066085760582987)
  ·
    refine ⟨101087334913599128640874481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67391556609066085760582987 101087334913599128640874481)
    ·
      refine ⟨75815501185199346480655861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101087334913599128640874481 75815501185199346480655861)
      ·
        refine ⟨7107703236112438732561487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75815501185199346480655861 7107703236112438732561487)
        ·
          refine ⟨10661554854168658098842231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107703236112438732561487 10661554854168658098842231)
          ·
            refine ⟨15992332281252987148263347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661554854168658098842231 15992332281252987148263347)
            ·
              refine ⟨23988498421879480722395021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15992332281252987148263347 23988498421879480722395021)
              ·
                refine ⟨8995686908204805270898133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23988498421879480722395021 8995686908204805270898133)
                ·
                  refine ⟨210836411911050123536675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8995686908204805270898133 210836411911050123536675)
                  ·
                    rfl

theorem cell22_1847711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_1847711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847711 prefixEnd_1847711 := by exact prefixLift 1847711
  have htrace : WordTrace (prefixWord ++ tailWord_1847711) baseStart_1847711 baseEnd_1847711 := by
    simpa [prefixWord, tailWord_1847711, baseEnd_1847711] using wordTrace_append hprefix tailTrace_1847711
  have hstable : (prefixWord ++ tailWord_1847711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847711).length < 2 ^ (prefixWord ++ tailWord_1847711).sum := by decide
  have hdescent : baseEnd_1847711 < baseStart_1847711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847715 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 3, 3]
def baseStart_1847715 : Nat := 118140960795 + 1847715 * 2 ^ 59
def prefixEnd_1847715 : Nat := 4983230072969 + 3 ^ 40 * 1847715 * 2
def baseEnd_1847715 : Nat := 632510605014895693510013

theorem tailTrace_1847715 : CollatzResearch.WordTrace tailWord_1847715 prefixEnd_1847715 632510605014895693510013 := by
  unfold tailWord_1847715
  simp only [CollatzResearch.WordTrace]
  refine ⟨67391702501051594443728599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44927801667367729629152399 67391702501051594443728599)
  ·
    refine ⟨101087553751577391665592899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67391702501051594443728599 101087553751577391665592899)
    ·
      refine ⟨151631330627366087498389349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101087553751577391665592899 151631330627366087498389349)
      ·
        refine ⟨28430874492631141405948003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151631330627366087498389349 28430874492631141405948003)
        ·
          refine ⟨42646311738946712108922005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28430874492631141405948003 42646311738946712108922005)
          ·
            refine ⟨1999045862763127130105719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42646311738946712108922005 1999045862763127130105719)
            ·
              refine ⟨2998568794144690695158579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999045862763127130105719 2998568794144690695158579)
              ·
                refine ⟨4497853191217036042737869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998568794144690695158579 4497853191217036042737869)
                ·
                  refine ⟨1686694946706388516026701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4497853191217036042737869 1686694946706388516026701)
                  ·
                    refine ⟨632510605014895693510013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686694946706388516026701 632510605014895693510013)
                    ·
                      rfl

theorem cell22_1847715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 3].length) (baseStart_1847715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847715 prefixEnd_1847715 := by exact prefixLift 1847715
  have htrace : WordTrace (prefixWord ++ tailWord_1847715) baseStart_1847715 baseEnd_1847715 := by
    simpa [prefixWord, tailWord_1847715, baseEnd_1847715] using wordTrace_append hprefix tailTrace_1847715
  have hstable : (prefixWord ++ tailWord_1847715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847715).length < 2 ^ (prefixWord ++ tailWord_1847715).sum := by decide
  have hdescent : baseEnd_1847715 < baseStart_1847715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847762 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1847762 : Nat := 118140960795 + 1847762 * 2 ^ 59
def prefixEnd_1847762 : Nat := 4983230072969 + 3 ^ 40 * 1847762 * 2
def baseEnd_1847762 : Nat := 210842231358467745861623

theorem tailTrace_1847762 : CollatzResearch.WordTrace tailWord_1847762 prefixEnd_1847762 210842231358467745861623 := by
  unfold tailWord_1847762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16848354182970330367672385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44928944487920880980459693 16848354182970330367672385)
  ·
    refine ⟨12636265637227747775754289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16848354182970330367672385 12636265637227747775754289)
    ·
      refine ⟨9477199227920810831815717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12636265637227747775754289 9477199227920810831815717)
      ·
        refine ⟨1776974855235152030965447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9477199227920810831815717 1776974855235152030965447)
        ·
          refine ⟨2665462282852728046448171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776974855235152030965447 2665462282852728046448171)
          ·
            refine ⟨3998193424279092069672257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665462282852728046448171 3998193424279092069672257)
            ·
              refine ⟨2998645068209319052254193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998193424279092069672257 2998645068209319052254193)
              ·
                refine ⟨2248983801156989289190645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998645068209319052254193 2248983801156989289190645)
                ·
                  refine ⟨210842231358467745861623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2248983801156989289190645 210842231358467745861623)
                  ·
                    rfl

theorem cell22_1847762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1847762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847762 prefixEnd_1847762 := by exact prefixLift 1847762
  have htrace : WordTrace (prefixWord ++ tailWord_1847762) baseStart_1847762 baseEnd_1847762 := by
    simpa [prefixWord, tailWord_1847762, baseEnd_1847762] using wordTrace_append hprefix tailTrace_1847762
  have hstable : (prefixWord ++ tailWord_1847762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847762).length < 2 ^ (prefixWord ++ tailWord_1847762).sum := by decide
  have hdescent : baseEnd_1847762 < baseStart_1847762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847773 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1847773 : Nat := 118140960795 + 1847773 * 2 ^ 59
def prefixEnd_1847773 : Nat := 4983230072969 + 3 ^ 40 * 1847773 * 2
def baseEnd_1847773 : Nat := 210843486533400958519945

theorem tailTrace_1847773 : CollatzResearch.WordTrace tailWord_1847773 prefixEnd_1847773 210843486533400958519945 := by
  unfold tailWord_1847773
  simp only [CollatzResearch.WordTrace]
  refine ⟨67393817934841470349339973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44929211956560980232893315 67393817934841470349339973)
  ·
    refine ⟨12636340862782775690501245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67393817934841470349339973 12636340862782775690501245)
    ·
      refine ⟨4738627823543540883937967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12636340862782775690501245 4738627823543540883937967)
      ·
        refine ⟨7107941735315311325906951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738627823543540883937967 7107941735315311325906951)
        ·
          refine ⟨10661912602972966988860427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107941735315311325906951 10661912602972966988860427)
          ·
            refine ⟨15992868904459450483290641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661912602972966988860427 15992868904459450483290641)
            ·
              refine ⟨11994651678344587862467981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15992868904459450483290641 11994651678344587862467981)
              ·
                refine ⟨4497994379379220448425493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11994651678344587862467981 4497994379379220448425493)
                ·
                  refine ⟨210843486533400958519945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4497994379379220448425493 210843486533400958519945)
                  ·
                    rfl

theorem cell22_1847773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1847773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847773 prefixEnd_1847773 := by exact prefixLift 1847773
  have htrace : WordTrace (prefixWord ++ tailWord_1847773) baseStart_1847773 baseEnd_1847773 := by
    simpa [prefixWord, tailWord_1847773, baseEnd_1847773] using wordTrace_append hprefix tailTrace_1847773
  have hstable : (prefixWord ++ tailWord_1847773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847773).length < 2 ^ (prefixWord ++ tailWord_1847773).sum := by decide
  have hdescent : baseEnd_1847773 < baseStart_1847773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847788 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_1847788 : Nat := 118140960795 + 1847788 * 2 ^ 59
def prefixEnd_1847788 : Nat := 4983230072969 + 3 ^ 40 * 1847788 * 2
def baseEnd_1847788 : Nat := 632535594406747836434789

theorem tailTrace_1847788 : CollatzResearch.WordTrace tailWord_1847788 prefixEnd_1847788 632535594406747836434789 := by
  unfold tailWord_1847788
  simp only [CollatzResearch.WordTrace]
  refine ⟨33697182514893563955568009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44929576686524751940757345 33697182514893563955568009)
  ·
    refine ⟨25272886886170172966676007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33697182514893563955568009 25272886886170172966676007)
    ·
      refine ⟨37909330329255259450014011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25272886886170172966676007 37909330329255259450014011)
      ·
        refine ⟨56863995493882889175021017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37909330329255259450014011 56863995493882889175021017)
        ·
          refine ⟨42647996620412166881265763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56863995493882889175021017 42647996620412166881265763)
          ·
            refine ⟨63971994930618250321898645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42647996620412166881265763 63971994930618250321898645)
            ·
              refine ⟨2998687262372730483838999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63971994930618250321898645 2998687262372730483838999)
              ·
                refine ⟨4498030893559095725758499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998687262372730483838999 4498030893559095725758499)
                ·
                  refine ⟨6747046340338643588637749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498030893559095725758499 6747046340338643588637749)
                  ·
                    refine ⟨632535594406747836434789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6747046340338643588637749 632535594406747836434789)
                    ·
                      rfl

theorem cell22_1847788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_1847788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847788 prefixEnd_1847788 := by exact prefixLift 1847788
  have htrace : WordTrace (prefixWord ++ tailWord_1847788) baseStart_1847788 baseEnd_1847788 := by
    simpa [prefixWord, tailWord_1847788, baseEnd_1847788] using wordTrace_append hprefix tailTrace_1847788
  have hstable : (prefixWord ++ tailWord_1847788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847788).length < 2 ^ (prefixWord ++ tailWord_1847788).sum := by decide
  have hdescent : baseEnd_1847788 < baseStart_1847788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847801 : List Nat := [1, 2, 1, 3, 1, 2, 2, 10]
def baseStart_1847801 : Nat := 118140960795 + 1847801 * 2 ^ 59
def prefixEnd_1847801 : Nat := 4983230072969 + 3 ^ 40 * 1847801 * 2
def baseEnd_1847801 : Nat := 70282227174713348428861

theorem tailTrace_1847801 : CollatzResearch.WordTrace tailWord_1847801 prefixEnd_1847801 70282227174713348428861 := by
  unfold tailWord_1847801
  simp only [CollatzResearch.WordTrace]
  refine ⟨67394839178740031131359257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44929892785826687420906171 67394839178740031131359257)
  ·
    refine ⟨50546129384055023348519443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67394839178740031131359257 50546129384055023348519443)
    ·
      refine ⟨75819194076082535022779165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50546129384055023348519443 75819194076082535022779165)
      ·
        refine ⟨28432197778530950633542187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75819194076082535022779165 28432197778530950633542187)
        ·
          refine ⟨42648296667796425950313281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28432197778530950633542187 42648296667796425950313281)
          ·
            refine ⟨31986222500847319462734961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42648296667796425950313281 31986222500847319462734961)
            ·
              refine ⟨23989666875635489597051221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31986222500847319462734961 23989666875635489597051221)
              ·
                refine ⟨70282227174713348428861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23989666875635489597051221 70282227174713348428861)
                ·
                  rfl

theorem cell22_1847801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 10].length) (baseStart_1847801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847801 prefixEnd_1847801 := by exact prefixLift 1847801
  have htrace : WordTrace (prefixWord ++ tailWord_1847801) baseStart_1847801 baseEnd_1847801 := by
    simpa [prefixWord, tailWord_1847801, baseEnd_1847801] using wordTrace_append hprefix tailTrace_1847801
  have hstable : (prefixWord ++ tailWord_1847801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847801).length < 2 ^ (prefixWord ++ tailWord_1847801).sum := by decide
  have hdescent : baseEnd_1847801 < baseStart_1847801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847822 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_1847822 : Nat := 118140960795 + 1847822 * 2 ^ 59
def prefixEnd_1847822 : Nat := 4983230072969 + 3 ^ 40 * 1847822 * 2
def baseEnd_1847822 : Nat := 632547233301583081084685

theorem tailTrace_1847822 : CollatzResearch.WordTrace tailWord_1847822 prefixEnd_1847822 632547233301583081084685 := by
  unfold tailWord_1847822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424450638957993964734215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44930403407775967811915813 8424450638957993964734215)
  ·
    refine ⟨12636675958436990947101323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8424450638957993964734215 12636675958436990947101323)
    ·
      refine ⟨18955013937655486420651985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12636675958436990947101323 18955013937655486420651985)
      ·
        refine ⟨14216260453241614815488989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18955013937655486420651985 14216260453241614815488989)
        ·
          refine ⟨5331097669965605555808371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14216260453241614815488989 5331097669965605555808371)
          ·
            refine ⟨7996646504948408333712557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331097669965605555808371 7996646504948408333712557)
            ·
              refine ⟨2998742439355653125142209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7996646504948408333712557 2998742439355653125142209)
              ·
                refine ⟨2249056829516739843856657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998742439355653125142209 2249056829516739843856657)
                ·
                  refine ⟨1686792622137554882892493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249056829516739843856657 1686792622137554882892493)
                  ·
                    refine ⟨632547233301583081084685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686792622137554882892493 632547233301583081084685)
                    ·
                      rfl

theorem cell22_1847822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_1847822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847822 prefixEnd_1847822 := by exact prefixLift 1847822
  have htrace : WordTrace (prefixWord ++ tailWord_1847822) baseStart_1847822 baseEnd_1847822 := by
    simpa [prefixWord, tailWord_1847822, baseEnd_1847822] using wordTrace_append hprefix tailTrace_1847822
  have hstable : (prefixWord ++ tailWord_1847822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847822).length < 2 ^ (prefixWord ++ tailWord_1847822).sum := by decide
  have hdescent : baseEnd_1847822 < baseStart_1847822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847833 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_1847833 : Nat := 118140960795 + 1847833 * 2 ^ 59
def prefixEnd_1847833 : Nat := 4983230072969 + 3 ^ 40 * 1847833 * 2
def baseEnd_1847833 : Nat := 632550998826382719059651

theorem tailTrace_1847833 : CollatzResearch.WordTrace tailWord_1847833 prefixEnd_1847833 632550998826382719059651 := by
  unfold tailWord_1847833
  simp only [CollatzResearch.WordTrace]
  refine ⟨67396006314624100596524153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44930670876416067064349435 67396006314624100596524153)
  ·
    refine ⟨50547004735968075447393115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67396006314624100596524153 50547004735968075447393115)
    ·
      refine ⟨75820507103952113171089673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50547004735968075447393115 75820507103952113171089673)
      ·
        refine ⟨56865380327964084878317255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75820507103952113171089673 56865380327964084878317255)
        ·
          refine ⟨85298070491946127317475883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56865380327964084878317255 85298070491946127317475883)
          ·
            refine ⟨127947105737919190976213825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85298070491946127317475883 127947105737919190976213825)
            ·
              refine ⟨95960329303439393232160369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127947105737919190976213825 95960329303439393232160369)
              ·
                refine ⟨71970246977579544924120277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95960329303439393232160369 71970246977579544924120277)
                ·
                  refine ⟨1686802663537020584159069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 71970246977579544924120277 1686802663537020584159069)
                  ·
                    refine ⟨632550998826382719059651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686802663537020584159069 632550998826382719059651)
                    ·
                      rfl

theorem cell22_1847833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_1847833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847833 prefixEnd_1847833 := by exact prefixLift 1847833
  have htrace : WordTrace (prefixWord ++ tailWord_1847833) baseStart_1847833 baseEnd_1847833 := by
    simpa [prefixWord, tailWord_1847833, baseEnd_1847833] using wordTrace_append hprefix tailTrace_1847833
  have hstable : (prefixWord ++ tailWord_1847833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847833).length < 2 ^ (prefixWord ++ tailWord_1847833).sum := by decide
  have hdescent : baseEnd_1847833 < baseStart_1847833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847884 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_1847884 : Nat := 118140960795 + 1847884 * 2 ^ 59
def prefixEnd_1847884 : Nat := 4983230072969 + 3 ^ 40 * 1847884 * 2
def baseEnd_1847884 : Nat := 632568457168635586034495

theorem tailTrace_1847884 : CollatzResearch.WordTrace tailWord_1847884 prefixEnd_1847884 632568457168635586034495 := by
  unfold tailWord_1847884
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698933218719668153315353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44931910958292890871087137 33698933218719668153315353)
  ·
    refine ⟨25274199914039751114986515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33698933218719668153315353 25274199914039751114986515)
    ·
      refine ⟨37911299871059626672479773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25274199914039751114986515 37911299871059626672479773)
      ·
        refine ⟨14216737451647360002179915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37911299871059626672479773 14216737451647360002179915)
        ·
          refine ⟨21325106177471040003269873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14216737451647360002179915 21325106177471040003269873)
          ·
            refine ⟨15993829633103280002452405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21325106177471040003269873 15993829633103280002452405)
            ·
              refine ⟨1499421528103432500229913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15993829633103280002452405 1499421528103432500229913)
              ·
                refine ⟨1124566146077574375172435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499421528103432500229913 1124566146077574375172435)
                ·
                  refine ⟨1686849219116361562758653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124566146077574375172435 1686849219116361562758653)
                  ·
                    refine ⟨632568457168635586034495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686849219116361562758653 632568457168635586034495)
                    ·
                      rfl

theorem cell22_1847884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_1847884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847884 prefixEnd_1847884 := by exact prefixLift 1847884
  have htrace : WordTrace (prefixWord ++ tailWord_1847884) baseStart_1847884 baseEnd_1847884 := by
    simpa [prefixWord, tailWord_1847884, baseEnd_1847884] using wordTrace_append hprefix tailTrace_1847884
  have hstable : (prefixWord ++ tailWord_1847884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847884).length < 2 ^ (prefixWord ++ tailWord_1847884).sum := by decide
  have hdescent : baseEnd_1847884 < baseStart_1847884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847908 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1847908 : Nat := 118140960795 + 1847908 * 2 ^ 59
def prefixEnd_1847908 : Nat := 4983230072969 + 3 ^ 40 * 1847908 * 2
def baseEnd_1847908 : Nat := 210858890953035841144807

theorem tailTrace_1847908 : CollatzResearch.WordTrace tailWord_1847908 prefixEnd_1847908 210858890953035841144807 := by
  unfold tailWord_1847908
  simp only [CollatzResearch.WordTrace]
  refine ⟨33699370894676194202752189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44932494526234925603669585 33699370894676194202752189)
  ·
    refine ⟨12637264085503572826032071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33699370894676194202752189 12637264085503572826032071)
    ·
      refine ⟨18955896128255359239048107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12637264085503572826032071 18955896128255359239048107)
      ·
        refine ⟨28433844192383038858572161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18955896128255359239048107 28433844192383038858572161)
        ·
          refine ⟨21325383144287279143929121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28433844192383038858572161 21325383144287279143929121)
          ·
            refine ⟨15994037358215459357946841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21325383144287279143929121 15994037358215459357946841)
            ·
              refine ⟨11995528018661594518460131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15994037358215459357946841 11995528018661594518460131)
              ·
                refine ⟨17993292027992391777690197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11995528018661594518460131 17993292027992391777690197)
                ·
                  refine ⟨210858890953035841144807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17993292027992391777690197 210858890953035841144807)
                  ·
                    rfl

theorem cell22_1847908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1847908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847908 prefixEnd_1847908 := by exact prefixLift 1847908
  have htrace : WordTrace (prefixWord ++ tailWord_1847908) baseStart_1847908 baseEnd_1847908 := by
    simpa [prefixWord, tailWord_1847908, baseEnd_1847908] using wordTrace_append hprefix tailTrace_1847908
  have hstable : (prefixWord ++ tailWord_1847908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847908).length < 2 ^ (prefixWord ++ tailWord_1847908).sum := by decide
  have hdescent : baseEnd_1847908 < baseStart_1847908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847978 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1847978 : Nat := 118140960795 + 1847978 * 2 ^ 59
def prefixEnd_1847978 : Nat := 4983230072969 + 3 ^ 40 * 1847978 * 2
def baseEnd_1847978 : Nat := 632600635289650674184207

theorem tailTrace_1847978 : CollatzResearch.WordTrace tailWord_1847978 prefixEnd_1847978 632600635289650674184207 := by
  unfold tailWord_1847978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16850323724774697590138147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44934196599399193573701725 16850323724774697590138147)
  ·
    refine ⟨25275485587162046385207221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16850323724774697590138147 25275485587162046385207221)
    ·
      refine ⟨2369576773796441848613177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25275485587162046385207221 2369576773796441848613177)
      ·
        refine ⟨1777182580347331386459883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2369576773796441848613177 1777182580347331386459883)
        ·
          refine ⟨2665773870520997079689825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777182580347331386459883 2665773870520997079689825)
          ·
            refine ⟨1999330402890747809767369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665773870520997079689825 1999330402890747809767369)
            ·
              refine ⟨1499497802168060857325527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999330402890747809767369 1499497802168060857325527)
              ·
                refine ⟨2249246703252091285988291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499497802168060857325527 2249246703252091285988291)
                ·
                  refine ⟨3373870054878136928982437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249246703252091285988291 3373870054878136928982437)
                  ·
                    refine ⟨632600635289650674184207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373870054878136928982437 632600635289650674184207)
                    ·
                      rfl

theorem cell22_1847978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1847978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847978 prefixEnd_1847978 := by exact prefixLift 1847978
  have htrace : WordTrace (prefixWord ++ tailWord_1847978) baseStart_1847978 baseEnd_1847978 := by
    simpa [prefixWord, tailWord_1847978, baseEnd_1847978] using wordTrace_append hprefix tailTrace_1847978
  have hstable : (prefixWord ++ tailWord_1847978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847978).length < 2 ^ (prefixWord ++ tailWord_1847978).sum := by decide
  have hdescent : baseEnd_1847978 < baseStart_1847978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847991 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 2, 3]
def baseStart_1847991 : Nat := 118140960795 + 1847991 * 2 ^ 59
def prefixEnd_1847991 : Nat := 4983230072969 + 3 ^ 40 * 1847991 * 2
def baseEnd_1847991 : Nat := 632605085455322973609167

theorem tailTrace_1847991 : CollatzResearch.WordTrace tailWord_1847991 prefixEnd_1847991 632605085455322973609167 := by
  unfold tailWord_1847991
  simp only [CollatzResearch.WordTrace]
  refine ⟨67401769048051693580775827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44934512698701129053850551 67401769048051693580775827)
  ·
    refine ⟨101102653572077540371163741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67401769048051693580775827 101102653572077540371163741)
    ·
      refine ⟨37913495089529077639186403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101102653572077540371163741 37913495089529077639186403)
      ·
        refine ⟨56870242634293616458779605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37913495089529077639186403 56870242634293616458779605)
        ·
          refine ⟨1332896311741256635752647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 56870242634293616458779605 1332896311741256635752647)
          ·
            refine ⟨1999344467611884953628971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332896311741256635752647 1999344467611884953628971)
            ·
              refine ⟨2999016701417827430443457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999344467611884953628971 2999016701417827430443457)
              ·
                refine ⟨2249262526063370572832593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999016701417827430443457 2249262526063370572832593)
                ·
                  refine ⟨1686946894547527929624445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249262526063370572832593 1686946894547527929624445)
                  ·
                    refine ⟨632605085455322973609167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686946894547527929624445 632605085455322973609167)
                    ·
                      rfl

theorem cell22_1847991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_1847991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1847991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1847991 prefixEnd_1847991 := by exact prefixLift 1847991
  have htrace : WordTrace (prefixWord ++ tailWord_1847991) baseStart_1847991 baseEnd_1847991 := by
    simpa [prefixWord, tailWord_1847991, baseEnd_1847991] using wordTrace_append hprefix tailTrace_1847991
  have hstable : (prefixWord ++ tailWord_1847991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847991).length < 2 ^ (prefixWord ++ tailWord_1847991).sum := by decide
  have hdescent : baseEnd_1847991 < baseStart_1847991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848021 : List Nat := [1, 3, 2, 5, 2, 1, 2, 6]
def baseStart_1848021 : Nat := 118140960795 + 1848021 * 2 ^ 59
def prefixEnd_1848021 : Nat := 4983230072969 + 3 ^ 40 * 1848021 * 2
def baseEnd_1848021 : Nat := 70290595007601432817675

theorem tailTrace_1848021 : CollatzResearch.WordTrace tailWord_1848021 prefixEnd_1848021 70290595007601432817675 := by
  unfold tailWord_1848021
  simp only [CollatzResearch.WordTrace]
  refine ⟨67402863237943008704367917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44935242158628672469578611 67402863237943008704367917)
  ·
    refine ⟨25276073714228628264137969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67402863237943008704367917 25276073714228628264137969)
    ·
      refine ⟨18957055285671471198103477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25276073714228628264137969 18957055285671471198103477)
      ·
        refine ⟨1777223933031700424822201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18957055285671471198103477 1777223933031700424822201)
        ·
          refine ⟨1332917949773775318616651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777223933031700424822201 1332917949773775318616651)
          ·
            refine ⟨1999376924660662977924977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332917949773775318616651 1999376924660662977924977)
            ·
              refine ⟨1499532693495497233443733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999376924660662977924977 1499532693495497233443733)
              ·
                refine ⟨70290595007601432817675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1499532693495497233443733 70290595007601432817675)
                ·
                  rfl

theorem cell22_1848021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 6].length) (baseStart_1848021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848021 prefixEnd_1848021 := by exact prefixLift 1848021
  have htrace : WordTrace (prefixWord ++ tailWord_1848021) baseStart_1848021 baseEnd_1848021 := by
    simpa [prefixWord, tailWord_1848021, baseEnd_1848021] using wordTrace_append hprefix tailTrace_1848021
  have hstable : (prefixWord ++ tailWord_1848021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848021).length < 2 ^ (prefixWord ++ tailWord_1848021).sum := by decide
  have hdescent : baseEnd_1848021 < baseStart_1848021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848036 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_1848036 : Nat := 118140960795 + 1848036 * 2 ^ 59
def prefixEnd_1848036 : Nat := 4983230072969 + 3 ^ 40 * 1848036 * 2
def baseEnd_1848036 : Nat := 632620489874957856234029

theorem tailTrace_1848036 : CollatzResearch.WordTrace tailWord_1848036 prefixEnd_1848036 632620489874957856234029 := by
  unfold tailWord_1848036
  simp only [CollatzResearch.WordTrace]
  refine ⟨33701705166444333133081981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44935606888592444177442641 33701705166444333133081981)
  ·
    refine ⟨12638139437416624924905743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33701705166444333133081981 12638139437416624924905743)
    ·
      refine ⟨18957209156124937387358615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12638139437416624924905743 18957209156124937387358615)
      ·
        refine ⟨28435813734187406081037923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18957209156124937387358615 28435813734187406081037923)
        ·
          refine ⟨42653720601281109121556885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28435813734187406081037923 42653720601281109121556885)
          ·
            refine ⟨1999393153185051990072979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42653720601281109121556885 1999393153185051990072979)
            ·
              refine ⟨2999089729777577985109469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999393153185051990072979 2999089729777577985109469)
              ·
                refine ⟨1124658648666591744416051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2999089729777577985109469 1124658648666591744416051)
                ·
                  refine ⟨1686987972999887616624077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124658648666591744416051 1686987972999887616624077)
                  ·
                    refine ⟨632620489874957856234029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686987972999887616624077 632620489874957856234029)
                    ·
                      rfl

theorem cell22_1848036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_1848036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848036 prefixEnd_1848036 := by exact prefixLift 1848036
  have htrace : WordTrace (prefixWord ++ tailWord_1848036) baseStart_1848036 baseEnd_1848036 := by
    simpa [prefixWord, tailWord_1848036, baseEnd_1848036] using wordTrace_append hprefix tailTrace_1848036
  have hstable : (prefixWord ++ tailWord_1848036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848036).length < 2 ^ (prefixWord ++ tailWord_1848036).sum := by decide
  have hdescent : baseEnd_1848036 < baseStart_1848036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848066 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1848066 : Nat := 118140960795 + 1848066 * 2 ^ 59
def prefixEnd_1848066 : Nat := 4983230072969 + 3 ^ 40 * 1848066 * 2
def baseEnd_1848066 : Nat := 210876919829349259327979

theorem tailTrace_1848066 : CollatzResearch.WordTrace tailWord_1848066 prefixEnd_1848066 210876919829349259327979 := by
  unfold tailWord_1848066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16851126130694995347439013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44936336348519987593170701 16851126130694995347439013)
  ·
    refine ⟨3159586149505311627644815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16851126130694995347439013 3159586149505311627644815)
    ·
      refine ⟨4739379224257967441467223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159586149505311627644815 4739379224257967441467223)
      ·
        refine ⟨7109068836386951162200835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739379224257967441467223 7109068836386951162200835)
        ·
          refine ⟨10663603254580426743301253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7109068836386951162200835 10663603254580426743301253)
          ·
            refine ⟨1999425610233830014368985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10663603254580426743301253 1999425610233830014368985)
            ·
              refine ⟨1499569207675372510776739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999425610233830014368985 1499569207675372510776739)
              ·
                refine ⟨2249353811513058766165109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499569207675372510776739 2249353811513058766165109)
                ·
                  refine ⟨210876919829349259327979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2249353811513058766165109 210876919829349259327979)
                  ·
                    rfl

theorem cell22_1848066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1848066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848066 prefixEnd_1848066 := by exact prefixLift 1848066
  have htrace : WordTrace (prefixWord ++ tailWord_1848066) baseStart_1848066 baseEnd_1848066 := by
    simpa [prefixWord, tailWord_1848066, baseEnd_1848066] using wordTrace_append hprefix tailTrace_1848066
  have hstable : (prefixWord ++ tailWord_1848066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848066).length < 2 ^ (prefixWord ++ tailWord_1848066).sum := by decide
  have hdescent : baseEnd_1848066 < baseStart_1848066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848075 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 1, 5]
def baseStart_1848075 : Nat := 118140960795 + 1848075 * 2 ^ 59
def prefixEnd_1848075 : Nat := 4983230072969 + 3 ^ 40 * 1848075 * 2
def baseEnd_1848075 : Nat := 632633840371974754508909

theorem tailTrace_1848075 : CollatzResearch.WordTrace tailWord_1848075 prefixEnd_1848075 632633840371974754508909 := by
  unfold tailWord_1848075
  simp only [CollatzResearch.WordTrace]
  refine ⟨67404832779747375926833679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44936555186498250617889119 67404832779747375926833679)
  ·
    refine ⟨101107249169621063890250519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67404832779747375926833679 101107249169621063890250519)
    ·
      refine ⟨151660873754431595835375779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101107249169621063890250519 151660873754431595835375779)
      ·
        refine ⟨227491310631647393753063669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151660873754431595835375779 227491310631647393753063669)
        ·
          refine ⟨21327310371716943164349719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227491310631647393753063669 21327310371716943164349719)
          ·
            refine ⟨31990965557575414746524579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21327310371716943164349719 31990965557575414746524579)
            ·
              refine ⟨47986448336363122119786869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31990965557575414746524579 47986448336363122119786869)
              ·
                refine ⟨4498729531534042698730019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47986448336363122119786869 4498729531534042698730019)
                ·
                  refine ⟨6748094297301064048095029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498729531534042698730019 6748094297301064048095029)
                  ·
                    refine ⟨632633840371974754508909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6748094297301064048095029 632633840371974754508909)
                    ·
                      rfl

theorem cell22_1848075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_1848075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848075 prefixEnd_1848075 := by exact prefixLift 1848075
  have htrace : WordTrace (prefixWord ++ tailWord_1848075) baseStart_1848075 baseEnd_1848075 := by
    simpa [prefixWord, tailWord_1848075, baseEnd_1848075] using wordTrace_append hprefix tailTrace_1848075
  have hstable : (prefixWord ++ tailWord_1848075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848075).length < 2 ^ (prefixWord ++ tailWord_1848075).sum := by decide
  have hdescent : baseEnd_1848075 < baseStart_1848075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848092 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1848092 : Nat := 118140960795 + 1848092 * 2 ^ 59
def prefixEnd_1848092 : Nat := 4983230072969 + 3 ^ 40 * 1848092 * 2
def baseEnd_1848092 : Nat := 632639659819392376833857

theorem tailTrace_1848092 : CollatzResearch.WordTrace tailWord_1848092 prefixEnd_1848092 632639659819392376833857 := by
  unfold tailWord_1848092
  simp only [CollatzResearch.WordTrace]
  refine ⟨33702726410342893915101265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44936968547123858553468353 33702726410342893915101265)
  ·
    refine ⟨25277044807757170436325949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33702726410342893915101265 25277044807757170436325949)
    ·
      refine ⟨9478891802908938913622231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25277044807757170436325949 9478891802908938913622231)
      ·
        refine ⟨14218337704363408370433347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9478891802908938913622231 14218337704363408370433347)
        ·
          refine ⟨21327506556545112555650021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14218337704363408370433347 21327506556545112555650021)
          ·
            refine ⟨3998907479352208604184379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21327506556545112555650021 3998907479352208604184379)
            ·
              refine ⟨5998361219028312906276569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998907479352208604184379 5998361219028312906276569)
              ·
                refine ⟨4498770914271234679707427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5998361219028312906276569 4498770914271234679707427)
                ·
                  refine ⟨6748156371406852019561141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498770914271234679707427 6748156371406852019561141)
                  ·
                    refine ⟨632639659819392376833857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6748156371406852019561141 632639659819392376833857)
                    ·
                      rfl

theorem cell22_1848092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1848092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848092 prefixEnd_1848092 := by exact prefixLift 1848092
  have htrace : WordTrace (prefixWord ++ tailWord_1848092) baseStart_1848092 baseEnd_1848092 := by
    simpa [prefixWord, tailWord_1848092, baseEnd_1848092] using wordTrace_append hprefix tailTrace_1848092
  have hstable : (prefixWord ++ tailWord_1848092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848092).length < 2 ^ (prefixWord ++ tailWord_1848092).sum := by decide
  have hdescent : baseEnd_1848092 < baseStart_1848092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848135 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1848135 : Nat := 118140960795 + 1848135 * 2 ^ 59
def prefixEnd_1848135 : Nat := 4983230072969 + 3 ^ 40 * 1848135 * 2
def baseEnd_1848135 : Nat := 632654379598154598008725

theorem tailTrace_1848135 : CollatzResearch.WordTrace tailWord_1848135 prefixEnd_1848135 632654379598154598008725 := by
  unfold tailWord_1848135
  simp only [CollatzResearch.WordTrace]
  refine ⟨67407021159530006174017859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44938014106353337449345239 67407021159530006174017859)
  ·
    refine ⟨101110531739295009261026789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67407021159530006174017859 101110531739295009261026789)
    ·
      refine ⟨18958224701117814236442523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101110531739295009261026789 18958224701117814236442523)
      ·
        refine ⟨28437337051676721354663785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18958224701117814236442523 28437337051676721354663785)
        ·
          refine ⟨21328002788757541015997839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28437337051676721354663785 21328002788757541015997839)
          ·
            refine ⟨31992004183136311523996759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21328002788757541015997839 31992004183136311523996759)
            ·
              refine ⟨47988006274704467285995139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31992004183136311523996759 47988006274704467285995139)
              ·
                refine ⟨71982009412056700928992709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47988006274704467285995139 71982009412056700928992709)
                ·
                  refine ⟨13496626764760631424186133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71982009412056700928992709 13496626764760631424186133)
                  ·
                    refine ⟨632654379598154598008725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13496626764760631424186133 632654379598154598008725)
                    ·
                      rfl

theorem cell22_1848135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1848135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848135 prefixEnd_1848135 := by exact prefixLift 1848135
  have htrace : WordTrace (prefixWord ++ tailWord_1848135) baseStart_1848135 baseEnd_1848135 := by
    simpa [prefixWord, tailWord_1848135, baseEnd_1848135] using wordTrace_append hprefix tailTrace_1848135
  have hstable : (prefixWord ++ tailWord_1848135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848135).length < 2 ^ (prefixWord ++ tailWord_1848135).sum := by decide
  have hdescent : baseEnd_1848135 < baseStart_1848135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848137 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_1848137 : Nat := 118140960795 + 1848137 * 2 ^ 59
def prefixEnd_1848137 : Nat := 4983230072969 + 3 ^ 40 * 1848137 * 2
def baseEnd_1848137 : Nat := 632655064239027259458719

theorem tailTrace_1848137 : CollatzResearch.WordTrace tailWord_1848137 prefixEnd_1848137 632655064239027259458719 := by
  unfold tailWord_1848137
  simp only [CollatzResearch.WordTrace]
  refine ⟨67407094105522760515590665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44938062737015173677060443 67407094105522760515590665)
  ·
    refine ⟨50555320579142070386692999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67407094105522760515590665 50555320579142070386692999)
    ·
      refine ⟨75832980868713105580039499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50555320579142070386692999 75832980868713105580039499)
      ·
        refine ⟨113749471303069658370059249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75832980868713105580039499 113749471303069658370059249)
        ·
          refine ⟨85312103477302243777544437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113749471303069658370059249 85312103477302243777544437)
          ·
            refine ⟨7998009700997085354144791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85312103477302243777544437 7998009700997085354144791)
            ·
              refine ⟨11997014551495628031217187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998009700997085354144791 11997014551495628031217187)
              ·
                refine ⟨17995521827243442046825781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997014551495628031217187 17995521827243442046825781)
                ·
                  refine ⟨1687080171304072691889917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17995521827243442046825781 1687080171304072691889917)
                  ·
                    refine ⟨632655064239027259458719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687080171304072691889917 632655064239027259458719)
                    ·
                      rfl

theorem cell22_1848137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_1848137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848137 prefixEnd_1848137 := by exact prefixLift 1848137
  have htrace : WordTrace (prefixWord ++ tailWord_1848137) baseStart_1848137 baseEnd_1848137 := by
    simpa [prefixWord, tailWord_1848137, baseEnd_1848137] using wordTrace_append hprefix tailTrace_1848137
  have hstable : (prefixWord ++ tailWord_1848137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848137).length < 2 ^ (prefixWord ++ tailWord_1848137).sum := by decide
  have hdescent : baseEnd_1848137 < baseStart_1848137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848167 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 7]
def baseStart_1848167 : Nat := 118140960795 + 1848167 * 2 ^ 59
def prefixEnd_1848167 : Nat := 4983230072969 + 3 ^ 40 * 1848167 * 2
def baseEnd_1848167 : Nat := 210888444617372393736209

theorem tailTrace_1848167 : CollatzResearch.WordTrace tailWord_1848167 prefixEnd_1848167 210888444617372393736209 := by
  unfold tailWord_1848167
  simp only [CollatzResearch.WordTrace]
  refine ⟨67408188295414075639182755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44938792196942717092788503 67408188295414075639182755)
  ·
    refine ⟨101112282443121113458774133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67408188295414075639182755 101112282443121113458774133)
    ·
      refine ⟨9479276479042604386760075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101112282443121113458774133 9479276479042604386760075)
      ·
        refine ⟨14218914718563906580140113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479276479042604386760075 14218914718563906580140113)
        ·
          refine ⟨10664186038922929935105085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14218914718563906580140113 10664186038922929935105085)
          ·
            refine ⟨3999069764596098725664407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10664186038922929935105085 3999069764596098725664407)
            ·
              refine ⟨5998604646894148088496611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999069764596098725664407 5998604646894148088496611)
              ·
                refine ⟨8997906970341222132744917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998604646894148088496611 8997906970341222132744917)
                ·
                  refine ⟨210888444617372393736209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8997906970341222132744917 210888444617372393736209)
                  ·
                    rfl

theorem cell22_1848167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 7].length) (baseStart_1848167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848167 prefixEnd_1848167 := by exact prefixLift 1848167
  have htrace : WordTrace (prefixWord ++ tailWord_1848167) baseStart_1848167 baseEnd_1848167 := by
    simpa [prefixWord, tailWord_1848167, baseEnd_1848167] using wordTrace_append hprefix tailTrace_1848167
  have hstable : (prefixWord ++ tailWord_1848167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848167).length < 2 ^ (prefixWord ++ tailWord_1848167).sum := by decide
  have hdescent : baseEnd_1848167 < baseStart_1848167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848278 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1848278 : Nat := 118140960795 + 1848278 * 2 ^ 59
def prefixEnd_1848278 : Nat := 4983230072969 + 3 ^ 40 * 1848278 * 2
def baseEnd_1848278 : Nat := 632703331420549891683287

theorem tailTrace_1848278 : CollatzResearch.WordTrace tailWord_1848278 prefixEnd_1848278 632703331420549891683287 := by
  unfold tailWord_1848278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213264799875746349779593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44941491198674627730982325 4213264799875746349779593)
  ·
    refine ⟨3159948599906809762334695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4213264799875746349779593 3159948599906809762334695)
    ·
      refine ⟨4739922899860214643502043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159948599906809762334695 4739922899860214643502043)
      ·
        refine ⟨7109884349790321965253065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739922899860214643502043 7109884349790321965253065)
        ·
          refine ⟨5332413262342741473939799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7109884349790321965253065 5332413262342741473939799)
          ·
            refine ⟨7998619893514112210909699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332413262342741473939799 7998619893514112210909699)
            ·
              refine ⟨11997929840271168316364549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998619893514112210909699 11997929840271168316364549)
              ·
                refine ⟨2249611845050844059318353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11997929840271168316364549 2249611845050844059318353)
                ·
                  refine ⟨1687208883788133044488765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249611845050844059318353 1687208883788133044488765)
                  ·
                    refine ⟨632703331420549891683287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687208883788133044488765 632703331420549891683287)
                    ·
                      rfl

theorem cell22_1848278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1848278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848278 prefixEnd_1848278 := by exact prefixLift 1848278
  have htrace : WordTrace (prefixWord ++ tailWord_1848278) baseStart_1848278 baseEnd_1848278 := by
    simpa [prefixWord, tailWord_1848278, baseEnd_1848278] using wordTrace_append hprefix tailTrace_1848278
  have hstable : (prefixWord ++ tailWord_1848278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848278).length < 2 ^ (prefixWord ++ tailWord_1848278).sum := by decide
  have hdescent : baseEnd_1848278 < baseStart_1848278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848289 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_1848289 : Nat := 118140960795 + 1848289 * 2 ^ 59
def prefixEnd_1848289 : Nat := 4983230072969 + 3 ^ 40 * 1848289 * 2
def baseEnd_1848289 : Nat := 632707096945349529658253

theorem tailTrace_1848289 : CollatzResearch.WordTrace tailWord_1848289 prefixEnd_1848289 632707096945349529658253 := by
  unfold tailWord_1848289
  simp only [CollatzResearch.WordTrace]
  refine ⟨67412638000972090475123921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44941758667314726983415947 67412638000972090475123921)
  ·
    refine ⟨50559478500729067856342941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67412638000972090475123921 50559478500729067856342941)
    ·
      refine ⟨18959804437773400446128603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50559478500729067856342941 18959804437773400446128603)
      ·
        refine ⟨28439706656660100669192905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18959804437773400446128603 28439706656660100669192905)
        ·
          refine ⟨21329779992495075501894679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28439706656660100669192905 21329779992495075501894679)
          ·
            refine ⟨31994669988742613252842019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21329779992495075501894679 31994669988742613252842019)
            ·
              refine ⟨47992004983113919879263029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31994669988742613252842019 47992004983113919879263029)
              ·
                refine ⟨4499250467166929988680909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47992004983113919879263029 4499250467166929988680909)
                ·
                  refine ⟨1687218925187598745755341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4499250467166929988680909 1687218925187598745755341)
                  ·
                    refine ⟨632707096945349529658253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687218925187598745755341 632707096945349529658253)
                    ·
                      rfl

theorem cell22_1848289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_1848289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848289 prefixEnd_1848289 := by exact prefixLift 1848289
  have htrace : WordTrace (prefixWord ++ tailWord_1848289) baseStart_1848289 baseEnd_1848289 := by
    simpa [prefixWord, tailWord_1848289, baseEnd_1848289] using wordTrace_append hprefix tailTrace_1848289
  have hstable : (prefixWord ++ tailWord_1848289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848289).length < 2 ^ (prefixWord ++ tailWord_1848289).sum := by decide
  have hdescent : baseEnd_1848289 < baseStart_1848289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848317 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1848317 : Nat := 118140960795 + 1848317 * 2 ^ 59
def prefixEnd_1848317 : Nat := 4983230072969 + 3 ^ 40 * 1848317 * 2
def baseEnd_1848317 : Nat := 632716681917566789958167

theorem tailTrace_1848317 : CollatzResearch.WordTrace tailWord_1848317 prefixEnd_1848317 632716681917566789958167 := by
  unfold tailWord_1848317
  simp only [CollatzResearch.WordTrace]
  refine ⟨67413659244870651257143205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44942439496580434171428803 67413659244870651257143205)
  ·
    refine ⟨12640061108413247110714351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67413659244870651257143205 12640061108413247110714351)
    ·
      refine ⟨18960091662619870666071527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12640061108413247110714351 18960091662619870666071527)
      ·
        refine ⟨28440137493929805999107291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18960091662619870666071527 28440137493929805999107291)
        ·
          refine ⟨42660206240894708998660937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28440137493929805999107291 42660206240894708998660937)
          ·
            refine ⟨31995154680671031748995703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42660206240894708998660937 31995154680671031748995703)
            ·
              refine ⟨47992732021006547623493555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31995154680671031748995703 47992732021006547623493555)
              ·
                refine ⟨71989098031509821435240333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47992732021006547623493555 71989098031509821435240333)
                ·
                  refine ⟨26995911761816183038215125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71989098031509821435240333 26995911761816183038215125)
                  ·
                    refine ⟨632716681917566789958167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26995911761816183038215125 632716681917566789958167)
                    ·
                      rfl

theorem cell22_1848317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1848317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848317 prefixEnd_1848317 := by exact prefixLift 1848317
  have htrace : WordTrace (prefixWord ++ tailWord_1848317) baseStart_1848317 baseEnd_1848317 := by
    simpa [prefixWord, tailWord_1848317, baseEnd_1848317] using wordTrace_append hprefix tailTrace_1848317
  have hstable : (prefixWord ++ tailWord_1848317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848317).length < 2 ^ (prefixWord ++ tailWord_1848317).sum := by decide
  have hdescent : baseEnd_1848317 < baseStart_1848317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848334 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1848334 : Nat := 118140960795 + 1848334 * 2 ^ 59
def prefixEnd_1848334 : Nat := 4983230072969 + 3 ^ 40 * 1848334 * 2
def baseEnd_1848334 : Nat := 632722501364984412283115

theorem tailTrace_1848334 : CollatzResearch.WordTrace tailWord_1848334 prefixEnd_1848334 632722501364984412283115 := by
  unfold tailWord_1848334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426784910726132895064007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44942852857206042107008037 8426784910726132895064007)
  ·
    refine ⟨12640177366089199342596011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8426784910726132895064007 12640177366089199342596011)
    ·
      refine ⟨18960266049133799013894017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12640177366089199342596011 18960266049133799013894017)
      ·
        refine ⟨14220199536850349260420513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18960266049133799013894017 14220199536850349260420513)
        ·
          refine ⟨10665149652637761945315385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14220199536850349260420513 10665149652637761945315385)
          ·
            refine ⟨7998862239478321458986539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10665149652637761945315385 7998862239478321458986539)
            ·
              refine ⟨11998293359217482188479809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998862239478321458986539 11998293359217482188479809)
              ·
                refine ⟨8998720019413111641359857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11998293359217482188479809 8998720019413111641359857)
                ·
                  refine ⟨6749040014559833731019893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998720019413111641359857 6749040014559833731019893)
                  ·
                    refine ⟨632722501364984412283115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6749040014559833731019893 632722501364984412283115)
                    ·
                      rfl

theorem cell22_1848334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1848334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848334 prefixEnd_1848334 := by exact prefixLift 1848334
  have htrace : WordTrace (prefixWord ++ tailWord_1848334) baseStart_1848334 baseEnd_1848334 := by
    simpa [prefixWord, tailWord_1848334, baseEnd_1848334] using wordTrace_append hprefix tailTrace_1848334
  have hstable : (prefixWord ++ tailWord_1848334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848334).length < 2 ^ (prefixWord ++ tailWord_1848334).sum := by decide
  have hdescent : baseEnd_1848334 < baseStart_1848334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848394 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1848394 : Nat := 118140960795 + 1848394 * 2 ^ 59
def prefixEnd_1848394 : Nat := 4983230072969 + 3 ^ 40 * 1848394 * 2
def baseEnd_1848394 : Nat := 632743040591164255782931

theorem tailTrace_1848394 : CollatzResearch.WordTrace tailWord_1848394 prefixEnd_1848394 632743040591164255782931 := by
  unfold tailWord_1848394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16854116916397923351924059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44944311777061128938464157 16854116916397923351924059)
  ·
    refine ⟨25281175374596885027886089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16854116916397923351924059 25281175374596885027886089)
    ·
      refine ⟨18960881530947663770914567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25281175374596885027886089 18960881530947663770914567)
      ·
        refine ⟨28441322296421495656371851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18960881530947663770914567 28441322296421495656371851)
        ·
          refine ⟨42661983444632243484557777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28441322296421495656371851 42661983444632243484557777)
          ·
            refine ⟨31996487583474182613418333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42661983444632243484557777 31996487583474182613418333)
            ·
              refine ⟨11998682843802818480031875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31996487583474182613418333 11998682843802818480031875)
              ·
                refine ⟨17998024265704227720047813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11998682843802818480031875 17998024265704227720047813)
                ·
                  refine ⟨3374629549819542697508965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17998024265704227720047813 3374629549819542697508965)
                  ·
                    refine ⟨632743040591164255782931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3374629549819542697508965 632743040591164255782931)
                    ·
                      rfl

theorem cell22_1848394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1848394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848394 prefixEnd_1848394 := by exact prefixLift 1848394
  have htrace : WordTrace (prefixWord ++ tailWord_1848394) baseStart_1848394 baseEnd_1848394 := by
    simpa [prefixWord, tailWord_1848394, baseEnd_1848394] using wordTrace_append hprefix tailTrace_1848394
  have hstable : (prefixWord ++ tailWord_1848394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848394).length < 2 ^ (prefixWord ++ tailWord_1848394).sum := by decide
  have hdescent : baseEnd_1848394 < baseStart_1848394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848396 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_1848396 : Nat := 118140960795 + 1848396 * 2 ^ 59
def prefixEnd_1848396 : Nat := 4983230072969 + 3 ^ 40 * 1848396 * 2
def baseEnd_1848396 : Nat := 632743725232036917232925

theorem tailTrace_1848396 : CollatzResearch.WordTrace tailWord_1848396 prefixEnd_1848396 632743725232036917232925 := by
  unfold tailWord_1848396
  simp only [CollatzResearch.WordTrace]
  refine ⟨33708270305792223874634521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44944360407722965166179361 33708270305792223874634521)
  ·
    refine ⟨25281202729344167905975891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33708270305792223874634521 25281202729344167905975891)
    ·
      refine ⟨37921804094016251858963837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25281202729344167905975891 37921804094016251858963837)
      ·
        refine ⟨14220676535256094447111439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37921804094016251858963837 14220676535256094447111439)
        ·
          refine ⟨21331014802884141670667159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14220676535256094447111439 21331014802884141670667159)
          ·
            refine ⟨31996522204326212506000739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21331014802884141670667159 31996522204326212506000739)
            ·
              refine ⟨47994783306489318759001109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31996522204326212506000739 47994783306489318759001109)
              ·
                refine ⟨2249755467491686816828177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47994783306489318759001109 2249755467491686816828177)
                ·
                  refine ⟨1687316600618765112621133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249755467491686816828177 1687316600618765112621133)
                  ·
                    refine ⟨632743725232036917232925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687316600618765112621133 632743725232036917232925)
                    ·
                      rfl

theorem cell22_1848396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_1848396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848396 prefixEnd_1848396 := by exact prefixLift 1848396
  have htrace : WordTrace (prefixWord ++ tailWord_1848396) baseStart_1848396 baseEnd_1848396 := by
    simpa [prefixWord, tailWord_1848396, baseEnd_1848396] using wordTrace_append hprefix tailTrace_1848396
  have hstable : (prefixWord ++ tailWord_1848396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848396).length < 2 ^ (prefixWord ++ tailWord_1848396).sum := by decide
  have hdescent : baseEnd_1848396 < baseStart_1848396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848398 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_1848398 : Nat := 118140960795 + 1848398 * 2 ^ 59
def prefixEnd_1848398 : Nat := 4983230072969 + 3 ^ 40 * 1848398 * 2
def baseEnd_1848398 : Nat := 210914803290969859560973

theorem tailTrace_1848398 : CollatzResearch.WordTrace tailWord_1848398 prefixEnd_1848398 210914803290969859560973 := by
  unfold tailWord_1848398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427076694697150261355231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44944409038384801393894565 8427076694697150261355231)
  ·
    refine ⟨12640615042045725392032847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8427076694697150261355231 12640615042045725392032847)
    ·
      refine ⟨18960922563068588088049271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12640615042045725392032847 18960922563068588088049271)
      ·
        refine ⟨28441383844602882132073907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18960922563068588088049271 28441383844602882132073907)
        ·
          refine ⟨42662075766904323198110861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28441383844602882132073907 42662075766904323198110861)
          ·
            refine ⟨15998278412589121199291573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42662075766904323198110861 15998278412589121199291573)
            ·
              refine ⟨1499838601180230112433585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15998278412589121199291573 1499838601180230112433585)
              ·
                refine ⟨1124878950885172584325189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499838601180230112433585 1124878950885172584325189)
                ·
                  refine ⟨210914803290969859560973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1124878950885172584325189 210914803290969859560973)
                  ·
                    rfl

theorem cell22_1848398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_1848398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848398 prefixEnd_1848398 := by exact prefixLift 1848398
  have htrace : WordTrace (prefixWord ++ tailWord_1848398) baseStart_1848398 baseEnd_1848398 := by
    simpa [prefixWord, tailWord_1848398, baseEnd_1848398] using wordTrace_append hprefix tailTrace_1848398
  have hstable : (prefixWord ++ tailWord_1848398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848398).length < 2 ^ (prefixWord ++ tailWord_1848398).sum := by decide
  have hdescent : baseEnd_1848398 < baseStart_1848398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848471 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 5]
def baseStart_1848471 : Nat := 118140960795 + 1848471 * 2 ^ 59
def prefixEnd_1848471 : Nat := 4983230072969 + 3 ^ 40 * 1848471 * 2
def baseEnd_1848471 : Nat := 210923133088253907202565

theorem tailTrace_1848471 : CollatzResearch.WordTrace tailWord_1848471 prefixEnd_1848471 210923133088253907202565 := by
  unfold tailWord_1848471
  simp only [CollatzResearch.WordTrace]
  refine ⟨67419276086312735558249267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44946184057541823705499511 67419276086312735558249267)
  ·
    refine ⟨101128914129469103337373901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67419276086312735558249267 101128914129469103337373901)
    ·
      refine ⟨37923342798550913751515213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101128914129469103337373901 37923342798550913751515213)
      ·
        refine ⟨14221253549456592656818205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37923342798550913751515213 14221253549456592656818205)
        ·
          refine ⟨5332970081046222246306827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14221253549456592656818205 5332970081046222246306827)
          ·
            refine ⟨7999455121569333369460241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332970081046222246306827 7999455121569333369460241)
            ·
              refine ⟨5999591341177000027095181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7999455121569333369460241 5999591341177000027095181)
              ·
                refine ⟨2249846752941375010160693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5999591341177000027095181 2249846752941375010160693)
                ·
                  refine ⟨210923133088253907202565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2249846752941375010160693 210923133088253907202565)
                  ·
                    rfl

theorem cell22_1848471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 5].length) (baseStart_1848471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848471 prefixEnd_1848471 := by exact prefixLift 1848471
  have htrace : WordTrace (prefixWord ++ tailWord_1848471) baseStart_1848471 baseEnd_1848471 := by
    simpa [prefixWord, tailWord_1848471, baseEnd_1848471] using wordTrace_append hprefix tailTrace_1848471
  have hstable : (prefixWord ++ tailWord_1848471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848471).length < 2 ^ (prefixWord ++ tailWord_1848471).sum := by decide
  have hdescent : baseEnd_1848471 < baseStart_1848471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848627 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 1, 3]
def baseStart_1848627 : Nat := 118140960795 + 1848627 * 2 ^ 59
def prefixEnd_1848627 : Nat := 4983230072969 + 3 ^ 40 * 1848627 * 2
def baseEnd_1848627 : Nat := 632822801252829314707217

theorem tailTrace_1848627 : CollatzResearch.WordTrace tailWord_1848627 prefixEnd_1848627 632822801252829314707217 := by
  unfold tailWord_1848627
  simp only [CollatzResearch.WordTrace]
  refine ⟨67424965873747574200928135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44949977249165049467285423 67424965873747574200928135)
  ·
    refine ⟨101137448810621361301392203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67424965873747574200928135 101137448810621361301392203)
    ·
      refine ⟨151706173215932041952088305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101137448810621361301392203 151706173215932041952088305)
      ·
        refine ⟨113779629911949031464066229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151706173215932041952088305 113779629911949031464066229)
        ·
          refine ⟨10666840304245221699756209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113779629911949031464066229 10666840304245221699756209)
          ·
            refine ⟨8000130228183916274817157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10666840304245221699756209 8000130228183916274817157)
            ·
              refine ⟨1500024417784484301528217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8000130228183916274817157 1500024417784484301528217)
              ·
                refine ⟨1125018313338363226146163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500024417784484301528217 1125018313338363226146163)
                ·
                  refine ⟨1687527470007544839219245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125018313338363226146163 1687527470007544839219245)
                  ·
                    refine ⟨632822801252829314707217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687527470007544839219245 632822801252829314707217)
                    ·
                      rfl

theorem cell22_1848627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 3].length) (baseStart_1848627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848627 prefixEnd_1848627 := by exact prefixLift 1848627
  have htrace : WordTrace (prefixWord ++ tailWord_1848627) baseStart_1848627 baseEnd_1848627 := by
    simpa [prefixWord, tailWord_1848627, baseEnd_1848627] using wordTrace_append hprefix tailTrace_1848627
  have hstable : (prefixWord ++ tailWord_1848627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848627).length < 2 ^ (prefixWord ++ tailWord_1848627).sum := by decide
  have hdescent : baseEnd_1848627 < baseStart_1848627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848638 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1848638 : Nat := 118140960795 + 1848638 * 2 ^ 59
def prefixEnd_1848638 : Nat := 4983230072969 + 3 ^ 40 * 1848638 * 2
def baseEnd_1848638 : Nat := 632826566777628952682183

theorem tailTrace_1848638 : CollatzResearch.WordTrace tailWord_1848638 prefixEnd_1848638 632826566777628952682183 := by
  unfold tailWord_1848638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428170884588465384947321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44950244717805148719719045 8428170884588465384947321)
  ·
    refine ⟨6321128163441349038710491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8428170884588465384947321 6321128163441349038710491)
    ·
      refine ⟨9481692245162023558065737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321128163441349038710491 9481692245162023558065737)
      ·
        refine ⟨7111269183871517668549303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9481692245162023558065737 7111269183871517668549303)
        ·
          refine ⟨10666903775807276502823955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111269183871517668549303 10666903775807276502823955)
          ·
            refine ⟨16000355663710914754235933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10666903775807276502823955 16000355663710914754235933)
            ·
              refine ⟨6000133373891593032838475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16000355663710914754235933 6000133373891593032838475)
              ·
                refine ⟨9000200060837389549257713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000133373891593032838475 9000200060837389549257713)
                ·
                  refine ⟨6750150045628042161943285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000200060837389549257713 6750150045628042161943285)
                  ·
                    refine ⟨632826566777628952682183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6750150045628042161943285 632826566777628952682183)
                    ·
                      rfl

theorem cell22_1848638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1848638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848638 prefixEnd_1848638 := by exact prefixLift 1848638
  have htrace : WordTrace (prefixWord ++ tailWord_1848638) baseStart_1848638 baseEnd_1848638 := by
    simpa [prefixWord, tailWord_1848638, baseEnd_1848638] using wordTrace_append hprefix tailTrace_1848638
  have hstable : (prefixWord ++ tailWord_1848638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848638).length < 2 ^ (prefixWord ++ tailWord_1848638).sum := by decide
  have hdescent : baseEnd_1848638 < baseStart_1848638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848685 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1848685 : Nat := 118140960795 + 1848685 * 2 ^ 59
def prefixEnd_1848685 : Nat := 4983230072969 + 3 ^ 40 * 1848685 * 2
def baseEnd_1848685 : Nat := 210947551946045498919013

theorem tailTrace_1848685 : CollatzResearch.WordTrace tailWord_1848685 prefixEnd_1848685 210947551946045498919013 := by
  unfold tailWord_1848685
  simp only [CollatzResearch.WordTrace]
  refine ⟨67427081307537450106539509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44951387538358300071026339 67427081307537450106539509)
  ·
    refine ⟨6321288872581635947488079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67427081307537450106539509 6321288872581635947488079)
    ·
      refine ⟨9481933308872453921232119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321288872581635947488079 9481933308872453921232119)
      ·
        refine ⟨14222899963308680881848179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9481933308872453921232119 14222899963308680881848179)
        ·
          refine ⟨21334349944963021322772269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14222899963308680881848179 21334349944963021322772269)
          ·
            refine ⟨8000381229361132996039601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21334349944963021322772269 8000381229361132996039601)
            ·
              refine ⟨6000285922020849747029701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8000381229361132996039601 6000285922020849747029701)
              ·
                refine ⟨1125053610378909327568069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6000285922020849747029701 1125053610378909327568069)
                ·
                  refine ⟨210947551946045498919013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125053610378909327568069 210947551946045498919013)
                  ·
                    rfl

theorem cell22_1848685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1848685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848685 prefixEnd_1848685 := by exact prefixLift 1848685
  have htrace : WordTrace (prefixWord ++ tailWord_1848685) baseStart_1848685 baseEnd_1848685 := by
    simpa [prefixWord, tailWord_1848685, baseEnd_1848685] using wordTrace_append hprefix tailTrace_1848685
  have hstable : (prefixWord ++ tailWord_1848685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848685).length < 2 ^ (prefixWord ++ tailWord_1848685).sum := by decide
  have hdescent : baseEnd_1848685 < baseStart_1848685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848713 : List Nat := [1, 2, 1, 1, 7, 1, 1, 8]
def baseStart_1848713 : Nat := 118140960795 + 1848713 * 2 ^ 59
def prefixEnd_1848713 : Nat := 4983230072969 + 3 ^ 40 * 1848713 * 2
def baseEnd_1848713 : Nat := 70316915645594861895217

theorem tailTrace_1848713 : CollatzResearch.WordTrace tailWord_1848713 prefixEnd_1848713 70316915645594861895217 := by
  unfold tailWord_1848713
  simp only [CollatzResearch.WordTrace]
  refine ⟨67428102551436010888558793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44952068367624007259039195 67428102551436010888558793)
  ·
    refine ⟨50571076913577008166419095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67428102551436010888558793 50571076913577008166419095)
    ·
      refine ⟨75856615370365512249628643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50571076913577008166419095 75856615370365512249628643)
      ·
        refine ⟨113784923055548268374442965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75856615370365512249628643 113784923055548268374442965)
        ·
          refine ⟨2666834134114412540026007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113784923055548268374442965 2666834134114412540026007)
          ·
            refine ⟨4000251201171618810039011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666834134114412540026007 4000251201171618810039011)
            ·
              refine ⟨6000376801757428215058517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000251201171618810039011 6000376801757428215058517)
              ·
                refine ⟨70316915645594861895217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6000376801757428215058517 70316915645594861895217)
                ·
                  rfl

theorem cell22_1848713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 8].length) (baseStart_1848713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848713 prefixEnd_1848713 := by exact prefixLift 1848713
  have htrace : WordTrace (prefixWord ++ tailWord_1848713) baseStart_1848713 baseEnd_1848713 := by
    simpa [prefixWord, tailWord_1848713, baseEnd_1848713] using wordTrace_append hprefix tailTrace_1848713
  have hstable : (prefixWord ++ tailWord_1848713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848713).length < 2 ^ (prefixWord ++ tailWord_1848713).sum := by decide
  have hdescent : baseEnd_1848713 < baseStart_1848713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848732 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1848732 : Nat := 118140960795 + 1848732 * 2 ^ 59
def prefixEnd_1848732 : Nat := 4983230072969 + 3 ^ 40 * 1848732 * 2
def baseEnd_1848732 : Nat := 632858744898644040831895

theorem tailTrace_1848732 : CollatzResearch.WordTrace tailWord_1848732 prefixEnd_1848732 632858744898644040831895 := by
  unfold tailWord_1848732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33714397769183588566750225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44952530358911451422333633 33714397769183588566750225)
  ·
    refine ⟨25285798326887691425062669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33714397769183588566750225 25285798326887691425062669)
    ·
      refine ⟨9482174372582884284398501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25285798326887691425062669 9482174372582884284398501)
      ·
        refine ⟨1777907694859290803324719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9482174372582884284398501 1777907694859290803324719)
        ·
          refine ⟨2666861542288936204987079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777907694859290803324719 2666861542288936204987079)
          ·
            refine ⟨4000292313433404307480619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666861542288936204987079 4000292313433404307480619)
            ·
              refine ⟨6000438470150106461220929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000292313433404307480619 6000438470150106461220929)
              ·
                refine ⟨4500328852612579845915697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6000438470150106461220929 4500328852612579845915697)
                ·
                  refine ⟨3375246639459434884436773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500328852612579845915697 3375246639459434884436773)
                  ·
                    refine ⟨632858744898644040831895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375246639459434884436773 632858744898644040831895)
                    ·
                      rfl

theorem cell22_1848732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1848732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848732 prefixEnd_1848732 := by exact prefixLift 1848732
  have htrace : WordTrace (prefixWord ++ tailWord_1848732) baseStart_1848732 baseEnd_1848732 := by
    simpa [prefixWord, tailWord_1848732, baseEnd_1848732] using wordTrace_append hprefix tailTrace_1848732
  have hstable : (prefixWord ++ tailWord_1848732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848732).length < 2 ^ (prefixWord ++ tailWord_1848732).sum := by decide
  have hdescent : baseEnd_1848732 < baseStart_1848732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848743 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1848743 : Nat := 118140960795 + 1848743 * 2 ^ 59
def prefixEnd_1848743 : Nat := 4983230072969 + 3 ^ 40 * 1848743 * 2
def baseEnd_1848743 : Nat := 632862510423443678806861

theorem tailTrace_1848743 : CollatzResearch.WordTrace tailWord_1848743 prefixEnd_1848743 632862510423443678806861 := by
  unfold tailWord_1848743
  simp only [CollatzResearch.WordTrace]
  refine ⟨67429196741327326012150883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44952797827551550674767255 67429196741327326012150883)
  ·
    refine ⟨101143795111990989018226325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67429196741327326012150883 101143795111990989018226325)
    ·
      refine ⟨4741115395874577610229359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101143795111990989018226325 4741115395874577610229359)
      ·
        refine ⟨7111673093811866415344039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741115395874577610229359 7111673093811866415344039)
        ·
          refine ⟨10667509640717799623016059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111673093811866415344039 10667509640717799623016059)
          ·
            refine ⟨16001264461076699434524089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10667509640717799623016059 16001264461076699434524089)
            ·
              refine ⟨12000948345807524575893067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16001264461076699434524089 12000948345807524575893067)
              ·
                refine ⟨18001422518711286863839601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000948345807524575893067 18001422518711286863839601)
                ·
                  refine ⟨13501066889033465147879701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18001422518711286863839601 13501066889033465147879701)
                  ·
                    refine ⟨632862510423443678806861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13501066889033465147879701 632862510423443678806861)
                    ·
                      rfl

theorem cell22_1848743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1848743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848743 prefixEnd_1848743 := by exact prefixLift 1848743
  have htrace : WordTrace (prefixWord ++ tailWord_1848743) baseStart_1848743 baseEnd_1848743 := by
    simpa [prefixWord, tailWord_1848743, baseEnd_1848743] using wordTrace_append hprefix tailTrace_1848743
  have hstable : (prefixWord ++ tailWord_1848743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848743).length < 2 ^ (prefixWord ++ tailWord_1848743).sum := by decide
  have hdescent : baseEnd_1848743 < baseStart_1848743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848805 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1848805 : Nat := 118140960795 + 1848805 * 2 ^ 59
def prefixEnd_1848805 : Nat := 4983230072969 + 3 ^ 40 * 1848805 * 2
def baseEnd_1848805 : Nat := 632883734290496183756671

theorem tailTrace_1848805 : CollatzResearch.WordTrace tailWord_1848805 prefixEnd_1848805 632883734290496183756671 := by
  unfold tailWord_1848805
  simp only [CollatzResearch.WordTrace]
  refine ⟨67431458067102710600907869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44954305378068473733938579 67431458067102710600907869)
  ·
    refine ⟨25286796775163516475340451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67431458067102710600907869 25286796775163516475340451)
    ·
      refine ⟨37930195162745274713010677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25286796775163516475340451 37930195162745274713010677)
      ·
        refine ⟨3555955796507369504344751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37930195162745274713010677 3555955796507369504344751)
        ·
          refine ⟨5333933694761054256517127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555955796507369504344751 5333933694761054256517127)
          ·
            refine ⟨8000900542141581384775691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333933694761054256517127 8000900542141581384775691)
            ·
              refine ⟨12001350813212372077163537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000900542141581384775691 12001350813212372077163537)
              ·
                refine ⟨9001013109909279057872653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12001350813212372077163537 9001013109909279057872653)
                ·
                  refine ⟨3375379916215979646702245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9001013109909279057872653 3375379916215979646702245)
                  ·
                    refine ⟨632883734290496183756671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375379916215979646702245 632883734290496183756671)
                    ·
                      rfl

theorem cell22_1848805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1848805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848805 prefixEnd_1848805 := by exact prefixLift 1848805
  have htrace : WordTrace (prefixWord ++ tailWord_1848805) baseStart_1848805 baseEnd_1848805 := by
    simpa [prefixWord, tailWord_1848805, baseEnd_1848805] using wordTrace_append hprefix tailTrace_1848805
  have hstable : (prefixWord ++ tailWord_1848805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848805).length < 2 ^ (prefixWord ++ tailWord_1848805).sum := by decide
  have hdescent : baseEnd_1848805 < baseStart_1848805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848839 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 1, 4]
def baseStart_1848839 : Nat := 118140960795 + 1848839 * 2 ^ 59
def prefixEnd_1848839 : Nat := 4983230072969 + 3 ^ 40 * 1848839 * 2
def baseEnd_1848839 : Nat := 632895373185331428406567

theorem tailTrace_1848839 : CollatzResearch.WordTrace tailWord_1848839 prefixEnd_1848839 632895373185331428406567 := by
  unfold tailWord_1848839
  simp only [CollatzResearch.WordTrace]
  refine ⟨67432698148979534407645571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44955132099319689605097047 67432698148979534407645571)
  ·
    refine ⟨101149047223469301611468357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67432698148979534407645571 101149047223469301611468357)
    ·
      refine ⟨18965446354400494052150317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101149047223469301611468357 18965446354400494052150317)
      ·
        refine ⟨7112042382900185269556369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18965446354400494052150317 7112042382900185269556369)
        ·
          refine ⟨5334031787175138952167277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112042382900185269556369 5334031787175138952167277)
          ·
            refine ⟨2000261920190677107062729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5334031787175138952167277 2000261920190677107062729)
            ·
              refine ⟨1500196440143007830297047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000261920190677107062729 1500196440143007830297047)
              ·
                refine ⟨2250294660214511745445571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500196440143007830297047 2250294660214511745445571)
                ·
                  refine ⟨3375441990321767618168357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250294660214511745445571 3375441990321767618168357)
                  ·
                    refine ⟨632895373185331428406567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375441990321767618168357 632895373185331428406567)
                    ·
                      rfl

theorem cell22_1848839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_1848839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848839 prefixEnd_1848839 := by exact prefixLift 1848839
  have htrace : WordTrace (prefixWord ++ tailWord_1848839) baseStart_1848839 baseEnd_1848839 := by
    simpa [prefixWord, tailWord_1848839, baseEnd_1848839] using wordTrace_append hprefix tailTrace_1848839
  have hstable : (prefixWord ++ tailWord_1848839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848839).length < 2 ^ (prefixWord ++ tailWord_1848839).sum := by decide
  have hdescent : baseEnd_1848839 < baseStart_1848839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848910 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_1848910 : Nat := 118140960795 + 1848910 * 2 ^ 59
def prefixEnd_1848910 : Nat := 4983230072969 + 3 ^ 40 * 1848910 * 2
def baseEnd_1848910 : Nat := 210973225978770303293783

theorem tailTrace_1848910 : CollatzResearch.WordTrace tailWord_1848910 prefixEnd_1848910 210973225978770303293783 := by
  unfold tailWord_1848910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429410966465289191685023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44956858487814875688986789 8429410966465289191685023)
  ·
    refine ⟨12644116449697933787527535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429410966465289191685023 12644116449697933787527535)
    ·
      refine ⟨18966174674546900681291303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12644116449697933787527535 18966174674546900681291303)
      ·
        refine ⟨28449262011820351021936955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18966174674546900681291303 28449262011820351021936955)
        ·
          refine ⟨42673893017730526532905433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28449262011820351021936955 42673893017730526532905433)
          ·
            refine ⟨32005419763297894899679075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42673893017730526532905433 32005419763297894899679075)
            ·
              refine ⟨48008129644946842349518613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32005419763297894899679075 48008129644946842349518613)
              ·
                refine ⟨2250381077106883235133685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48008129644946842349518613 2250381077106883235133685)
                ·
                  refine ⟨210973225978770303293783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2250381077106883235133685 210973225978770303293783)
                  ·
                    rfl

theorem cell22_1848910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_1848910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848910 prefixEnd_1848910 := by exact prefixLift 1848910
  have htrace : WordTrace (prefixWord ++ tailWord_1848910) baseStart_1848910 baseEnd_1848910 := by
    simpa [prefixWord, tailWord_1848910, baseEnd_1848910] using wordTrace_append hprefix tailTrace_1848910
  have hstable : (prefixWord ++ tailWord_1848910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848910).length < 2 ^ (prefixWord ++ tailWord_1848910).sum := by decide
  have hdescent : baseEnd_1848910 < baseStart_1848910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848914 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1848914 : Nat := 118140960795 + 1848914 * 2 ^ 59
def prefixEnd_1848914 : Nat := 4983230072969 + 3 ^ 40 * 1848914 * 2
def baseEnd_1848914 : Nat := 632921047218056232781337

theorem tailTrace_1848914 : CollatzResearch.WordTrace tailWord_1848914 prefixEnd_1848914 632921047218056232781337 := by
  unfold tailWord_1848914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16858858405926955554156449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44956955749138548144417197 16858858405926955554156449)
  ·
    refine ⟨12644143804445216665617337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16858858405926955554156449 12644143804445216665617337)
    ·
      refine ⟨9483107853333912499213003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12644143804445216665617337 9483107853333912499213003)
      ·
        refine ⟨14224661780000868748819505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9483107853333912499213003 14224661780000868748819505)
        ·
          refine ⟨10668496335000651561614629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14224661780000868748819505 10668496335000651561614629)
          ·
            refine ⟨2000343062812622167802743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10668496335000651561614629 2000343062812622167802743)
            ·
              refine ⟨3000514594218933251704115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000343062812622167802743 3000514594218933251704115)
              ·
                refine ⟨4500771891328399877556173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000514594218933251704115 4500771891328399877556173)
                ·
                  refine ⟨1687789459248149954083565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4500771891328399877556173 1687789459248149954083565)
                  ·
                    refine ⟨632921047218056232781337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687789459248149954083565 632921047218056232781337)
                    ·
                      rfl

theorem cell22_1848914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1848914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848914 prefixEnd_1848914 := by exact prefixLift 1848914
  have htrace : WordTrace (prefixWord ++ tailWord_1848914) baseStart_1848914 baseEnd_1848914 := by
    simpa [prefixWord, tailWord_1848914, baseEnd_1848914] using wordTrace_append hprefix tailTrace_1848914
  have hstable : (prefixWord ++ tailWord_1848914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848914).length < 2 ^ (prefixWord ++ tailWord_1848914).sum := by decide
  have hdescent : baseEnd_1848914 < baseStart_1848914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848972 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 4]
def baseStart_1848972 : Nat := 118140960795 + 1848972 * 2 ^ 59
def prefixEnd_1848972 : Nat := 4983230072969 + 3 ^ 40 * 1848972 * 2
def baseEnd_1848972 : Nat := 210980300601121138277053

theorem tailTrace_1848972 : CollatzResearch.WordTrace tailWord_1848972 prefixEnd_1848972 210980300601121138277053 := by
  unfold tailWord_1848972
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718774528748849061118585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44958366038331798748158113 33718774528748849061118585)
  ·
    refine ⟨25289080896561636795838939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33718774528748849061118585 25289080896561636795838939)
    ·
      refine ⟨37933621344842455193758409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25289080896561636795838939 37933621344842455193758409)
      ·
        refine ⟨28450216008631841395318807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37933621344842455193758409 28450216008631841395318807)
        ·
          refine ⟨42675324012947762092978211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28450216008631841395318807 42675324012947762092978211)
          ·
            refine ⟨64012986019421643139467317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42675324012947762092978211 64012986019421643139467317)
            ·
              refine ⟨6001217439320779044325061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64012986019421643139467317 6001217439320779044325061)
              ·
                refine ⟨1125228269872646070810949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6001217439320779044325061 1125228269872646070810949)
                ·
                  refine ⟨210980300601121138277053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125228269872646070810949 210980300601121138277053)
                  ·
                    rfl

theorem cell22_1848972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_1848972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1848972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1848972 prefixEnd_1848972 := by exact prefixLift 1848972
  have htrace : WordTrace (prefixWord ++ tailWord_1848972) baseStart_1848972 baseEnd_1848972 := by
    simpa [prefixWord, tailWord_1848972, baseEnd_1848972] using wordTrace_append hprefix tailTrace_1848972
  have hstable : (prefixWord ++ tailWord_1848972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848972).length < 2 ^ (prefixWord ++ tailWord_1848972).sum := by decide
  have hdescent : baseEnd_1848972 < baseStart_1848972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849066 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_1849066 : Nat := 118140960795 + 1849066 * 2 ^ 59
def prefixEnd_1849066 : Nat := 4983230072969 + 3 ^ 40 * 1849066 * 2
def baseEnd_1849066 : Nat := 632973079924378502980871

theorem tailTrace_1849066 : CollatzResearch.WordTrace tailWord_1849066 prefixEnd_1849066 632973079924378502980871 := by
  unfold tailWord_1849066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860244379789288044039763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44960651679438101450772701 16860244379789288044039763)
  ·
    refine ⟨25290366569683932066059645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16860244379789288044039763 25290366569683932066059645)
    ·
      refine ⟨9483887463631474524772367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25290366569683932066059645 9483887463631474524772367)
      ·
        refine ⟨14225831195447211787158551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9483887463631474524772367 14225831195447211787158551)
        ·
          refine ⟨21338746793170817680737827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225831195447211787158551 21338746793170817680737827)
          ·
            refine ⟨32008120189756226521106741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21338746793170817680737827 32008120189756226521106741)
            ·
              refine ⟨3000761267789646236353757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32008120189756226521106741 3000761267789646236353757)
              ·
                refine ⟨1125285475421117338632659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3000761267789646236353757 1125285475421117338632659)
                ·
                  refine ⟨1687928213131676007948989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125285475421117338632659 1687928213131676007948989)
                  ·
                    refine ⟨632973079924378502980871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687928213131676007948989 632973079924378502980871)
                    ·
                      rfl

theorem cell22_1849066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_1849066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849066 prefixEnd_1849066 := by exact prefixLift 1849066
  have htrace : WordTrace (prefixWord ++ tailWord_1849066) baseStart_1849066 baseEnd_1849066 := by
    simpa [prefixWord, tailWord_1849066, baseEnd_1849066] using wordTrace_append hprefix tailTrace_1849066
  have hstable : (prefixWord ++ tailWord_1849066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849066).length < 2 ^ (prefixWord ++ tailWord_1849066).sum := by decide
  have hdescent : baseEnd_1849066 < baseStart_1849066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849109 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1849109 : Nat := 118140960795 + 1849109 * 2 ^ 59
def prefixEnd_1849109 : Nat := 4983230072969 + 3 ^ 40 * 1849109 * 2
def baseEnd_1849109 : Nat := 632987799703140724155739

theorem tailTrace_1849109 : CollatzResearch.WordTrace tailWord_1849109 prefixEnd_1849109 632987799703140724155739 := by
  unfold tailWord_1849109
  simp only [CollatzResearch.WordTrace]
  refine ⟨67442545858001370519974381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44961697238667580346649587 67442545858001370519974381)
  ·
    refine ⟨25290954696750513944990393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67442545858001370519974381 25290954696750513944990393)
    ·
      refine ⟨18968216022562885458742795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25290954696750513944990393 18968216022562885458742795)
      ·
        refine ⟨28452324033844328188114193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18968216022562885458742795 28452324033844328188114193)
        ·
          refine ⟨21339243025383246141085645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28452324033844328188114193 21339243025383246141085645)
          ·
            refine ⟨8002216134518717302907117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21339243025383246141085645 8002216134518717302907117)
            ·
              refine ⟨3000831050444518988590169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8002216134518717302907117 3000831050444518988590169)
              ·
                refine ⟨2250623287833389241442627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000831050444518988590169 2250623287833389241442627)
                ·
                  refine ⟨3375934931750083862163941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250623287833389241442627 3375934931750083862163941)
                  ·
                    refine ⟨632987799703140724155739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375934931750083862163941 632987799703140724155739)
                    ·
                      rfl

theorem cell22_1849109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1849109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849109 prefixEnd_1849109 := by exact prefixLift 1849109
  have htrace : WordTrace (prefixWord ++ tailWord_1849109) baseStart_1849109 baseEnd_1849109 := by
    simpa [prefixWord, tailWord_1849109, baseEnd_1849109] using wordTrace_append hprefix tailTrace_1849109
  have hstable : (prefixWord ++ tailWord_1849109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849109).length < 2 ^ (prefixWord ++ tailWord_1849109).sum := by decide
  have hdescent : baseEnd_1849109 < baseStart_1849109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849141 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 4]
def baseStart_1849141 : Nat := 118140960795 + 1849141 * 2 ^ 59
def prefixEnd_1849141 : Nat := 4983230072969 + 3 ^ 40 * 1849141 * 2
def baseEnd_1849141 : Nat := 210999584652367769118547

theorem tailTrace_1849141 : CollatzResearch.WordTrace tailWord_1849141 prefixEnd_1849141 210999584652367769118547 := by
  unfold tailWord_1849141
  simp only [CollatzResearch.WordTrace]
  refine ⟨67443712993885439985139277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44962475329256959990092851 67443712993885439985139277)
  ·
    refine ⟨25291392372707039994427229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67443712993885439985139277 25291392372707039994427229)
    ·
      refine ⟨9484272139765139997910211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25291392372707039994427229 9484272139765139997910211)
      ·
        refine ⟨14226408209647709996865317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484272139765139997910211 14226408209647709996865317)
        ·
          refine ⟨2667451539308945624412247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14226408209647709996865317 2667451539308945624412247)
          ·
            refine ⟨4001177308963418436618371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667451539308945624412247 4001177308963418436618371)
            ·
              refine ⟨6001765963445127654927557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001177308963418436618371 6001765963445127654927557)
              ·
                refine ⟨1125331118145961435298917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6001765963445127654927557 1125331118145961435298917)
                ·
                  refine ⟨210999584652367769118547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125331118145961435298917 210999584652367769118547)
                  ·
                    rfl

theorem cell22_1849141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_1849141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849141 prefixEnd_1849141 := by exact prefixLift 1849141
  have htrace : WordTrace (prefixWord ++ tailWord_1849141) baseStart_1849141 baseEnd_1849141 := by
    simpa [prefixWord, tailWord_1849141, baseEnd_1849141] using wordTrace_append hprefix tailTrace_1849141
  have hstable : (prefixWord ++ tailWord_1849141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849141).length < 2 ^ (prefixWord ++ tailWord_1849141).sum := by decide
  have hdescent : baseEnd_1849141 < baseStart_1849141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849169 : List Nat := [1, 2, 2, 1, 5, 2, 3, 6]
def baseStart_1849169 : Nat := 118140960795 + 1849169 * 2 ^ 59
def prefixEnd_1849169 : Nat := 4983230072969 + 3 ^ 40 * 1849169 * 2
def baseEnd_1849169 : Nat := 70334259881035618628395

theorem tailTrace_1849169 : CollatzResearch.WordTrace tailWord_1849169 prefixEnd_1849169 70334259881035618628395 := by
  unfold tailWord_1849169
  simp only [CollatzResearch.WordTrace]
  refine ⟨67444734237784000767158561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44963156158522667178105707 67444734237784000767158561)
  ·
    refine ⟨50583550678338000575368921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67444734237784000767158561 50583550678338000575368921)
    ·
      refine ⟨37937663008753500431526691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50583550678338000575368921 37937663008753500431526691)
      ·
        refine ⟨56906494513130250647290037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37937663008753500431526691 56906494513130250647290037)
        ·
          refine ⟨5334983860605960998183441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56906494513130250647290037 5334983860605960998183441)
          ·
            refine ⟨4001237895454470748637581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5334983860605960998183441 4001237895454470748637581)
            ·
              refine ⟨1500464210795426530739093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4001237895454470748637581 1500464210795426530739093)
              ·
                refine ⟨70334259881035618628395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1500464210795426530739093 70334259881035618628395)
                ·
                  rfl

theorem cell22_1849169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 6].length) (baseStart_1849169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849169 prefixEnd_1849169 := by exact prefixLift 1849169
  have htrace : WordTrace (prefixWord ++ tailWord_1849169) baseStart_1849169 baseEnd_1849169 := by
    simpa [prefixWord, tailWord_1849169, baseEnd_1849169] using wordTrace_append hprefix tailTrace_1849169
  have hstable : (prefixWord ++ tailWord_1849169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849169).length < 2 ^ (prefixWord ++ tailWord_1849169).sum := by decide
  have hdescent : baseEnd_1849169 < baseStart_1849169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849201 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 1, 3]
def baseStart_1849201 : Nat := 118140960795 + 1849201 * 2 ^ 59
def prefixEnd_1849201 : Nat := 4983230072969 + 3 ^ 40 * 1849201 * 2
def baseEnd_1849201 : Nat := 633019293183283150855457

theorem tailTrace_1849201 : CollatzResearch.WordTrace tailWord_1849201 prefixEnd_1849201 633019293183283150855457 := by
  unfold tailWord_1849201
  simp only [CollatzResearch.WordTrace]
  refine ⟨67445901373668070232323457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44963934249112046821548971 67445901373668070232323457)
  ·
    refine ⟨50584426030251052674242593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67445901373668070232323457 50584426030251052674242593)
    ·
      refine ⟨37938319522688289505681945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50584426030251052674242593 37938319522688289505681945)
      ·
        refine ⟨28453739642016217129261459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37938319522688289505681945 28453739642016217129261459)
        ·
          refine ⟨42680609463024325693892189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28453739642016217129261459 42680609463024325693892189)
          ·
            refine ⟨16005228548634122135209571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42680609463024325693892189 16005228548634122135209571)
            ·
              refine ⟨24007842822951183202814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005228548634122135209571 24007842822951183202814357)
              ·
                refine ⟨1125367632325836712631923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24007842822951183202814357 1125367632325836712631923)
                ·
                  refine ⟨1688051448488755068947885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125367632325836712631923 1688051448488755068947885)
                  ·
                    refine ⟨633019293183283150855457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688051448488755068947885 633019293183283150855457)
                    ·
                      rfl

theorem cell22_1849201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_1849201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849201 prefixEnd_1849201 := by exact prefixLift 1849201
  have htrace : WordTrace (prefixWord ++ tailWord_1849201) baseStart_1849201 baseEnd_1849201 := by
    simpa [prefixWord, tailWord_1849201, baseEnd_1849201] using wordTrace_append hprefix tailTrace_1849201
  have hstable : (prefixWord ++ tailWord_1849201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849201).length < 2 ^ (prefixWord ++ tailWord_1849201).sum := by decide
  have hdescent : baseEnd_1849201 < baseStart_1849201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849257 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_1849257 : Nat := 118140960795 + 1849257 * 2 ^ 59
def prefixEnd_1849257 : Nat := 4983230072969 + 3 ^ 40 * 1849257 * 2
def baseEnd_1849257 : Nat := 633038463127717671455285

theorem tailTrace_1849257 : CollatzResearch.WordTrace tailWord_1849257 prefixEnd_1849257 633038463127717671455285 := by
  unfold tailWord_1849257
  simp only [CollatzResearch.WordTrace]
  refine ⟨67447943861465191796362025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44965295907643461197574683 67447943861465191796362025)
  ·
    refine ⟨50585957896098893847271519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67447943861465191796362025 50585957896098893847271519)
    ·
      refine ⟨75878936844148340770907279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50585957896098893847271519 75878936844148340770907279)
      ·
        refine ⟨113818405266222511156360919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75878936844148340770907279 113818405266222511156360919)
        ·
          refine ⟨170727607899333766734541379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113818405266222511156360919 170727607899333766734541379)
          ·
            refine ⟨256091411849000650101812069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170727607899333766734541379 256091411849000650101812069)
            ·
              refine ⟨48017139721687621894089763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256091411849000650101812069 48017139721687621894089763)
              ·
                refine ⟨72025709582531432841134645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48017139721687621894089763 72025709582531432841134645)
                ·
                  refine ⟨6752410273362321828856373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72025709582531432841134645 6752410273362321828856373)
                  ·
                    refine ⟨633038463127717671455285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6752410273362321828856373 633038463127717671455285)
                    ·
                      rfl

theorem cell22_1849257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_1849257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849257 prefixEnd_1849257 := by exact prefixLift 1849257
  have htrace : WordTrace (prefixWord ++ tailWord_1849257) baseStart_1849257 baseEnd_1849257 := by
    simpa [prefixWord, tailWord_1849257, baseEnd_1849257] using wordTrace_append hprefix tailTrace_1849257
  have hstable : (prefixWord ++ tailWord_1849257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849257).length < 2 ^ (prefixWord ++ tailWord_1849257).sum := by decide
  have hdescent : baseEnd_1849257 < baseStart_1849257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849274 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_1849274 : Nat := 118140960795 + 1849274 * 2 ^ 59
def prefixEnd_1849274 : Nat := 4983230072969 + 3 ^ 40 * 1849274 * 2
def baseEnd_1849274 : Nat := 633044282575135293780233

theorem tailTrace_1849274 : CollatzResearch.WordTrace tailWord_1849274 prefixEnd_1849274 633044282575135293780233 := by
  unfold tailWord_1849274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16862140975600900924932719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44965709268269069133153917 16862140975600900924932719)
  ·
    refine ⟨25293211463401351387399079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16862140975600900924932719 25293211463401351387399079)
    ·
      refine ⟨37939817195102027081098619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25293211463401351387399079 37939817195102027081098619)
      ·
        refine ⟨56909725792653040621647929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37939817195102027081098619 56909725792653040621647929)
        ·
          refine ⟨42682294344489780466235947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56909725792653040621647929 42682294344489780466235947)
          ·
            refine ⟨64023441516734670699353921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42682294344489780466235947 64023441516734670699353921)
            ·
              refine ⟨48017581137551003024515441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64023441516734670699353921 48017581137551003024515441)
              ·
                refine ⟨36013185853163252268386581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48017581137551003024515441 36013185853163252268386581)
                ·
                  refine ⟨1688118086867027450080621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36013185853163252268386581 1688118086867027450080621)
                  ·
                    refine ⟨633044282575135293780233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688118086867027450080621 633044282575135293780233)
                    ·
                      rfl

theorem cell22_1849274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_1849274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849274 prefixEnd_1849274 := by exact prefixLift 1849274
  have htrace : WordTrace (prefixWord ++ tailWord_1849274) baseStart_1849274 baseEnd_1849274 := by
    simpa [prefixWord, tailWord_1849274, baseEnd_1849274] using wordTrace_append hprefix tailTrace_1849274
  have hstable : (prefixWord ++ tailWord_1849274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849274).length < 2 ^ (prefixWord ++ tailWord_1849274).sum := by decide
  have hdescent : baseEnd_1849274 < baseStart_1849274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849278 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1849278 : Nat := 118140960795 + 1849278 * 2 ^ 59
def prefixEnd_1849278 : Nat := 4983230072969 + 3 ^ 40 * 1849278 * 2
def baseEnd_1849278 : Nat := 633045651856880616680221

theorem tailTrace_1849278 : CollatzResearch.WordTrace tailWord_1849278 prefixEnd_1849278 633045651856880616680221 := by
  unfold tailWord_1849278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8431088724298639047859561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44965806529592741588584325 8431088724298639047859561)
  ·
    refine ⟨6323316543223979285894671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8431088724298639047859561 6323316543223979285894671)
    ·
      refine ⟨9484974814835968928842007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323316543223979285894671 9484974814835968928842007)
      ·
        refine ⟨14227462222253953393263011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484974814835968928842007 14227462222253953393263011)
        ·
          refine ⟨21341193333380930089894517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14227462222253953393263011 21341193333380930089894517)
          ·
            refine ⟨2000736875004462195927611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21341193333380930089894517 2000736875004462195927611)
            ·
              refine ⟨3001105312506693293891417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000736875004462195927611 3001105312506693293891417)
              ·
                refine ⟨2250828984380019970418563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001105312506693293891417 2250828984380019970418563)
                ·
                  refine ⟨3376243476570029955627845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250828984380019970418563 3376243476570029955627845)
                  ·
                    refine ⟨633045651856880616680221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376243476570029955627845 633045651856880616680221)
                    ·
                      rfl

theorem cell22_1849278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1849278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849278 prefixEnd_1849278 := by exact prefixLift 1849278
  have htrace : WordTrace (prefixWord ++ tailWord_1849278) baseStart_1849278 baseEnd_1849278 := by
    simpa [prefixWord, tailWord_1849278, baseEnd_1849278] using wordTrace_append hprefix tailTrace_1849278
  have hstable : (prefixWord ++ tailWord_1849278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849278).length < 2 ^ (prefixWord ++ tailWord_1849278).sum := by decide
  have hdescent : baseEnd_1849278 < baseStart_1849278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849411 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 4]
def baseStart_1849411 : Nat := 118140960795 + 1849411 * 2 ^ 59
def prefixEnd_1849411 : Nat := 4983230072969 + 3 ^ 40 * 1849411 * 2
def baseEnd_1849411 : Nat := 211030393491637534368271

theorem tailTrace_1849411 : CollatzResearch.WordTrace tailWord_1849411 prefixEnd_1849411 211030393491637534368271 := by
  unfold tailWord_1849411
  simp only [CollatzResearch.WordTrace]
  refine ⟨67453560702907276097468087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44969040468604850731645391 67453560702907276097468087)
  ·
    refine ⟨101180341054360914146202131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67453560702907276097468087 101180341054360914146202131)
    ·
      refine ⟨151770511581541371219303197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101180341054360914146202131 151770511581541371219303197)
      ·
        refine ⟨56913941843078014207238699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151770511581541371219303197 56913941843078014207238699)
        ·
          refine ⟨85370912764617021310858049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56913941843078014207238699 85370912764617021310858049)
          ·
            refine ⟨64028184573462765983143537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85370912764617021310858049 64028184573462765983143537)
            ·
              refine ⟨48021138430097074487357653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64028184573462765983143537 48021138430097074487357653)
              ·
                refine ⟨1125495431955400183297445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48021138430097074487357653 1125495431955400183297445)
                ·
                  refine ⟨211030393491637534368271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125495431955400183297445 211030393491637534368271)
                  ·
                    rfl

theorem cell22_1849411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 4].length) (baseStart_1849411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849411 prefixEnd_1849411 := by exact prefixLift 1849411
  have htrace : WordTrace (prefixWord ++ tailWord_1849411) baseStart_1849411 baseEnd_1849411 := by
    simpa [prefixWord, tailWord_1849411, baseEnd_1849411] using wordTrace_append hprefix tailTrace_1849411
  have hstable : (prefixWord ++ tailWord_1849411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849411).length < 2 ^ (prefixWord ++ tailWord_1849411).sum := by decide
  have hdescent : baseEnd_1849411 < baseStart_1849411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849458 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1849458 : Nat := 118140960795 + 1849458 * 2 ^ 59
def prefixEnd_1849458 : Nat := 4983230072969 + 3 ^ 40 * 1849458 * 2
def baseEnd_1849458 : Nat := 633107269535420147179669

theorem tailTrace_1849458 : CollatzResearch.WordTrace tailWord_1849458 prefixEnd_1849458 633107269535420147179669 := by
  unfold tailWord_1849458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16863818733434250781107257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44970183289158002082952685 16863818733434250781107257)
  ·
    refine ⟨12647864050075688085830443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16863818733434250781107257 12647864050075688085830443)
    ·
      refine ⟨18971796075113532128745665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12647864050075688085830443 18971796075113532128745665)
      ·
        refine ⟨14228847056335149096559249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18971796075113532128745665 14228847056335149096559249)
        ·
          refine ⟨10671635292251361822419437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14228847056335149096559249 10671635292251361822419437)
          ·
            refine ⟨4001863234594260683407289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10671635292251361822419437 4001863234594260683407289)
            ·
              refine ⟨3001397425945695512555467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001863234594260683407289 3001397425945695512555467)
              ·
                refine ⟨4502096138918543268833201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001397425945695512555467 4502096138918543268833201)
                ·
                  refine ⟨3376572104188907451624901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502096138918543268833201 3376572104188907451624901)
                  ·
                    refine ⟨633107269535420147179669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376572104188907451624901 633107269535420147179669)
                    ·
                      rfl

theorem cell22_1849458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1849458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849458 prefixEnd_1849458 := by exact prefixLift 1849458
  have htrace : WordTrace (prefixWord ++ tailWord_1849458) baseStart_1849458 baseEnd_1849458 := by
    simpa [prefixWord, tailWord_1849458, baseEnd_1849458] using wordTrace_append hprefix tailTrace_1849458
  have hstable : (prefixWord ++ tailWord_1849458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849458).length < 2 ^ (prefixWord ++ tailWord_1849458).sum := by decide
  have hdescent : baseEnd_1849458 < baseStart_1849458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849565 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1849565 : Nat := 118140960795 + 1849565 * 2 ^ 59
def prefixEnd_1849565 : Nat := 4983230072969 + 3 ^ 40 * 1849565 * 2
def baseEnd_1849565 : Nat := 633143897822107534754341

theorem tailTrace_1849565 : CollatzResearch.WordTrace tailWord_1849565 prefixEnd_1849565 633143897822107534754341 := by
  unfold tailWord_1849565
  simp only [CollatzResearch.WordTrace]
  refine ⟨67459177544349360398574149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44972785029566240265716099 67459177544349360398574149)
  ·
    refine ⟨12648595789565505074732653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67459177544349360398574149 12648595789565505074732653)
    ·
      refine ⟨4743223421087064403024745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12648595789565505074732653 4743223421087064403024745)
      ·
        refine ⟨3557417565815298302268559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4743223421087064403024745 3557417565815298302268559)
        ·
          refine ⟨5336126348722947453402839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557417565815298302268559 5336126348722947453402839)
          ·
            refine ⟨8004189523084421180104259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336126348722947453402839 8004189523084421180104259)
            ·
              refine ⟨12006284284626631770156389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004189523084421180104259 12006284284626631770156389)
              ·
                refine ⟨2251178303367493456904323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12006284284626631770156389 2251178303367493456904323)
                ·
                  refine ⟨3376767455051240185356485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251178303367493456904323 3376767455051240185356485)
                  ·
                    refine ⟨633143897822107534754341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376767455051240185356485 633143897822107534754341)
                    ·
                      rfl

theorem cell22_1849565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1849565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849565 prefixEnd_1849565 := by exact prefixLift 1849565
  have htrace : WordTrace (prefixWord ++ tailWord_1849565) baseStart_1849565 baseEnd_1849565 := by
    simpa [prefixWord, tailWord_1849565, baseEnd_1849565] using wordTrace_append hprefix tailTrace_1849565
  have hstable : (prefixWord ++ tailWord_1849565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849565).length < 2 ^ (prefixWord ++ tailWord_1849565).sum := by decide
  have hdescent : baseEnd_1849565 < baseStart_1849565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849578 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1849578 : Nat := 118140960795 + 1849578 * 2 ^ 59
def prefixEnd_1849578 : Nat := 4983230072969 + 3 ^ 40 * 1849578 * 2
def baseEnd_1849578 : Nat := 633148347987779834179301

theorem tailTrace_1849578 : CollatzResearch.WordTrace tailWord_1849578 prefixEnd_1849578 633148347987779834179301 := by
  unfold tailWord_1849578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16864912923325565904699347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44973101128868175745864925 16864912923325565904699347)
  ·
    refine ⟨25297369384988348857049021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16864912923325565904699347 25297369384988348857049021)
    ·
      refine ⟨9486513519370630821393383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25297369384988348857049021 9486513519370630821393383)
      ·
        refine ⟨14229770279055946232090075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9486513519370630821393383 14229770279055946232090075)
        ·
          refine ⟨21344655418583919348135113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229770279055946232090075 21344655418583919348135113)
          ·
            refine ⟨16008491563937939511101335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21344655418583919348135113 16008491563937939511101335)
            ·
              refine ⟨24012737345906909266652003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008491563937939511101335 24012737345906909266652003)
              ·
                refine ⟨36019106018860363899978005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24012737345906909266652003 36019106018860363899978005)
                ·
                  refine ⟨1688395594634079557811469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36019106018860363899978005 1688395594634079557811469)
                  ·
                    refine ⟨633148347987779834179301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688395594634079557811469 633148347987779834179301)
                    ·
                      rfl

theorem cell22_1849578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1849578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849578 prefixEnd_1849578 := by exact prefixLift 1849578
  have htrace : WordTrace (prefixWord ++ tailWord_1849578) baseStart_1849578 baseEnd_1849578 := by
    simpa [prefixWord, tailWord_1849578, baseEnd_1849578] using wordTrace_append hprefix tailTrace_1849578
  have hstable : (prefixWord ++ tailWord_1849578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849578).length < 2 ^ (prefixWord ++ tailWord_1849578).sum := by decide
  have hdescent : baseEnd_1849578 < baseStart_1849578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849608 : List Nat := [2, 1, 3, 2, 3, 2, 2, 7]
def baseStart_1849608 : Nat := 118140960795 + 1849608 * 2 ^ 59
def prefixEnd_1849608 : Nat := 4983230072969 + 3 ^ 40 * 1849608 * 2
def baseEnd_1849608 : Nat := 70350957511207750658801

theorem tailTrace_1849608 : CollatzResearch.WordTrace tailWord_1849608 prefixEnd_1849608 70350957511207750658801 := by
  unfold tailWord_1849608
  simp only [CollatzResearch.WordTrace]
  refine ⟨33730372941596789371194739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44973830588795719161592985 33730372941596789371194739)
  ·
    refine ⟨50595559412395184056792109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33730372941596789371194739 50595559412395184056792109)
    ·
      refine ⟨18973334779648194021297041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50595559412395184056792109 18973334779648194021297041)
      ·
        refine ⟨14230001084736145515972781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18973334779648194021297041 14230001084736145515972781)
        ·
          refine ⟨5336250406776054568489793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14230001084736145515972781 5336250406776054568489793)
          ·
            refine ⟨4002187805082040926367345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5336250406776054568489793 4002187805082040926367345)
            ·
              refine ⟨3001640853811530694775509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002187805082040926367345 3001640853811530694775509)
              ·
                refine ⟨70350957511207750658801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3001640853811530694775509 70350957511207750658801)
                ·
                  rfl

theorem cell22_1849608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_1849608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849608 prefixEnd_1849608 := by exact prefixLift 1849608
  have htrace : WordTrace (prefixWord ++ tailWord_1849608) baseStart_1849608 baseEnd_1849608 := by
    simpa [prefixWord, tailWord_1849608, baseEnd_1849608] using wordTrace_append hprefix tailTrace_1849608
  have hstable : (prefixWord ++ tailWord_1849608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849608).length < 2 ^ (prefixWord ++ tailWord_1849608).sum := by decide
  have hdescent : baseEnd_1849608 < baseStart_1849608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849700 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1849700 : Nat := 118140960795 + 1849700 * 2 ^ 59
def prefixEnd_1849700 : Nat := 4983230072969 + 3 ^ 40 * 1849700 * 2
def baseEnd_1849700 : Nat := 633190111081012182628927

theorem tailTrace_1849700 : CollatzResearch.WordTrace tailWord_1849700 prefixEnd_1849700 633190111081012182628927 := by
  unfold tailWord_1849700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33732050699430139227369277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44976067599240185636492369 33732050699430139227369277)
  ·
    refine ⟨12649519012286302210263479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33732050699430139227369277 12649519012286302210263479)
    ·
      refine ⟨18974278518429453315395219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12649519012286302210263479 18974278518429453315395219)
      ·
        refine ⟨28461417777644179973092829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18974278518429453315395219 28461417777644179973092829)
        ·
          refine ⟨10673031666616567489909811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28461417777644179973092829 10673031666616567489909811)
          ·
            refine ⟨16009547499924851234864717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673031666616567489909811 16009547499924851234864717)
            ·
              refine ⟨6003580312471819213074269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16009547499924851234864717 6003580312471819213074269)
              ·
                refine ⟨2251342617176932204902851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6003580312471819213074269 2251342617176932204902851)
                ·
                  refine ⟨3377013925765398307354277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251342617176932204902851 3377013925765398307354277)
                  ·
                    refine ⟨633190111081012182628927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377013925765398307354277 633190111081012182628927)
                    ·
                      rfl

theorem cell22_1849700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1849700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849700 prefixEnd_1849700 := by exact prefixLift 1849700
  have htrace : WordTrace (prefixWord ++ tailWord_1849700) baseStart_1849700 baseEnd_1849700 := by
    simpa [prefixWord, tailWord_1849700, baseEnd_1849700] using wordTrace_append hprefix tailTrace_1849700
  have hstable : (prefixWord ++ tailWord_1849700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849700).length < 2 ^ (prefixWord ++ tailWord_1849700).sum := by decide
  have hdescent : baseEnd_1849700 < baseStart_1849700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849781 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1849781 : Nat := 118140960795 + 1849781 * 2 ^ 59
def prefixEnd_1849781 : Nat := 4983230072969 + 3 ^ 40 * 1849781 * 2
def baseEnd_1849781 : Nat := 633217839036354971353679

theorem tailTrace_1849781 : CollatzResearch.WordTrace tailWord_1849781 prefixEnd_1849781 633217839036354971353679 := by
  unfold tailWord_1849781
  simp only [CollatzResearch.WordTrace]
  refine ⟨67467055711566829288437197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44978037141044552858958131 67467055711566829288437197)
  ·
    refine ⟨25300145891837560983163949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67467055711566829288437197 25300145891837560983163949)
    ·
      refine ⟨9487554709439085368686481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25300145891837560983163949 9487554709439085368686481)
      ·
        refine ⟨7115666032079314026514861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9487554709439085368686481 7115666032079314026514861)
        ·
          refine ⟨2668374762029742759943073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7115666032079314026514861 2668374762029742759943073)
          ·
            refine ⟨2001281071522307069957305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668374762029742759943073 2001281071522307069957305)
            ·
              refine ⟨1500960803641730302467979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001281071522307069957305 1500960803641730302467979)
              ·
                refine ⟨2251441205462595453701969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500960803641730302467979 2251441205462595453701969)
                ·
                  refine ⟨1688580904096946590276477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251441205462595453701969 1688580904096946590276477)
                  ·
                    refine ⟨633217839036354971353679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688580904096946590276477 633217839036354971353679)
                    ·
                      rfl

theorem cell22_1849781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1849781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849781 prefixEnd_1849781 := by exact prefixLift 1849781
  have htrace : WordTrace (prefixWord ++ tailWord_1849781) baseStart_1849781 baseEnd_1849781 := by
    simpa [prefixWord, tailWord_1849781, baseEnd_1849781] using wordTrace_append hprefix tailTrace_1849781
  have hstable : (prefixWord ++ tailWord_1849781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849781).length < 2 ^ (prefixWord ++ tailWord_1849781).sum := by decide
  have hdescent : baseEnd_1849781 < baseStart_1849781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849803 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_1849803 : Nat := 118140960795 + 1849803 * 2 ^ 59
def prefixEnd_1849803 : Nat := 4983230072969 + 3 ^ 40 * 1849803 * 2
def baseEnd_1849803 : Nat := 633225370085954247303611

theorem tailTrace_1849803 : CollatzResearch.WordTrace tailWord_1849803 prefixEnd_1849803 633225370085954247303611 := by
  unfold tailWord_1849803
  simp only [CollatzResearch.WordTrace]
  refine ⟨67467858117487127045738063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44978572078324751363825375 67467858117487127045738063)
  ·
    refine ⟨101201787176230690568607095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67467858117487127045738063 101201787176230690568607095)
    ·
      refine ⟨151802680764346035852910643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101201787176230690568607095 151802680764346035852910643)
      ·
        refine ⟨227704021146519053779365965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151802680764346035852910643 227704021146519053779365965)
        ·
          refine ⟨85389007929944645167262237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227704021146519053779365965 85389007929944645167262237)
          ·
            refine ⟨32020877973729241937723339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85389007929944645167262237 32020877973729241937723339)
            ·
              refine ⟨48031316960593862906585009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32020877973729241937723339 48031316960593862906585009)
              ·
                refine ⟨36023487720445397179938757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48031316960593862906585009 36023487720445397179938757)
                ·
                  refine ⟨6754403947583511971238517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36023487720445397179938757 6754403947583511971238517)
                  ·
                    refine ⟨633225370085954247303611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6754403947583511971238517 633225370085954247303611)
                    ·
                      rfl

theorem cell22_1849803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_1849803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849803 prefixEnd_1849803 := by exact prefixLift 1849803
  have htrace : WordTrace (prefixWord ++ tailWord_1849803) baseStart_1849803 baseEnd_1849803 := by
    simpa [prefixWord, tailWord_1849803, baseEnd_1849803] using wordTrace_append hprefix tailTrace_1849803
  have hstable : (prefixWord ++ tailWord_1849803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849803).length < 2 ^ (prefixWord ++ tailWord_1849803).sum := by decide
  have hdescent : baseEnd_1849803 < baseStart_1849803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849837 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1849837 : Nat := 118140960795 + 1849837 * 2 ^ 59
def prefixEnd_1849837 : Nat := 4983230072969 + 3 ^ 40 * 1849837 * 2
def baseEnd_1849837 : Nat := 633237008980789491953507

theorem tailTrace_1849837 : CollatzResearch.WordTrace tailWord_1849837 prefixEnd_1849837 633237008980789491953507 := by
  unfold tailWord_1849837
  simp only [CollatzResearch.WordTrace]
  refine ⟨67469098199363950852475765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44979398799575967234983843 67469098199363950852475765)
  ·
    refine ⟨6325227956190370392419603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67469098199363950852475765 6325227956190370392419603)
    ·
      refine ⟨9487841934285555588629405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6325227956190370392419603 9487841934285555588629405)
      ·
        refine ⟨3557940725357083345736027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9487841934285555588629405 3557940725357083345736027)
        ·
          refine ⟨5336911088035625018604041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557940725357083345736027 5336911088035625018604041)
          ·
            refine ⟨4002683316026718763953031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5336911088035625018604041 4002683316026718763953031)
            ·
              refine ⟨6004024974040078145929547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002683316026718763953031 6004024974040078145929547)
              ·
                refine ⟨9006037461060117218894321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004024974040078145929547 9006037461060117218894321)
                ·
                  refine ⟨6754528095795087914170741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9006037461060117218894321 6754528095795087914170741)
                  ·
                    refine ⟨633237008980789491953507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6754528095795087914170741 633237008980789491953507)
                    ·
                      rfl

theorem cell22_1849837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1849837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849837 prefixEnd_1849837 := by exact prefixLift 1849837
  have htrace : WordTrace (prefixWord ++ tailWord_1849837) baseStart_1849837 baseEnd_1849837 := by
    simpa [prefixWord, tailWord_1849837, baseEnd_1849837] using wordTrace_append hprefix tailTrace_1849837
  have hstable : (prefixWord ++ tailWord_1849837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849837).length < 2 ^ (prefixWord ++ tailWord_1849837).sum := by decide
  have hdescent : baseEnd_1849837 < baseStart_1849837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849867 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 4]
def baseStart_1849867 : Nat := 118140960795 + 1849867 * 2 ^ 59
def prefixEnd_1849867 : Nat := 4983230072969 + 3 ^ 40 * 1849867 * 2
def baseEnd_1849867 : Nat := 211082426197959804567805

theorem tailTrace_1849867 : CollatzResearch.WordTrace tailWord_1849867 prefixEnd_1849867 211082426197959804567805 := by
  unfold tailWord_1849867
  simp only [CollatzResearch.WordTrace]
  refine ⟨67470192389255265976067855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44980128259503510650711903 67470192389255265976067855)
  ·
    refine ⟨101205288583882898964101783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67470192389255265976067855 101205288583882898964101783)
    ·
      refine ⟨151807932875824348446152675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101205288583882898964101783 151807932875824348446152675)
      ·
        refine ⟨227711899313736522669229013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151807932875824348446152675 227711899313736522669229013)
        ·
          refine ⟨5336997640165699750060055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 227711899313736522669229013 5336997640165699750060055)
          ·
            refine ⟨8005496460248549625090083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336997640165699750060055 8005496460248549625090083)
            ·
              refine ⟨12008244690372824437635125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8005496460248549625090083 12008244690372824437635125)
              ·
                refine ⟨1125772939722452291028293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12008244690372824437635125 1125772939722452291028293)
                ·
                  refine ⟨211082426197959804567805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125772939722452291028293 211082426197959804567805)
                  ·
                    rfl

theorem cell22_1849867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 4].length) (baseStart_1849867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849867 prefixEnd_1849867 := by exact prefixLift 1849867
  have htrace : WordTrace (prefixWord ++ tailWord_1849867) baseStart_1849867 baseEnd_1849867 := by
    simpa [prefixWord, tailWord_1849867, baseEnd_1849867] using wordTrace_append hprefix tailTrace_1849867
  have hstable : (prefixWord ++ tailWord_1849867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849867).length < 2 ^ (prefixWord ++ tailWord_1849867).sum := by decide
  have hdescent : baseEnd_1849867 < baseStart_1849867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849918 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1849918 : Nat := 118140960795 + 1849918 * 2 ^ 59
def prefixEnd_1849918 : Nat := 4983230072969 + 3 ^ 40 * 1849918 * 2
def baseEnd_1849918 : Nat := 211088245645377426892753

theorem tailTrace_1849918 : CollatzResearch.WordTrace tailWord_1849918 prefixEnd_1849918 211088245645377426892753 := by
  unfold tailWord_1849918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434006564008812710771801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44981368341380334457449605 8434006564008812710771801)
  ·
    refine ⟨6325504923006609533078851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8434006564008812710771801 6325504923006609533078851)
    ·
      refine ⟨9488257384509914299618277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6325504923006609533078851 9488257384509914299618277)
      ·
        refine ⟨1779048259595608931178427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9488257384509914299618277 1779048259595608931178427)
        ·
          refine ⟨2668572389393413396767641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779048259595608931178427 2668572389393413396767641)
          ·
            refine ⟨2001429292045060047575731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668572389393413396767641 2001429292045060047575731)
            ·
              refine ⟨3002143938067590071363597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001429292045060047575731 3002143938067590071363597)
              ·
                refine ⟨1125803976775346276761349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3002143938067590071363597 1125803976775346276761349)
                ·
                  refine ⟨211088245645377426892753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125803976775346276761349 211088245645377426892753)
                  ·
                    rfl

theorem cell22_1849918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1849918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849918 prefixEnd_1849918 := by exact prefixLift 1849918
  have htrace : WordTrace (prefixWord ++ tailWord_1849918) baseStart_1849918 baseEnd_1849918 := by
    simpa [prefixWord, tailWord_1849918, baseEnd_1849918] using wordTrace_append hprefix tailTrace_1849918
  have hstable : (prefixWord ++ tailWord_1849918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849918).length < 2 ^ (prefixWord ++ tailWord_1849918).sum := by decide
  have hdescent : baseEnd_1849918 < baseStart_1849918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849944 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 1, 3]
def baseStart_1849944 : Nat := 118140960795 + 1849944 * 2 ^ 59
def prefixEnd_1849944 : Nat := 4983230072969 + 3 ^ 40 * 1849944 * 2
def baseEnd_1849944 : Nat := 633273637267476879528179

theorem tailTrace_1849944 : CollatzResearch.WordTrace tailWord_1849944 prefixEnd_1849944 633273637267476879528179 := by
  unfold tailWord_1849944
  simp only [CollatzResearch.WordTrace]
  refine ⟨33736500404988154063310443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44982000539984205417747257 33736500404988154063310443)
  ·
    refine ⟨50604750607482231094965665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33736500404988154063310443 50604750607482231094965665)
    ·
      refine ⟨37953562955611673321224249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50604750607482231094965665 37953562955611673321224249)
      ·
        refine ⟨28465172216708754990918187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37953562955611673321224249 28465172216708754990918187)
        ·
          refine ⟨42697758325063132486377281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28465172216708754990918187 42697758325063132486377281)
          ·
            refine ⟨32023318743797349364782961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42697758325063132486377281 32023318743797349364782961)
            ·
              refine ⟨24017489057848012023587221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32023318743797349364782961 24017489057848012023587221)
              ·
                refine ⟨1125819799586625563605651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24017489057848012023587221 1125819799586625563605651)
                ·
                  refine ⟨1688729699379938345408477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125819799586625563605651 1688729699379938345408477)
                  ·
                    refine ⟨633273637267476879528179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688729699379938345408477 633273637267476879528179)
                    ·
                      rfl

theorem cell22_1849944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_1849944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849944 prefixEnd_1849944 := by exact prefixLift 1849944
  have htrace : WordTrace (prefixWord ++ tailWord_1849944) baseStart_1849944 baseEnd_1849944 := by
    simpa [prefixWord, tailWord_1849944, baseEnd_1849944] using wordTrace_append hprefix tailTrace_1849944
  have hstable : (prefixWord ++ tailWord_1849944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849944).length < 2 ^ (prefixWord ++ tailWord_1849944).sum := by decide
  have hdescent : baseEnd_1849944 < baseStart_1849944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849950 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1849950 : Nat := 118140960795 + 1849950 * 2 ^ 59
def prefixEnd_1849950 : Nat := 4983230072969 + 3 ^ 40 * 1849950 * 2
def baseEnd_1849950 : Nat := 633275691190094863878161

theorem tailTrace_1849950 : CollatzResearch.WordTrace tailWord_1849950 prefixEnd_1849950 633275691190094863878161 := by
  unfold tailWord_1849950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434152455994321393917413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44982146431969714100892869 8434152455994321393917413)
  ·
    refine ⟨1581403585498935261359515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8434152455994321393917413 1581403585498935261359515)
    ·
      refine ⟨2372105378248402892039273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581403585498935261359515 2372105378248402892039273)
      ·
        refine ⟨1779079033686302169029455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2372105378248402892039273 1779079033686302169029455)
        ·
          refine ⟨2668618550529453253544183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779079033686302169029455 2668618550529453253544183)
          ·
            refine ⟨4002927825794179880316275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668618550529453253544183 4002927825794179880316275)
            ·
              refine ⟨6004391738691269820474413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002927825794179880316275 6004391738691269820474413)
              ·
                refine ⟨2251646902009226182677905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6004391738691269820474413 2251646902009226182677905)
                ·
                  refine ⟨1688735176506919637008429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251646902009226182677905 1688735176506919637008429)
                  ·
                    refine ⟨633275691190094863878161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688735176506919637008429 633275691190094863878161)
                    ·
                      rfl

theorem cell22_1849950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1849950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849950 prefixEnd_1849950 := by exact prefixLift 1849950
  have htrace : WordTrace (prefixWord ++ tailWord_1849950) baseStart_1849950 baseEnd_1849950 := by
    simpa [prefixWord, tailWord_1849950, baseEnd_1849950] using wordTrace_append hprefix tailTrace_1849950
  have hstable : (prefixWord ++ tailWord_1849950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849950).length < 2 ^ (prefixWord ++ tailWord_1849950).sum := by decide
  have hdescent : baseEnd_1849950 < baseStart_1849950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849955 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_1849955 : Nat := 118140960795 + 1849955 * 2 ^ 59
def prefixEnd_1849955 : Nat := 4983230072969 + 3 ^ 40 * 1849955 * 2
def baseEnd_1849955 : Nat := 633277402792276517503145

theorem tailTrace_1849955 : CollatzResearch.WordTrace tailWord_1849955 prefixEnd_1849955 633277402792276517503145 := by
  unfold tailWord_1849955
  simp only [CollatzResearch.WordTrace]
  refine ⟨67473402012936457005271319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44982268008624304670180879 67473402012936457005271319)
  ·
    refine ⟨101210103019404685507906979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67473402012936457005271319 101210103019404685507906979)
    ·
      refine ⟨151815154529107028261860469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101210103019404685507906979 151815154529107028261860469)
      ·
        refine ⟨14232670737103783899549419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151815154529107028261860469 14232670737103783899549419)
        ·
          refine ⟨21349006105655675849324129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14232670737103783899549419 21349006105655675849324129)
          ·
            refine ⟨16011754579241756886993097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21349006105655675849324129 16011754579241756886993097)
            ·
              refine ⟨12008815934431317665244823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16011754579241756886993097 12008815934431317665244823)
              ·
                refine ⟨18013223901646976497867235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008815934431317665244823 18013223901646976497867235)
                ·
                  refine ⟨27019835852470464746800853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18013223901646976497867235 27019835852470464746800853)
                  ·
                    refine ⟨633277402792276517503145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27019835852470464746800853 633277402792276517503145)
                    ·
                      rfl

theorem cell22_1849955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_1849955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849955 prefixEnd_1849955 := by exact prefixLift 1849955
  have htrace : WordTrace (prefixWord ++ tailWord_1849955) baseStart_1849955 baseEnd_1849955 := by
    simpa [prefixWord, tailWord_1849955, baseEnd_1849955] using wordTrace_append hprefix tailTrace_1849955
  have hstable : (prefixWord ++ tailWord_1849955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849955).length < 2 ^ (prefixWord ++ tailWord_1849955).sum := by decide
  have hdescent : baseEnd_1849955 < baseStart_1849955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849987 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 1, 4]
def baseStart_1849987 : Nat := 118140960795 + 1849987 * 2 ^ 59
def prefixEnd_1849987 : Nat := 4983230072969 + 3 ^ 40 * 1849987 * 2
def baseEnd_1849987 : Nat := 633288357046239100703047

theorem tailTrace_1849987 : CollatzResearch.WordTrace tailWord_1849987 prefixEnd_1849987 633288357046239100703047 := by
  unfold tailWord_1849987
  simp only [CollatzResearch.WordTrace]
  refine ⟨67474569148820526470436215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44983046099213684313624143 67474569148820526470436215)
  ·
    refine ⟨101211853723230789705654323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67474569148820526470436215 101211853723230789705654323)
    ·
      refine ⟨151817780584846184558481485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101211853723230789705654323 151817780584846184558481485)
      ·
        refine ⟨56931667719317319209430557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151817780584846184558481485 56931667719317319209430557)
        ·
          refine ⟨21349375394743994703536459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56931667719317319209430557 21349375394743994703536459)
          ·
            refine ⟨32024063092115992055304689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21349375394743994703536459 32024063092115992055304689)
            ·
              refine ⟨24018047319086994041478517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32024063092115992055304689 24018047319086994041478517)
              ·
                refine ⟨2251691936164405691388611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24018047319086994041478517 2251691936164405691388611)
                ·
                  refine ⟨3377537904246608537082917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251691936164405691388611 3377537904246608537082917)
                  ·
                    refine ⟨633288357046239100703047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377537904246608537082917 633288357046239100703047)
                    ·
                      rfl

theorem cell22_1849987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 4].length) (baseStart_1849987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1849987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1849987 prefixEnd_1849987 := by exact prefixLift 1849987
  have htrace : WordTrace (prefixWord ++ tailWord_1849987) baseStart_1849987 baseEnd_1849987 := by
    simpa [prefixWord, tailWord_1849987, baseEnd_1849987] using wordTrace_append hprefix tailTrace_1849987
  have hstable : (prefixWord ++ tailWord_1849987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849987).length < 2 ^ (prefixWord ++ tailWord_1849987).sum := by decide
  have hdescent : baseEnd_1849987 < baseStart_1849987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850004 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1850004 : Nat := 118140960795 + 1850004 * 2 ^ 59
def prefixEnd_1850004 : Nat := 4983230072969 + 3 ^ 40 * 1850004 * 2
def baseEnd_1850004 : Nat := 633294176493656723027995

theorem tailTrace_1850004 : CollatzResearch.WordTrace tailWord_1850004 prefixEnd_1850004 633294176493656723027995 := by
  unfold tailWord_1850004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737594594879469186902533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44983459459839292249203377 33737594594879469186902533)
  ·
    refine ⟨6325798986539900472544225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33737594594879469186902533 6325798986539900472544225)
    ·
      refine ⟨4744349239904925354408169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6325798986539900472544225 4744349239904925354408169)
      ·
        refine ⟨3558261929928694015806127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4744349239904925354408169 3558261929928694015806127)
        ·
          refine ⟨5337392894893041023709191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558261929928694015806127 5337392894893041023709191)
          ·
            refine ⟨8006089342339561535563787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337392894893041023709191 8006089342339561535563787)
            ·
              refine ⟨12009134013509342303345681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006089342339561535563787 12009134013509342303345681)
              ·
                refine ⟨9006850510132006727509261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12009134013509342303345681 9006850510132006727509261)
                ·
                  refine ⟨3377568941299502522815973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9006850510132006727509261 3377568941299502522815973)
                  ·
                    refine ⟨633294176493656723027995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377568941299502522815973 633294176493656723027995)
                    ·
                      rfl

theorem cell22_1850004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1850004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850004 prefixEnd_1850004 := by exact prefixLift 1850004
  have htrace : WordTrace (prefixWord ++ tailWord_1850004) baseStart_1850004 baseEnd_1850004 := by
    simpa [prefixWord, tailWord_1850004, baseEnd_1850004] using wordTrace_append hprefix tailTrace_1850004
  have hstable : (prefixWord ++ tailWord_1850004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850004).length < 2 ^ (prefixWord ++ tailWord_1850004).sum := by decide
  have hdescent : baseEnd_1850004 < baseStart_1850004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850038 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1850038 : Nat := 118140960795 + 1850038 * 2 ^ 59
def prefixEnd_1850038 : Nat := 4983230072969 + 3 ^ 40 * 1850038 * 2
def baseEnd_1850038 : Nat := 633305815388491967677891

theorem tailTrace_1850038 : CollatzResearch.WordTrace tailWord_1850038 prefixEnd_1850038 633305815388491967677891 := by
  unfold tailWord_1850038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217276829477235136283923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44984286181090508120361845 4217276829477235136283923)
  ·
    refine ⟨6325915244215852704425885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4217276829477235136283923 6325915244215852704425885)
    ·
      refine ⟨2372218216580944764159707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6325915244215852704425885 2372218216580944764159707)
      ·
        refine ⟨3558327324871417146239561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372218216580944764159707 3558327324871417146239561)
        ·
          refine ⟨2668745493653562859679671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3558327324871417146239561 2668745493653562859679671)
          ·
            refine ⟨4003118240480344289519507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668745493653562859679671 4003118240480344289519507)
            ·
              refine ⟨6004677360720516434279261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003118240480344289519507 6004677360720516434279261)
              ·
                refine ⟨2251754010270193662854723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6004677360720516434279261 2251754010270193662854723)
                ·
                  refine ⟨3377631015405290494282085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251754010270193662854723 3377631015405290494282085)
                  ·
                    refine ⟨633305815388491967677891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377631015405290494282085 633305815388491967677891)
                    ·
                      rfl

theorem cell22_1850038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1850038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850038 prefixEnd_1850038 := by exact prefixLift 1850038
  have htrace : WordTrace (prefixWord ++ tailWord_1850038) baseStart_1850038 baseEnd_1850038 := by
    simpa [prefixWord, tailWord_1850038, baseEnd_1850038] using wordTrace_append hprefix tailTrace_1850038
  have hstable : (prefixWord ++ tailWord_1850038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850038).length < 2 ^ (prefixWord ++ tailWord_1850038).sum := by decide
  have hdescent : baseEnd_1850038 < baseStart_1850038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850068 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_1850068 : Nat := 118140960795 + 1850068 * 2 ^ 59
def prefixEnd_1850068 : Nat := 4983230072969 + 3 ^ 40 * 1850068 * 2
def baseEnd_1850068 : Nat := 633316085001581889427799

theorem tailTrace_1850068 : CollatzResearch.WordTrace tailWord_1850068 prefixEnd_1850068 633316085001581889427799 := by
  unfold tailWord_1850068
  simp only [CollatzResearch.WordTrace]
  refine ⟨33738761730763538652067429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44985015641018051536089905 33738761730763538652067429)
  ·
    refine ⟨6326017824518163497262643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33738761730763538652067429 6326017824518163497262643)
    ·
      refine ⟨9489026736777245245893965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326017824518163497262643 9489026736777245245893965)
      ·
        refine ⟨3558385026291466967210237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9489026736777245245893965 3558385026291466967210237)
        ·
          refine ⟨1334394384859300112703839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3558385026291466967210237 1334394384859300112703839)
          ·
            refine ⟨2001591577288950169055759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334394384859300112703839 2001591577288950169055759)
            ·
              refine ⟨3002387365933425253583639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001591577288950169055759 3002387365933425253583639)
              ·
                refine ⟨4503581048900137880375459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002387365933425253583639 4503581048900137880375459)
                ·
                  refine ⟨6755371573350206820563189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503581048900137880375459 6755371573350206820563189)
                  ·
                    refine ⟨633316085001581889427799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6755371573350206820563189 633316085001581889427799)
                    ·
                      rfl

theorem cell22_1850068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_1850068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850068 prefixEnd_1850068 := by exact prefixLift 1850068
  have htrace : WordTrace (prefixWord ++ tailWord_1850068) baseStart_1850068 baseEnd_1850068 := by
    simpa [prefixWord, tailWord_1850068, baseEnd_1850068] using wordTrace_append hprefix tailTrace_1850068
  have hstable : (prefixWord ++ tailWord_1850068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850068).length < 2 ^ (prefixWord ++ tailWord_1850068).sum := by decide
  have hdescent : baseEnd_1850068 < baseStart_1850068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850079 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 3, 3]
def baseStart_1850079 : Nat := 118140960795 + 1850079 * 2 ^ 59
def prefixEnd_1850079 : Nat := 4983230072969 + 3 ^ 40 * 1850079 * 2
def baseEnd_1850079 : Nat := 633319850526381527402765

theorem tailTrace_1850079 : CollatzResearch.WordTrace tailWord_1850079 prefixEnd_1850079 633319850526381527402765 := by
  unfold tailWord_1850079
  simp only [CollatzResearch.WordTrace]
  refine ⟨67477924664487226182785291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44985283109658150788523527 67477924664487226182785291)
  ·
    refine ⟨101216886996730839274177937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67477924664487226182785291 101216886996730839274177937)
    ·
      refine ⟨75912665247548129455633453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101216886996730839274177937 75912665247548129455633453)
      ·
        refine ⟨28467249467830548545862545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75912665247548129455633453 28467249467830548545862545)
        ·
          refine ⟨21350437100872911409396909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28467249467830548545862545 21350437100872911409396909)
          ·
            refine ⟨8006413912827341778523841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21350437100872911409396909 8006413912827341778523841)
            ·
              refine ⟨6004810434620506333892881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8006413912827341778523841 6004810434620506333892881)
              ·
                refine ⟨4503607825965379750419661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6004810434620506333892881 4503607825965379750419661)
                ·
                  refine ⟨1688852934737017406407373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4503607825965379750419661 1688852934737017406407373)
                  ·
                    refine ⟨633319850526381527402765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688852934737017406407373 633319850526381527402765)
                    ·
                      rfl

theorem cell22_1850079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_1850079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850079 prefixEnd_1850079 := by exact prefixLift 1850079
  have htrace : WordTrace (prefixWord ++ tailWord_1850079) baseStart_1850079 baseEnd_1850079 := by
    simpa [prefixWord, tailWord_1850079, baseEnd_1850079] using wordTrace_append hprefix tailTrace_1850079
  have hstable : (prefixWord ++ tailWord_1850079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850079).length < 2 ^ (prefixWord ++ tailWord_1850079).sum := by decide
  have hdescent : baseEnd_1850079 < baseStart_1850079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850156 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_1850156 : Nat := 118140960795 + 1850156 * 2 ^ 59
def prefixEnd_1850156 : Nat := 4983230072969 + 3 ^ 40 * 1850156 * 2
def baseEnd_1850156 : Nat := 633346209199978993227529

theorem tailTrace_1850156 : CollatzResearch.WordTrace tailWord_1850156 prefixEnd_1850156 633346209199978993227529 := by
  unfold tailWord_1850156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33740366542604134166669161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44987155390138845555558881 33740366542604134166669161)
  ·
    refine ⟨25305274906953100625001871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33740366542604134166669161 25305274906953100625001871)
    ·
      refine ⟨37957912360429650937502807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25305274906953100625001871 37957912360429650937502807)
      ·
        refine ⟨56936868540644476406254211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37957912360429650937502807 56936868540644476406254211)
        ·
          refine ⟨85405302810966714609381317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56936868540644476406254211 85405302810966714609381317)
          ·
            refine ⟨16013494277056258989258997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85405302810966714609381317 16013494277056258989258997)
            ·
              refine ⟨1501265088474024280243031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16013494277056258989258997 1501265088474024280243031)
              ·
                refine ⟨2251897632711036420364547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501265088474024280243031 2251897632711036420364547)
                ·
                  refine ⟨3377846449066554630546821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251897632711036420364547 3377846449066554630546821)
                  ·
                    refine ⟨633346209199978993227529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377846449066554630546821 633346209199978993227529)
                    ·
                      rfl

theorem cell22_1850156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_1850156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850156 prefixEnd_1850156 := by exact prefixLift 1850156
  have htrace : WordTrace (prefixWord ++ tailWord_1850156) baseStart_1850156 baseEnd_1850156 := by
    simpa [prefixWord, tailWord_1850156, baseEnd_1850156] using wordTrace_append hprefix tailTrace_1850156
  have hstable : (prefixWord ++ tailWord_1850156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850156).length < 2 ^ (prefixWord ++ tailWord_1850156).sum := by decide
  have hdescent : baseEnd_1850156 < baseStart_1850156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850164 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1850164 : Nat := 118140960795 + 1850164 * 2 ^ 59
def prefixEnd_1850164 : Nat := 4983230072969 + 3 ^ 40 * 1850164 * 2
def baseEnd_1850164 : Nat := 633348947763469639027505

theorem tailTrace_1850164 : CollatzResearch.WordTrace tailWord_1850164 prefixEnd_1850164 633348947763469639027505 := by
  unfold tailWord_1850164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33740512434589642849814773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44987349912786190466419697 33740512434589642849814773)
  ·
    refine ⟨3163173040742779017170135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33740512434589642849814773 3163173040742779017170135)
    ·
      refine ⟨4744759561114168525755203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163173040742779017170135 4744759561114168525755203)
      ·
        refine ⟨7117139341671252788632805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4744759561114168525755203 7117139341671252788632805)
        ·
          refine ⟨1334463626563359897868651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7117139341671252788632805 1334463626563359897868651)
          ·
            refine ⟨2001695439845039846802977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334463626563359897868651 2001695439845039846802977)
            ·
              refine ⟨1501271579883779885102233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001695439845039846802977 1501271579883779885102233)
              ·
                refine ⟨1125953684912834913826675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501271579883779885102233 1125953684912834913826675)
                ·
                  refine ⟨1688930527369252370740013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125953684912834913826675 1688930527369252370740013)
                  ·
                    refine ⟨633348947763469639027505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688930527369252370740013 633348947763469639027505)
                    ·
                      rfl

theorem cell22_1850164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1850164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850164 prefixEnd_1850164 := by exact prefixLift 1850164
  have htrace : WordTrace (prefixWord ++ tailWord_1850164) baseStart_1850164 baseEnd_1850164 := by
    simpa [prefixWord, tailWord_1850164, baseEnd_1850164] using wordTrace_append hprefix tailTrace_1850164
  have hstable : (prefixWord ++ tailWord_1850164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850164).length < 2 ^ (prefixWord ++ tailWord_1850164).sum := by decide
  have hdescent : baseEnd_1850164 < baseStart_1850164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850201 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_1850201 : Nat := 118140960795 + 1850201 * 2 ^ 59
def prefixEnd_1850201 : Nat := 4983230072969 + 3 ^ 40 * 1850201 * 2
def baseEnd_1850201 : Nat := 633361613619613875852391

theorem tailTrace_1850201 : CollatzResearch.WordTrace tailWord_1850201 prefixEnd_1850201 633361613619613875852391 := by
  unfold tailWord_1850201
  simp only [CollatzResearch.WordTrace]
  refine ⟨67482374370045241018726457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44988249580030160679150971 67482374370045241018726457)
  ·
    refine ⟨50611780777533930764044843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67482374370045241018726457 50611780777533930764044843)
    ·
      refine ⟨75917671166300896146067265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50611780777533930764044843 75917671166300896146067265)
      ·
        refine ⟨56938253374725672109550449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75917671166300896146067265 56938253374725672109550449)
        ·
          refine ⟨42703690031044254082162837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56938253374725672109550449 42703690031044254082162837)
          ·
            refine ⟨2001735470205199410101383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42703690031044254082162837 2001735470205199410101383)
            ·
              refine ⟨3002603205307799115152075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001735470205199410101383 3002603205307799115152075)
              ·
                refine ⟨4503904807961698672728113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002603205307799115152075 4503904807961698672728113)
                ·
                  refine ⟨3377928605971274004546085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4503904807961698672728113 3377928605971274004546085)
                  ·
                    refine ⟨633361613619613875852391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377928605971274004546085 633361613619613875852391)
                    ·
                      rfl

theorem cell22_1850201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_1850201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850201 prefixEnd_1850201 := by exact prefixLift 1850201
  have htrace : WordTrace (prefixWord ++ tailWord_1850201) baseStart_1850201 baseEnd_1850201 := by
    simpa [prefixWord, tailWord_1850201, baseEnd_1850201] using wordTrace_append hprefix tailTrace_1850201
  have hstable : (prefixWord ++ tailWord_1850201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850201).length < 2 ^ (prefixWord ++ tailWord_1850201).sum := by decide
  have hdescent : baseEnd_1850201 < baseStart_1850201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850325 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_1850325 : Nat := 118140960795 + 1850325 * 2 ^ 59
def prefixEnd_1850325 : Nat := 4983230072969 + 3 ^ 40 * 1850325 * 2
def baseEnd_1850325 : Nat := 633404061353718885752011

theorem tailTrace_1850325 : CollatzResearch.WordTrace tailWord_1850325 prefixEnd_1850325 633404061353718885752011 := by
  unfold tailWord_1850325
  simp only [CollatzResearch.WordTrace]
  refine ⟨67486897021596010196240429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44991264681064006797493619 67486897021596010196240429)
  ·
    refine ⟨25307586383098503823590161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67486897021596010196240429 25307586383098503823590161)
    ·
      refine ⟨18980689787323877867692621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25307586383098503823590161 18980689787323877867692621)
      ·
        refine ⟨7117758670246454200384733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18980689787323877867692621 7117758670246454200384733)
        ·
          refine ⟨2669159501342420325144275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7117758670246454200384733 2669159501342420325144275)
          ·
            refine ⟨4003739252013630487716413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669159501342420325144275 4003739252013630487716413)
            ·
              refine ⟨1501402219505111432893655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4003739252013630487716413 1501402219505111432893655)
              ·
                refine ⟨2252103329257667149340483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501402219505111432893655 2252103329257667149340483)
                ·
                  refine ⟨3378154993886500724010725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252103329257667149340483 3378154993886500724010725)
                  ·
                    refine ⟨633404061353718885752011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378154993886500724010725 633404061353718885752011)
                    ·
                      rfl

theorem cell22_1850325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_1850325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850325 prefixEnd_1850325 := by exact prefixLift 1850325
  have htrace : WordTrace (prefixWord ++ tailWord_1850325) baseStart_1850325 baseEnd_1850325 := by
    simpa [prefixWord, tailWord_1850325, baseEnd_1850325] using wordTrace_append hprefix tailTrace_1850325
  have hstable : (prefixWord ++ tailWord_1850325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850325).length < 2 ^ (prefixWord ++ tailWord_1850325).sum := by decide
  have hdescent : baseEnd_1850325 < baseStart_1850325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850351 : List Nat := [1, 1, 2, 1, 4, 5, 1, 7]
def baseStart_1850351 : Nat := 118140960795 + 1850351 * 2 ^ 59
def prefixEnd_1850351 : Nat := 4983230072969 + 3 ^ 40 * 1850351 * 2
def baseEnd_1850351 : Nat := 70379217965007053844659

theorem tailTrace_1850351 : CollatzResearch.WordTrace tailWord_1850351 prefixEnd_1850351 70379217965007053844659 := by
  unfold tailWord_1850351
  simp only [CollatzResearch.WordTrace]
  refine ⟨67487845319501816636686907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44991896879667877757791271 67487845319501816636686907)
  ·
    refine ⟨101231767979252724955030361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67487845319501816636686907 101231767979252724955030361)
    ·
      refine ⟨75923825984439543716272771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101231767979252724955030361 75923825984439543716272771)
      ·
        refine ⟨113885738976659315574409157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75923825984439543716272771 113885738976659315574409157)
        ·
          refine ⟨21353576058123621670201717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113885738976659315574409157 21353576058123621670201717)
          ·
            refine ⟨2001897755449089531581411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21353576058123621670201717 2001897755449089531581411)
            ·
              refine ⟨3002846633173634297372117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001897755449089531581411 3002846633173634297372117)
              ·
                refine ⟨70379217965007053844659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3002846633173634297372117 70379217965007053844659)
                ·
                  rfl

theorem cell22_1850351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 7].length) (baseStart_1850351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850351 prefixEnd_1850351 := by exact prefixLift 1850351
  have htrace : WordTrace (prefixWord ++ tailWord_1850351) baseStart_1850351 baseEnd_1850351 := by
    simpa [prefixWord, tailWord_1850351, baseEnd_1850351] using wordTrace_append hprefix tailTrace_1850351
  have hstable : (prefixWord ++ tailWord_1850351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850351).length < 2 ^ (prefixWord ++ tailWord_1850351).sum := by decide
  have hdescent : baseEnd_1850351 < baseStart_1850351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850370 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1850370 : Nat := 118140960795 + 1850370 * 2 ^ 59
def prefixEnd_1850370 : Nat := 4983230072969 + 3 ^ 40 * 1850370 * 2
def baseEnd_1850370 : Nat := 633419465773353768376873

theorem tailTrace_1850370 : CollatzResearch.WordTrace tailWord_1850370 prefixEnd_1850370 633419465773353768376873 := by
  unfold tailWord_1850370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16872134576608245720407141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44992358870955321921085709 16872134576608245720407141)
  ·
    refine ⟨3163525233114046072576339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16872134576608245720407141 3163525233114046072576339)
    ·
      refine ⟨4745287849671069108864509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163525233114046072576339 4745287849671069108864509)
      ·
        refine ⟨1779482943626650915824191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4745287849671069108864509 1779482943626650915824191)
        ·
          refine ⟨2669224415439976373736287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779482943626650915824191 2669224415439976373736287)
          ·
            refine ⟨4003836623159964560604431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669224415439976373736287 4003836623159964560604431)
            ·
              refine ⟨6005754934739946840906647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003836623159964560604431 6005754934739946840906647)
              ·
                refine ⟨9008632402109920261359971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6005754934739946840906647 9008632402109920261359971)
                ·
                  refine ⟨13512948603164880392039957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9008632402109920261359971 13512948603164880392039957)
                  ·
                    refine ⟨633419465773353768376873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13512948603164880392039957 633419465773353768376873)
                    ·
                      rfl

theorem cell22_1850370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1850370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850370 prefixEnd_1850370 := by exact prefixLift 1850370
  have htrace : WordTrace (prefixWord ++ tailWord_1850370) baseStart_1850370 baseEnd_1850370 := by
    simpa [prefixWord, tailWord_1850370, baseEnd_1850370] using wordTrace_append hprefix tailTrace_1850370
  have hstable : (prefixWord ++ tailWord_1850370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850370).length < 2 ^ (prefixWord ++ tailWord_1850370).sum := by decide
  have hdescent : baseEnd_1850370 < baseStart_1850370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850426 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_1850426 : Nat := 118140960795 + 1850426 * 2 ^ 59
def prefixEnd_1850426 : Nat := 4983230072969 + 3 ^ 40 * 1850426 * 2
def baseEnd_1850426 : Nat := 633438635717788288976701

theorem tailTrace_1850426 : CollatzResearch.WordTrace tailWord_1850426 prefixEnd_1850426 633438635717788288976701 := by
  unfold tailWord_1850426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16872645198557526111416783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44993720529486736297111421 16872645198557526111416783)
  ·
    refine ⟨25308967797836289167125175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16872645198557526111416783 25308967797836289167125175)
    ·
      refine ⟨37963451696754433750687763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25308967797836289167125175 37963451696754433750687763)
      ·
        refine ⟨56945177545131650626031645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37963451696754433750687763 56945177545131650626031645)
        ·
          refine ⟨21354441579424368984761867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56945177545131650626031645 21354441579424368984761867)
          ·
            refine ⟨32031662369136553477142801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21354441579424368984761867 32031662369136553477142801)
            ·
              refine ⟨24023746776852415107857101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32031662369136553477142801 24023746776852415107857101)
              ·
                refine ⟨9008905041319655665446413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24023746776852415107857101 9008905041319655665446413)
                ·
                  refine ⟨3378339390494870874542405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9008905041319655665446413 3378339390494870874542405)
                  ·
                    refine ⟨633438635717788288976701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378339390494870874542405 633438635717788288976701)
                    ·
                      rfl

theorem cell22_1850426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_1850426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850426 prefixEnd_1850426 := by exact prefixLift 1850426
  have htrace : WordTrace (prefixWord ++ tailWord_1850426) baseStart_1850426 baseEnd_1850426 := by
    simpa [prefixWord, tailWord_1850426, baseEnd_1850426] using wordTrace_append hprefix tailTrace_1850426
  have hstable : (prefixWord ++ tailWord_1850426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850426).length < 2 ^ (prefixWord ++ tailWord_1850426).sum := by decide
  have hdescent : baseEnd_1850426 < baseStart_1850426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850535 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1850535 : Nat := 118140960795 + 1850535 * 2 ^ 59
def prefixEnd_1850535 : Nat := 4983230072969 + 3 ^ 40 * 1850535 * 2
def baseEnd_1850535 : Nat := 633475948645348338001367

theorem tailTrace_1850535 : CollatzResearch.WordTrace tailWord_1850535 prefixEnd_1850535 633475948645348338001367 := by
  unfold tailWord_1850535
  simp only [CollatzResearch.WordTrace]
  refine ⟨67494556350835216061385059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44996370900556810707590039 67494556350835216061385059)
  ·
    refine ⟨101241834526252824092077589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67494556350835216061385059 101241834526252824092077589)
    ·
      refine ⟨4745710993418101129316137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101241834526252824092077589 4745710993418101129316137)
      ·
        refine ⟨3559283245063575846987103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4745710993418101129316137 3559283245063575846987103)
        ·
          refine ⟨5338924867595363770480655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559283245063575846987103 5338924867595363770480655)
          ·
            refine ⟨8008387301393045655720983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338924867595363770480655 8008387301393045655720983)
            ·
              refine ⟨12012580952089568483581475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008387301393045655720983 12012580952089568483581475)
              ·
                refine ⟨18018871428134352725372213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012580952089568483581475 18018871428134352725372213)
                ·
                  refine ⟨1689269196387595568003645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18018871428134352725372213 1689269196387595568003645)
                  ·
                    refine ⟨633475948645348338001367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689269196387595568003645 633475948645348338001367)
                    ·
                      rfl

theorem cell22_1850535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1850535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850535 prefixEnd_1850535 := by exact prefixLift 1850535
  have htrace : WordTrace (prefixWord ++ tailWord_1850535) baseStart_1850535 baseEnd_1850535 := by
    simpa [prefixWord, tailWord_1850535, baseEnd_1850535] using wordTrace_append hprefix tailTrace_1850535
  have hstable : (prefixWord ++ tailWord_1850535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850535).length < 2 ^ (prefixWord ++ tailWord_1850535).sum := by decide
  have hdescent : baseEnd_1850535 < baseStart_1850535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850593 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 6]
def baseStart_1850593 : Nat := 118140960795 + 1850593 * 2 ^ 59
def prefixEnd_1850593 : Nat := 4983230072969 + 3 ^ 40 * 1850593 * 2
def baseEnd_1850593 : Nat := 211165267743551840017063

theorem tailTrace_1850593 : CollatzResearch.WordTrace tailWord_1850593 prefixEnd_1850593 211165267743551840017063 := by
  unfold tailWord_1850593
  simp only [CollatzResearch.WordTrace]
  refine ⟨67496671784625091966996433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44997781189750061311330955 67496671784625091966996433)
  ·
    refine ⟨50622503838468818975247325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67496671784625091966996433 50622503838468818975247325)
    ·
      refine ⟨18983438939425807115717747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50622503838468818975247325 18983438939425807115717747)
      ·
        refine ⟨28475158409138710673576621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18983438939425807115717747 28475158409138710673576621)
        ·
          refine ⟨10678184403427016502591233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28475158409138710673576621 10678184403427016502591233)
          ·
            refine ⟨8008638302570262376943425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10678184403427016502591233 8008638302570262376943425)
            ·
              refine ⟨6006478726927696782707569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8008638302570262376943425 6006478726927696782707569)
              ·
                refine ⟨4504859045195772587030677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6006478726927696782707569 4504859045195772587030677)
                ·
                  refine ⟨211165267743551840017063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4504859045195772587030677 211165267743551840017063)
                  ·
                    rfl

theorem cell22_1850593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_1850593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850593 prefixEnd_1850593 := by exact prefixLift 1850593
  have htrace : WordTrace (prefixWord ++ tailWord_1850593) baseStart_1850593 baseEnd_1850593 := by
    simpa [prefixWord, tailWord_1850593, baseEnd_1850593] using wordTrace_append hprefix tailTrace_1850593
  have hstable : (prefixWord ++ tailWord_1850593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850593).length < 2 ^ (prefixWord ++ tailWord_1850593).sum := by decide
  have hdescent : baseEnd_1850593 < baseStart_1850593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850623 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 4, 4]
def baseStart_1850623 : Nat := 118140960795 + 1850623 * 2 ^ 59
def prefixEnd_1850623 : Nat := 4983230072969 + 3 ^ 40 * 1850623 * 2
def baseEnd_1850623 : Nat := 633506072843745441801097

theorem tailTrace_1850623 : CollatzResearch.WordTrace tailWord_1850623 prefixEnd_1850623 633506072843745441801097 := by
  unfold tailWord_1850623
  simp only [CollatzResearch.WordTrace]
  refine ⟨67497765974516407090588523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44998510649677604727059015 67497765974516407090588523)
  ·
    refine ⟨101246648961774610635882785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67497765974516407090588523 101246648961774610635882785)
    ·
      refine ⟨75934986721330957976912089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101246648961774610635882785 75934986721330957976912089)
      ·
        refine ⟨56951240040998218482684067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75934986721330957976912089 56951240040998218482684067)
        ·
          refine ⟨85426860061497327724026101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56951240040998218482684067 85426860061497327724026101)
          ·
            refine ⟨8008768130765374474127447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85426860061497327724026101 8008768130765374474127447)
            ·
              refine ⟨12013152196148061711191171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008768130765374474127447 12013152196148061711191171)
              ·
                refine ⟨18019728294222092566786757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12013152196148061711191171 18019728294222092566786757)
                ·
                  refine ⟨3378699055166642356272517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18019728294222092566786757 3378699055166642356272517)
                  ·
                    refine ⟨633506072843745441801097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378699055166642356272517 633506072843745441801097)
                    ·
                      rfl

theorem cell22_1850623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_1850623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850623 prefixEnd_1850623 := by exact prefixLift 1850623
  have htrace : WordTrace (prefixWord ++ tailWord_1850623) baseStart_1850623 baseEnd_1850623 := by
    simpa [prefixWord, tailWord_1850623, baseEnd_1850623] using wordTrace_append hprefix tailTrace_1850623
  have hstable : (prefixWord ++ tailWord_1850623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850623).length < 2 ^ (prefixWord ++ tailWord_1850623).sum := by decide
  have hdescent : baseEnd_1850623 < baseStart_1850623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850625 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1850625 : Nat := 118140960795 + 1850625 * 2 ^ 59
def prefixEnd_1850625 : Nat := 4983230072969 + 3 ^ 40 * 1850625 * 2
def baseEnd_1850625 : Nat := 633506757484618103251091

theorem tailTrace_1850625 : CollatzResearch.WordTrace tailWord_1850625 prefixEnd_1850625 633506757484618103251091 := by
  unfold tailWord_1850625
  simp only [CollatzResearch.WordTrace]
  refine ⟨67497838920509161432161329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44998559280339440954774219 67497838920509161432161329)
  ·
    refine ⟨50623379190381871074120997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67497838920509161432161329 50623379190381871074120997)
    ·
      refine ⟨9491883598196600826397687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50623379190381871074120997 9491883598196600826397687)
      ·
        refine ⟨14237825397294901239596531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491883598196600826397687 14237825397294901239596531)
        ·
          refine ⟨21356738095942351859394797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237825397294901239596531 21356738095942351859394797)
          ·
            refine ⟨8008776785978381947273049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21356738095942351859394797 8008776785978381947273049)
            ·
              refine ⟨6006582589483786460454787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8008776785978381947273049 6006582589483786460454787)
              ·
                refine ⟨9009873884225679690682181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006582589483786460454787 9009873884225679690682181)
                ·
                  refine ⟨1689351353292314942002909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9009873884225679690682181 1689351353292314942002909)
                  ·
                    refine ⟨633506757484618103251091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689351353292314942002909 633506757484618103251091)
                    ·
                      rfl

theorem cell22_1850625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1850625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850625 prefixEnd_1850625 := by exact prefixLift 1850625
  have htrace : WordTrace (prefixWord ++ tailWord_1850625) baseStart_1850625 baseEnd_1850625 := by
    simpa [prefixWord, tailWord_1850625, baseEnd_1850625] using wordTrace_append hprefix tailTrace_1850625
  have hstable : (prefixWord ++ tailWord_1850625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850625).length < 2 ^ (prefixWord ++ tailWord_1850625).sum := by decide
  have hdescent : baseEnd_1850625 < baseStart_1850625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850627 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 4]
def baseStart_1850627 : Nat := 118140960795 + 1850627 * 2 ^ 59
def prefixEnd_1850627 : Nat := 4983230072969 + 3 ^ 40 * 1850627 * 2
def baseEnd_1850627 : Nat := 211169147375163588233695

theorem tailTrace_1850627 : CollatzResearch.WordTrace tailWord_1850627 prefixEnd_1850627 211169147375163588233695 := by
  unfold tailWord_1850627
  simp only [CollatzResearch.WordTrace]
  refine ⟨67497911866501915773734135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44998607911001277182489423 67497911866501915773734135)
  ·
    refine ⟨101246867799752873660601203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67497911866501915773734135 101246867799752873660601203)
    ·
      refine ⟨151870301699629310490901805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101246867799752873660601203 151870301699629310490901805)
      ·
        refine ⟨56951363137360991434088177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151870301699629310490901805 56951363137360991434088177)
        ·
          refine ⟨42713522353020743575566133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56951363137360991434088177 42713522353020743575566133)
          ·
            refine ⟨4004392720595694710209325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42713522353020743575566133 4004392720595694710209325)
            ·
              refine ⟨1501647270223385516328497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4004392720595694710209325 1501647270223385516328497)
              ·
                refine ⟨1126235452667539137246373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501647270223385516328497 1126235452667539137246373)
                ·
                  refine ⟨211169147375163588233695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126235452667539137246373 211169147375163588233695)
                  ·
                    rfl

theorem cell22_1850627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 4].length) (baseStart_1850627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850627 prefixEnd_1850627 := by exact prefixLift 1850627
  have htrace : WordTrace (prefixWord ++ tailWord_1850627) baseStart_1850627 baseEnd_1850627 := by
    simpa [prefixWord, tailWord_1850627, baseEnd_1850627] using wordTrace_append hprefix tailTrace_1850627
  have hstable : (prefixWord ++ tailWord_1850627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850627).length < 2 ^ (prefixWord ++ tailWord_1850627).sum := by decide
  have hdescent : baseEnd_1850627 < baseStart_1850627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850638 : List Nat := [4, 1, 1, 2, 1, 3, 1, 9]
def baseStart_1850638 : Nat := 118140960795 + 1850638 * 2 ^ 59
def prefixEnd_1850638 : Nat := 4983230072969 + 3 ^ 40 * 1850638 * 2
def baseEnd_1850638 : Nat := 70390134183365600297339

theorem tailTrace_1850638 : CollatzResearch.WordTrace tailWord_1850638 prefixEnd_1850638 70390134183365600297339 := by
  unfold tailWord_1850638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437289133682758081548071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44998875379641376434923045 8437289133682758081548071)
  ·
    refine ⟨12655933700524137122322107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8437289133682758081548071 12655933700524137122322107)
    ·
      refine ⟨18983900550786205683483161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12655933700524137122322107 18983900550786205683483161)
      ·
        refine ⟨14237925413089654262612371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18983900550786205683483161 14237925413089654262612371)
        ·
          refine ⟨21356888119634481393918557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237925413089654262612371 21356888119634481393918557)
          ·
            refine ⟨8008833044862930522719459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21356888119634481393918557 8008833044862930522719459)
            ·
              refine ⟨12013249567294395784079189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008833044862930522719459 12013249567294395784079189)
              ·
                refine ⟨70390134183365600297339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12013249567294395784079189 70390134183365600297339)
                ·
                  rfl

theorem cell22_1850638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_1850638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850638 prefixEnd_1850638 := by exact prefixLift 1850638
  have htrace : WordTrace (prefixWord ++ tailWord_1850638) baseStart_1850638 baseEnd_1850638 := by
    simpa [prefixWord, tailWord_1850638, baseEnd_1850638] using wordTrace_append hprefix tailTrace_1850638
  have hstable : (prefixWord ++ tailWord_1850638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850638).length < 2 ^ (prefixWord ++ tailWord_1850638).sum := by decide
  have hdescent : baseEnd_1850638 < baseStart_1850638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850678 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1850678 : Nat := 118140960795 + 1850678 * 2 ^ 59
def prefixEnd_1850678 : Nat := 4983230072969 + 3 ^ 40 * 1850678 * 2
def baseEnd_1850678 : Nat := 211174966822581210558643

theorem tailTrace_1850678 : CollatzResearch.WordTrace tailWord_1850678 prefixEnd_1850678 211174966822581210558643 := by
  unfold tailWord_1850678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218735749332321967740043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44999847992878100989227125 4218735749332321967740043)
  ·
    refine ⟨6328103623998482951610065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218735749332321967740043 6328103623998482951610065)
    ·
      refine ⟨4746077717998862213707549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6328103623998482951610065 4746077717998862213707549)
      ·
        refine ⟨1779779144249573330140331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4746077717998862213707549 1779779144249573330140331)
        ·
          refine ⟨2669668716374359995210497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779779144249573330140331 2669668716374359995210497)
          ·
            refine ⟨2002251537280769996407873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2669668716374359995210497 2002251537280769996407873)
            ·
              refine ⟨1501688652960577497305905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002251537280769996407873 1501688652960577497305905)
              ·
                refine ⟨1126266489720433122979429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501688652960577497305905 1126266489720433122979429)
                ·
                  refine ⟨211174966822581210558643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126266489720433122979429 211174966822581210558643)
                  ·
                    rfl

theorem cell22_1850678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1850678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850678 prefixEnd_1850678 := by exact prefixLift 1850678
  have htrace : WordTrace (prefixWord ++ tailWord_1850678) baseStart_1850678 baseEnd_1850678 := by
    simpa [prefixWord, tailWord_1850678, baseEnd_1850678] using wordTrace_append hprefix tailTrace_1850678
  have hstable : (prefixWord ++ tailWord_1850678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850678).length < 2 ^ (prefixWord ++ tailWord_1850678).sum := by decide
  have hdescent : baseEnd_1850678 < baseStart_1850678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850700 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_1850700 : Nat := 118140960795 + 1850700 * 2 ^ 59
def prefixEnd_1850700 : Nat := 4983230072969 + 3 ^ 40 * 1850700 * 2
def baseEnd_1850700 : Nat := 211177477172447635875287

theorem tailTrace_1850700 : CollatzResearch.WordTrace tailWord_1850700 prefixEnd_1850700 211177477172447635875287 := by
  unfold tailWord_1850700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33750287197618724620570777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45000382930158299494094369 33750287197618724620570777)
  ·
    refine ⟨25312715398214043465428083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33750287197618724620570777 25312715398214043465428083)
    ·
      refine ⟨37969073097321065198142125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25312715398214043465428083 37969073097321065198142125)
      ·
        refine ⟨14238402411495399449303297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37969073097321065198142125 14238402411495399449303297)
        ·
          refine ⟨10678801808621549586977473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14238402411495399449303297 10678801808621549586977473)
          ·
            refine ⟨8009101356466162190233105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10678801808621549586977473 8009101356466162190233105)
            ·
              refine ⟨6006826017349621642674829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8009101356466162190233105 6006826017349621642674829)
              ·
                refine ⟨2252559756506108116003061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6006826017349621642674829 2252559756506108116003061)
                ·
                  refine ⟨211177477172447635875287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2252559756506108116003061 211177477172447635875287)
                  ·
                    rfl

theorem cell22_1850700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_1850700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850700 prefixEnd_1850700 := by exact prefixLift 1850700
  have htrace : WordTrace (prefixWord ++ tailWord_1850700) baseStart_1850700 baseEnd_1850700 := by
    simpa [prefixWord, tailWord_1850700, baseEnd_1850700] using wordTrace_append hprefix tailTrace_1850700
  have hstable : (prefixWord ++ tailWord_1850700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850700).length < 2 ^ (prefixWord ++ tailWord_1850700).sum := by decide
  have hdescent : baseEnd_1850700 < baseStart_1850700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850775 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1850775 : Nat := 118140960795 + 1850775 * 2 ^ 59
def prefixEnd_1850775 : Nat := 4983230072969 + 3 ^ 40 * 1850775 * 2
def baseEnd_1850775 : Nat := 633558105550067712000631

theorem tailTrace_1850775 : CollatzResearch.WordTrace tailWord_1850775 prefixEnd_1850775 633558105550067712000631 := by
  unfold tailWord_1850775
  simp only [CollatzResearch.WordTrace]
  refine ⟨67503309869965737050121779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45002206579977158033414519 67503309869965737050121779)
  ·
    refine ⟨101254964804948605575182669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67503309869965737050121779 101254964804948605575182669)
    ·
      refine ⟨37970611801855727090693501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101254964804948605575182669 37970611801855727090693501)
      ·
        refine ⟨14238979425695897659010063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37970611801855727090693501 14238979425695897659010063)
        ·
          refine ⟨21358469138543846488515095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238979425695897659010063 21358469138543846488515095)
          ·
            refine ⟨32037703707815769732772643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21358469138543846488515095 32037703707815769732772643)
            ·
              refine ⟨48056555561723654599158965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32037703707815769732772643 48056555561723654599158965)
              ·
                refine ⟨4505302083911592618671153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48056555561723654599158965 4505302083911592618671153)
                ·
                  refine ⟨3378976562933694464003365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505302083911592618671153 3378976562933694464003365)
                  ·
                    refine ⟨633558105550067712000631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378976562933694464003365 633558105550067712000631)
                    ·
                      rfl

theorem cell22_1850775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1850775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850775 prefixEnd_1850775 := by exact prefixLift 1850775
  have htrace : WordTrace (prefixWord ++ tailWord_1850775) baseStart_1850775 baseEnd_1850775 := by
    simpa [prefixWord, tailWord_1850775, baseEnd_1850775] using wordTrace_append hprefix tailTrace_1850775
  have hstable : (prefixWord ++ tailWord_1850775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850775).length < 2 ^ (prefixWord ++ tailWord_1850775).sum := by decide
  have hdescent : baseEnd_1850775 < baseStart_1850775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850869 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 5]
def baseStart_1850869 : Nat := 118140960795 + 1850869 * 2 ^ 59
def prefixEnd_1850869 : Nat := 4983230072969 + 3 ^ 40 * 1850869 * 2
def baseEnd_1850869 : Nat := 211196761223694266716781

theorem tailTrace_1850869 : CollatzResearch.WordTrace tailWord_1850869 prefixEnd_1850869 211196761223694266716781 := by
  unfold tailWord_1850869
  simp only [CollatzResearch.WordTrace]
  refine ⟨67506738331625191104043661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45004492221083460736029107 67506738331625191104043661)
  ·
    refine ⟨25315026874359446664016373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67506738331625191104043661 25315026874359446664016373)
    ·
      refine ⟨2373283769471198124751535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25315026874359446664016373 2373283769471198124751535)
      ·
        refine ⟨3559925654206797187127303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373283769471198124751535 3559925654206797187127303)
        ·
          refine ⟨5339888481310195780690955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559925654206797187127303 5339888481310195780690955)
          ·
            refine ⟨8009832721965293671036433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339888481310195780690955 8009832721965293671036433)
            ·
              refine ⟨6007374541473970253277325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8009832721965293671036433 6007374541473970253277325)
              ·
                refine ⟨2252765453052738844978997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6007374541473970253277325 2252765453052738844978997)
                ·
                  refine ⟨211196761223694266716781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2252765453052738844978997 211196761223694266716781)
                  ·
                    rfl

theorem cell22_1850869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_1850869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850869 prefixEnd_1850869 := by exact prefixLift 1850869
  have htrace : WordTrace (prefixWord ++ tailWord_1850869) baseStart_1850869 baseEnd_1850869 := by
    simpa [prefixWord, tailWord_1850869, baseEnd_1850869] using wordTrace_append hprefix tailTrace_1850869
  have hstable : (prefixWord ++ tailWord_1850869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850869).length < 2 ^ (prefixWord ++ tailWord_1850869).sum := by decide
  have hdescent : baseEnd_1850869 < baseStart_1850869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850899 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 1, 4]
def baseStart_1850899 : Nat := 118140960795 + 1850899 * 2 ^ 59
def prefixEnd_1850899 : Nat := 4983230072969 + 3 ^ 40 * 1850899 * 2
def baseEnd_1850899 : Nat := 633600553284172721900251

theorem tailTrace_1850899 : CollatzResearch.WordTrace tailWord_1850899 prefixEnd_1850899 633600553284172721900251 := by
  unfold tailWord_1850899
  simp only [CollatzResearch.WordTrace]
  refine ⟨67507832521516506227635751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45005221681011004151757167 67507832521516506227635751)
  ·
    refine ⟨101261748782274759341453627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67507832521516506227635751 101261748782274759341453627)
    ·
      refine ⟨151892623173412139012180441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101261748782274759341453627 151892623173412139012180441)
      ·
        refine ⟨113919467380059104259135331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151892623173412139012180441 113919467380059104259135331)
        ·
          refine ⟨170879201070088656388702997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113919467380059104259135331 170879201070088656388702997)
          ·
            refine ⟨8009962550160405768220453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170879201070088656388702997 8009962550160405768220453)
            ·
              refine ⟨1501867978155076081541335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8009962550160405768220453 1501867978155076081541335)
              ·
                refine ⟨2252801967232614122312003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501867978155076081541335 2252801967232614122312003)
                ·
                  refine ⟨3379202950848921183468005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252801967232614122312003 3379202950848921183468005)
                  ·
                    refine ⟨633600553284172721900251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379202950848921183468005 633600553284172721900251)
                    ·
                      rfl

theorem cell22_1850899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 4].length) (baseStart_1850899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850899 prefixEnd_1850899 := by exact prefixLift 1850899
  have htrace : WordTrace (prefixWord ++ tailWord_1850899) baseStart_1850899 baseEnd_1850899 := by
    simpa [prefixWord, tailWord_1850899, baseEnd_1850899] using wordTrace_append hprefix tailTrace_1850899
  have hstable : (prefixWord ++ tailWord_1850899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850899).length < 2 ^ (prefixWord ++ tailWord_1850899).sum := by decide
  have hdescent : baseEnd_1850899 < baseStart_1850899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850914 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1850914 : Nat := 118140960795 + 1850914 * 2 ^ 59
def prefixEnd_1850914 : Nat := 4983230072969 + 3 ^ 40 * 1850914 * 2
def baseEnd_1850914 : Nat := 211201896030239227591735

theorem tailTrace_1850914 : CollatzResearch.WordTrace tailWord_1850914 prefixEnd_1850914 211201896030239227591735 := by
  unfold tailWord_1850914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877094904115540947357949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45005586410974775859621197 16877094904115540947357949)
  ·
    refine ⟨6328910589043327855259231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16877094904115540947357949 6328910589043327855259231)
    ·
      refine ⟨9493365883564991782888847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6328910589043327855259231 9493365883564991782888847)
      ·
        refine ⟨14240048825347487674333271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493365883564991782888847 14240048825347487674333271)
        ·
          refine ⟨21360073238021231511499907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240048825347487674333271 21360073238021231511499907)
          ·
            refine ⟨32040109857031847267249861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21360073238021231511499907 32040109857031847267249861)
            ·
              refine ⟨6007520598193471362609349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32040109857031847267249861 6007520598193471362609349)
              ·
                refine ⟨1126410112161275880489253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6007520598193471362609349 1126410112161275880489253)
                ·
                  refine ⟨211201896030239227591735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126410112161275880489253 211201896030239227591735)
                  ·
                    rfl

theorem cell22_1850914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1850914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850914 prefixEnd_1850914 := by exact prefixLift 1850914
  have htrace : WordTrace (prefixWord ++ tailWord_1850914) baseStart_1850914 baseEnd_1850914 := by
    simpa [prefixWord, tailWord_1850914, baseEnd_1850914] using wordTrace_append hprefix tailTrace_1850914
  have hstable : (prefixWord ++ tailWord_1850914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850914).length < 2 ^ (prefixWord ++ tailWord_1850914).sum := by decide
  have hdescent : baseEnd_1850914 < baseStart_1850914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850955 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_1850955 : Nat := 118140960795 + 1850955 * 2 ^ 59
def prefixEnd_1850955 : Nat := 4983230072969 + 3 ^ 40 * 1850955 * 2
def baseEnd_1850955 : Nat := 633619723228607242500079

theorem tailTrace_1850955 : CollatzResearch.WordTrace tailWord_1850955 prefixEnd_1850955 633619723228607242500079 := by
  unfold tailWord_1850955
  simp only [CollatzResearch.WordTrace]
  refine ⟨67509875009313627791674319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45006583339542418527782879 67509875009313627791674319)
  ·
    refine ⟨101264812513970441687511479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67509875009313627791674319 101264812513970441687511479)
    ·
      refine ⟨151897218770955662531267219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101264812513970441687511479 151897218770955662531267219)
      ·
        refine ⟨227845828156433493796900829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151897218770955662531267219 227845828156433493796900829)
        ·
          refine ⟨85442185558662560173837811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227845828156433493796900829 85442185558662560173837811)
          ·
            refine ⟨128163278337993840260756717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85442185558662560173837811 128163278337993840260756717)
            ·
              refine ⟨48061229376747690097783769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128163278337993840260756717 48061229376747690097783769)
              ·
                refine ⟨36045922032560767573337827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48061229376747690097783769 36045922032560767573337827)
                ·
                  refine ⟨54068883048841151360006741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36045922032560767573337827 54068883048841151360006741)
                  ·
                    refine ⟨633619723228607242500079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54068883048841151360006741 633619723228607242500079)
                    ·
                      rfl

theorem cell22_1850955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_1850955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1850955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1850955 prefixEnd_1850955 := by exact prefixLift 1850955
  have htrace : WordTrace (prefixWord ++ tailWord_1850955) baseStart_1850955 baseEnd_1850955 := by
    simpa [prefixWord, tailWord_1850955, baseEnd_1850955] using wordTrace_append hprefix tailTrace_1850955
  have hstable : (prefixWord ++ tailWord_1850955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850955).length < 2 ^ (prefixWord ++ tailWord_1850955).sum := by decide
  have hdescent : baseEnd_1850955 < baseStart_1850955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851066 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_1851066 : Nat := 118140960795 + 1851066 * 2 ^ 59
def prefixEnd_1851066 : Nat := 4983230072969 + 3 ^ 40 * 1851066 * 2
def baseEnd_1851066 : Nat := 211219240265679984324913

theorem tailTrace_1851066 : CollatzResearch.WordTrace tailWord_1851066 prefixEnd_1851066 211219240265679984324913 := by
  unfold tailWord_1851066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16878480877977873437241263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45009282341274329165976701 16878480877977873437241263)
  ·
    refine ⟨25317721316966810155861895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16878480877977873437241263 25317721316966810155861895)
    ·
      refine ⟨37976581975450215233792843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25317721316966810155861895 37976581975450215233792843)
      ·
        refine ⟨56964872963175322850689265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37976581975450215233792843 56964872963175322850689265)
        ·
          refine ⟨42723654722381492138016949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56964872963175322850689265 42723654722381492138016949)
          ·
            refine ⟨4005342630223264887939089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42723654722381492138016949 4005342630223264887939089)
            ·
              refine ⟨3004006972667448665954317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005342630223264887939089 3004006972667448665954317)
              ·
                refine ⟨1126502614750293249732869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004006972667448665954317 1126502614750293249732869)
                ·
                  refine ⟨211219240265679984324913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126502614750293249732869 211219240265679984324913)
                  ·
                    rfl

theorem cell22_1851066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_1851066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851066 prefixEnd_1851066 := by exact prefixLift 1851066
  have htrace : WordTrace (prefixWord ++ tailWord_1851066) baseStart_1851066 baseEnd_1851066 := by
    simpa [prefixWord, tailWord_1851066, baseEnd_1851066] using wordTrace_append hprefix tailTrace_1851066
  have hstable : (prefixWord ++ tailWord_1851066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851066).length < 2 ^ (prefixWord ++ tailWord_1851066).sum := by decide
  have hdescent : baseEnd_1851066 < baseStart_1851066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851068 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_1851068 : Nat := 118140960795 + 1851068 * 2 ^ 59
def prefixEnd_1851068 : Nat := 4983230072969 + 3 ^ 40 * 1851068 * 2
def baseEnd_1851068 : Nat := 633658405437912614424733

theorem tailTrace_1851068 : CollatzResearch.WordTrace tailWord_1851068 prefixEnd_1851068 633658405437912614424733 := by
  unfold tailWord_1851068
  simp only [CollatzResearch.WordTrace]
  refine ⟨33756998228952124045268929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45009330971936165393691905 33756998228952124045268929)
  ·
    refine ⟨25317748671714093033951697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33756998228952124045268929 25317748671714093033951697)
    ·
      refine ⟨18988311503785569775463773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25317748671714093033951697 18988311503785569775463773)
      ·
        refine ⟨7120616813919588665798915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18988311503785569775463773 7120616813919588665798915)
        ·
          refine ⟨10680925220879382998698373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120616813919588665798915 10680925220879382998698373)
          ·
            refine ⟨2002673478914884312255945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10680925220879382998698373 2002673478914884312255945)
            ·
              refine ⟨1502005109186163234191959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002673478914884312255945 1502005109186163234191959)
              ·
                refine ⟨2253007663779244851287939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502005109186163234191959 2253007663779244851287939)
                ·
                  refine ⟨3379511495668867276931909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253007663779244851287939 3379511495668867276931909)
                  ·
                    refine ⟨633658405437912614424733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379511495668867276931909 633658405437912614424733)
                    ·
                      rfl

theorem cell22_1851068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_1851068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851068 prefixEnd_1851068 := by exact prefixLift 1851068
  have htrace : WordTrace (prefixWord ++ tailWord_1851068) baseStart_1851068 baseEnd_1851068 := by
    simpa [prefixWord, tailWord_1851068, baseEnd_1851068] using wordTrace_append hprefix tailTrace_1851068
  have hstable : (prefixWord ++ tailWord_1851068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851068).length < 2 ^ (prefixWord ++ tailWord_1851068).sum := by decide
  have hdescent : baseEnd_1851068 < baseStart_1851068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851098 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_1851098 : Nat := 118140960795 + 1851098 * 2 ^ 59
def prefixEnd_1851098 : Nat := 4983230072969 + 3 ^ 40 * 1851098 * 2
def baseEnd_1851098 : Nat := 633668675051002536174641

theorem tailTrace_1851098 : CollatzResearch.WordTrace tailWord_1851098 prefixEnd_1851098 633668675051002536174641 := by
  unfold tailWord_1851098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16878772661948890803532487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45010060431863708809419965 16878772661948890803532487)
  ·
    refine ⟨25318158992923336205298731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16878772661948890803532487 25318158992923336205298731)
    ·
      refine ⟨37977238489385004307948097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25318158992923336205298731 37977238489385004307948097)
      ·
        refine ⟨28482928867038753230961073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37977238489385004307948097 28482928867038753230961073)
        ·
          refine ⟨21362196650279064923220805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28482928867038753230961073 21362196650279064923220805)
          ·
            refine ⟨4005411871927324673103901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21362196650279064923220805 4005411871927324673103901)
            ·
              refine ⟨1502029451972746752413963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4005411871927324673103901 1502029451972746752413963)
              ·
                refine ⟨2253044177959120128620945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502029451972746752413963 2253044177959120128620945)
                ·
                  refine ⟨1689783133469340096465709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253044177959120128620945 1689783133469340096465709)
                  ·
                    refine ⟨633668675051002536174641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689783133469340096465709 633668675051002536174641)
                    ·
                      rfl

theorem cell22_1851098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_1851098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851098 prefixEnd_1851098 := by exact prefixLift 1851098
  have htrace : WordTrace (prefixWord ++ tailWord_1851098) baseStart_1851098 baseEnd_1851098 := by
    simpa [prefixWord, tailWord_1851098, baseEnd_1851098] using wordTrace_append hprefix tailTrace_1851098
  have hstable : (prefixWord ++ tailWord_1851098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851098).length < 2 ^ (prefixWord ++ tailWord_1851098).sum := by decide
  have hdescent : baseEnd_1851098 < baseStart_1851098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851111 : List Nat := [1, 1, 5, 4, 1, 1, 1, 8]
def baseStart_1851111 : Nat := 118140960795 + 1851111 * 2 ^ 59
def prefixEnd_1851111 : Nat := 4983230072969 + 3 ^ 40 * 1851111 * 2
def baseEnd_1851111 : Nat := 70408125024074981733289

theorem tailTrace_1851111 : CollatzResearch.WordTrace tailWord_1851111 prefixEnd_1851111 70408125024074981733289 := by
  unfold tailWord_1851111
  simp only [CollatzResearch.WordTrace]
  refine ⟨67515564796748466434353187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45010376531165644289568791 67515564796748466434353187)
  ·
    refine ⟨101273347195122699651529781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67515564796748466434353187 101273347195122699651529781)
    ·
      refine ⟨9494376299542753092330917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101273347195122699651529781 9494376299542753092330917)
      ·
        refine ⟨1780195556164266204812047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9494376299542753092330917 1780195556164266204812047)
        ·
          refine ⟨2670293334246399307218071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780195556164266204812047 2670293334246399307218071)
          ·
            refine ⟨4005440001369598960827107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670293334246399307218071 4005440001369598960827107)
            ·
              refine ⟨6008160002054398441240661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005440001369598960827107 6008160002054398441240661)
              ·
                refine ⟨70408125024074981733289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6008160002054398441240661 70408125024074981733289)
                ·
                  rfl

theorem cell22_1851111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 8].length) (baseStart_1851111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851111 prefixEnd_1851111 := by exact prefixLift 1851111
  have htrace : WordTrace (prefixWord ++ tailWord_1851111) baseStart_1851111 baseEnd_1851111 := by
    simpa [prefixWord, tailWord_1851111, baseEnd_1851111] using wordTrace_append hprefix tailTrace_1851111
  have hstable : (prefixWord ++ tailWord_1851111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851111).length < 2 ^ (prefixWord ++ tailWord_1851111).sum := by decide
  have hdescent : baseEnd_1851111 < baseStart_1851111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851149 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1851149 : Nat := 118140960795 + 1851149 * 2 ^ 59
def prefixEnd_1851149 : Nat := 4983230072969 + 3 ^ 40 * 1851149 * 2
def baseEnd_1851149 : Nat := 633686133393255403149485

theorem tailTrace_1851149 : CollatzResearch.WordTrace tailWord_1851149 prefixEnd_1851149 633686133393255403149485 := by
  unfold tailWord_1851149
  simp only [CollatzResearch.WordTrace]
  refine ⟨67516950770610798924236501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45011300513740532616157667 67516950770610798924236501)
  ·
    refine ⟨1582428533686190599786793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67516950770610798924236501 1582428533686190599786793)
    ·
      refine ⟨1186821400264642949840095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1582428533686190599786793 1186821400264642949840095)
      ·
        refine ⟨1780232100396964424760143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186821400264642949840095 1780232100396964424760143)
        ·
          refine ⟨2670348150595446637140215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780232100396964424760143 2670348150595446637140215)
          ·
            refine ⟨4005522225893169955710323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670348150595446637140215 4005522225893169955710323)
            ·
              refine ⟨6008283338839754933565485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005522225893169955710323 6008283338839754933565485)
              ·
                refine ⟨2253106252064908100087057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6008283338839754933565485 2253106252064908100087057)
                ·
                  refine ⟨1689829689048681075065293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253106252064908100087057 1689829689048681075065293)
                  ·
                    refine ⟨633686133393255403149485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689829689048681075065293 633686133393255403149485)
                    ·
                      rfl

theorem cell22_1851149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1851149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851149 prefixEnd_1851149 := by exact prefixLift 1851149
  have htrace : WordTrace (prefixWord ++ tailWord_1851149) baseStart_1851149 baseEnd_1851149 := by
    simpa [prefixWord, tailWord_1851149, baseEnd_1851149] using wordTrace_append hprefix tailTrace_1851149
  have hstable : (prefixWord ++ tailWord_1851149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851149).length < 2 ^ (prefixWord ++ tailWord_1851149).sum := by decide
  have hdescent : baseEnd_1851149 < baseStart_1851149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851231 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 2, 4]
def baseStart_1851231 : Nat := 118140960795 + 1851231 * 2 ^ 59
def prefixEnd_1851231 : Nat := 4983230072969 + 3 ^ 40 * 1851231 * 2
def baseEnd_1851231 : Nat := 633714203669034522599233

theorem tailTrace_1851231 : CollatzResearch.WordTrace tailWord_1851231 prefixEnd_1851231 633714203669034522599233 := by
  unfold tailWord_1851231
  simp only [CollatzResearch.WordTrace]
  refine ⟨67519941556313726928721547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45013294370875817952481031 67519941556313726928721547)
  ·
    refine ⟨101279912334470590393082321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67519941556313726928721547 101279912334470590393082321)
    ·
      refine ⟨75959934250852942794811741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101279912334470590393082321 75959934250852942794811741)
      ·
        refine ⟨28484975344069853548054403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75959934250852942794811741 28484975344069853548054403)
        ·
          refine ⟨42727463016104780322081605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28484975344069853548054403 42727463016104780322081605)
          ·
            refine ⟨8011399315519646310390301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42727463016104780322081605 8011399315519646310390301)
            ·
              refine ⟨3004274743319867366396363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8011399315519646310390301 3004274743319867366396363)
              ·
                refine ⟨4506412114979801049594545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004274743319867366396363 4506412114979801049594545)
                ·
                  refine ⟨3379809086234850787195909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4506412114979801049594545 3379809086234850787195909)
                  ·
                    refine ⟨633714203669034522599233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379809086234850787195909 633714203669034522599233)
                    ·
                      rfl

theorem cell22_1851231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_1851231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851231 prefixEnd_1851231 := by exact prefixLift 1851231
  have htrace : WordTrace (prefixWord ++ tailWord_1851231) baseStart_1851231 baseEnd_1851231 := by
    simpa [prefixWord, tailWord_1851231, baseEnd_1851231] using wordTrace_append hprefix tailTrace_1851231
  have hstable : (prefixWord ++ tailWord_1851231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851231).length < 2 ^ (prefixWord ++ tailWord_1851231).sum := by decide
  have hdescent : baseEnd_1851231 < baseStart_1851231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851246 : List Nat := [4, 1, 2, 3, 1, 2, 9]
def baseStart_1851246 : Nat := 118140960795 + 1851246 * 2 ^ 59
def prefixEnd_1851246 : Nat := 4983230072969 + 3 ^ 40 * 1851246 * 2
def baseEnd_1851246 : Nat := 23471086610206647536081

theorem tailTrace_1851246 : CollatzResearch.WordTrace tailWord_1851246 prefixEnd_1851246 23471086610206647536081 := by
  unfold tailWord_1851246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440061081407423061314699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45013659100839589660345061 8440061081407423061314699)
  ·
    refine ⟨12660091622111134591972049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8440061081407423061314699 12660091622111134591972049)
    ·
      refine ⟨9495068716583350943979037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12660091622111134591972049 9495068716583350943979037)
      ·
        refine ⟨3560650768718756603992139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9495068716583350943979037 3560650768718756603992139)
        ·
          refine ⟨5340976153078134905988209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560650768718756603992139 5340976153078134905988209)
          ·
            refine ⟨4005732114808601179491157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340976153078134905988209 4005732114808601179491157)
            ·
              refine ⟨23471086610206647536081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4005732114808601179491157 23471086610206647536081)
              ·
                rfl

theorem cell22_1851246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 9].length) (baseStart_1851246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851246 prefixEnd_1851246 := by exact prefixLift 1851246
  have htrace : WordTrace (prefixWord ++ tailWord_1851246) baseStart_1851246 baseEnd_1851246 := by
    simpa [prefixWord, tailWord_1851246, baseEnd_1851246] using wordTrace_append hprefix tailTrace_1851246
  have hstable : (prefixWord ++ tailWord_1851246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851246).length < 2 ^ (prefixWord ++ tailWord_1851246).sum := by decide
  have hdescent : baseEnd_1851246 < baseStart_1851246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851286 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1851286 : Nat := 118140960795 + 1851286 * 2 ^ 59
def prefixEnd_1851286 : Nat := 4983230072969 + 3 ^ 40 * 1851286 * 2
def baseEnd_1851286 : Nat := 211244343764344237491355

theorem tailTrace_1851286 : CollatzResearch.WordTrace tailWord_1851286 prefixEnd_1851286 211244343764344237491355 := by
  unfold tailWord_1851286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220121723194654457623357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45014631714076314214649141 4220121723194654457623357)
  ·
    refine ⟨1582545646197995421608759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4220121723194654457623357 1582545646197995421608759)
    ·
      refine ⟨2373818469296993132413139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582545646197995421608759 2373818469296993132413139)
      ·
        refine ⟨3560727703945489698619709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373818469296993132413139 3560727703945489698619709)
        ·
          refine ⟨1335272888979558636982391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3560727703945489698619709 1335272888979558636982391)
          ·
            refine ⟨2002909333469337955473587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335272888979558636982391 2002909333469337955473587)
            ·
              refine ⟨3004364000204006933210381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002909333469337955473587 3004364000204006933210381)
              ·
                refine ⟨1126636500076502599953893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004364000204006933210381 1126636500076502599953893)
                ·
                  refine ⟨211244343764344237491355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126636500076502599953893 211244343764344237491355)
                  ·
                    rfl

theorem cell22_1851286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1851286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851286 prefixEnd_1851286 := by exact prefixLift 1851286
  have htrace : WordTrace (prefixWord ++ tailWord_1851286) baseStart_1851286 baseEnd_1851286 := by
    simpa [prefixWord, tailWord_1851286, baseEnd_1851286] using wordTrace_append hprefix tailTrace_1851286
  have hstable : (prefixWord ++ tailWord_1851286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851286).length < 2 ^ (prefixWord ++ tailWord_1851286).sum := by decide
  have hdescent : baseEnd_1851286 < baseStart_1851286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851289 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_1851289 : Nat := 118140960795 + 1851289 * 2 ^ 59
def prefixEnd_1851289 : Nat := 4983230072969 + 3 ^ 40 * 1851289 * 2
def baseEnd_1851289 : Nat := 633734058254341704649055

theorem tailTrace_1851289 : CollatzResearch.WordTrace tailWord_1851289 prefixEnd_1851289 633734058254341704649055 := by
  unfold tailWord_1851289
  simp only [CollatzResearch.WordTrace]
  refine ⟨67522056990103602834332921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45014704660069068556221947 67522056990103602834332921)
  ·
    refine ⟨50641542742577702125749691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67522056990103602834332921 50641542742577702125749691)
    ·
      refine ⟨75962314113866553188624537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50641542742577702125749691 75962314113866553188624537)
      ·
        refine ⟨56971735585399914891468403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75962314113866553188624537 56971735585399914891468403)
        ·
          refine ⟨85457603378099872337202605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56971735585399914891468403 85457603378099872337202605)
          ·
            refine ⟨32046601266787452126450977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85457603378099872337202605 32046601266787452126450977)
            ·
              refine ⟨24034950950090589094838233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32046601266787452126450977 24034950950090589094838233)
              ·
                refine ⟨18026213212567941821128675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24034950950090589094838233 18026213212567941821128675)
                ·
                  refine ⟨27039319818851912731693013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18026213212567941821128675 27039319818851912731693013)
                  ·
                    refine ⟨633734058254341704649055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27039319818851912731693013 633734058254341704649055)
                    ·
                      rfl

theorem cell22_1851289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_1851289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851289 prefixEnd_1851289 := by exact prefixLift 1851289
  have htrace : WordTrace (prefixWord ++ tailWord_1851289) baseStart_1851289 baseEnd_1851289 := by
    simpa [prefixWord, tailWord_1851289, baseEnd_1851289] using wordTrace_append hprefix tailTrace_1851289
  have hstable : (prefixWord ++ tailWord_1851289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851289).length < 2 ^ (prefixWord ++ tailWord_1851289).sum := by decide
  have hdescent : baseEnd_1851289 < baseStart_1851289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851321 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_1851321 : Nat := 118140960795 + 1851321 * 2 ^ 59
def prefixEnd_1851321 : Nat := 4983230072969 + 3 ^ 40 * 1851321 * 2
def baseEnd_1851321 : Nat := 633745012508304287848957

theorem tailTrace_1851321 : CollatzResearch.WordTrace tailWord_1851321 prefixEnd_1851321 633745012508304287848957 := by
  unfold tailWord_1851321
  simp only [CollatzResearch.WordTrace]
  refine ⟨67523224125987672299497817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45015482750658448199665211 67523224125987672299497817)
  ·
    refine ⟨50642418094490754224623363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67523224125987672299497817 50642418094490754224623363)
    ·
      refine ⟨75963627141736131336935045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50642418094490754224623363 75963627141736131336935045)
      ·
        refine ⟨14243180089075524625675321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75963627141736131336935045 14243180089075524625675321)
        ·
          refine ⟨10682385066806643469256491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14243180089075524625675321 10682385066806643469256491)
          ·
            refine ⟨16023577600209965203884737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682385066806643469256491 16023577600209965203884737)
            ·
              refine ⟨12017683200157473902913553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16023577600209965203884737 12017683200157473902913553)
              ·
                refine ⟨9013262400118105427185165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12017683200157473902913553 9013262400118105427185165)
                ·
                  refine ⟨3379973400044289535194437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9013262400118105427185165 3379973400044289535194437)
                  ·
                    refine ⟨633745012508304287848957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379973400044289535194437 633745012508304287848957)
                    ·
                      rfl

theorem cell22_1851321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_1851321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851321 prefixEnd_1851321 := by exact prefixLift 1851321
  have htrace : WordTrace (prefixWord ++ tailWord_1851321) baseStart_1851321 baseEnd_1851321 := by
    simpa [prefixWord, tailWord_1851321, baseEnd_1851321] using wordTrace_append hprefix tailTrace_1851321
  have hstable : (prefixWord ++ tailWord_1851321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851321).length < 2 ^ (prefixWord ++ tailWord_1851321).sum := by decide
  have hdescent : baseEnd_1851321 < baseStart_1851321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851325 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1851325 : Nat := 118140960795 + 1851325 * 2 ^ 59
def prefixEnd_1851325 : Nat := 4983230072969 + 3 ^ 40 * 1851325 * 2
def baseEnd_1851325 : Nat := 211248793930016536916315

theorem tailTrace_1851325 : CollatzResearch.WordTrace tailWord_1851325 prefixEnd_1851325 211248793930016536916315 := by
  unfold tailWord_1851325
  simp only [CollatzResearch.WordTrace]
  refine ⟨67523370017973180982643429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45015580011982120655095619 67523370017973180982643429)
  ·
    refine ⟨12660631878369971434245643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67523370017973180982643429 12660631878369971434245643)
    ·
      refine ⟨18990947817554957151368465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660631878369971434245643 18990947817554957151368465)
      ·
        refine ⟨14243210863166217863526349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18990947817554957151368465 14243210863166217863526349)
        ·
          refine ⟨5341204073687331698822381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14243210863166217863526349 5341204073687331698822381)
          ·
            refine ⟨2002951527632749387058393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5341204073687331698822381 2002951527632749387058393)
            ·
              refine ⟨1502213645724562040293795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002951527632749387058393 1502213645724562040293795)
              ·
                refine ⟨2253320468586843060440693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502213645724562040293795 2253320468586843060440693)
                ·
                  refine ⟨211248793930016536916315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2253320468586843060440693 211248793930016536916315)
                  ·
                    rfl

theorem cell22_1851325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1851325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851325 prefixEnd_1851325 := by exact prefixLift 1851325
  have htrace : WordTrace (prefixWord ++ tailWord_1851325) baseStart_1851325 baseEnd_1851325 := by
    simpa [prefixWord, tailWord_1851325, baseEnd_1851325] using wordTrace_append hprefix tailTrace_1851325
  have hstable : (prefixWord ++ tailWord_1851325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851325).length < 2 ^ (prefixWord ++ tailWord_1851325).sum := by decide
  have hdescent : baseEnd_1851325 < baseStart_1851325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851338 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_1851338 : Nat := 118140960795 + 1851338 * 2 ^ 59
def prefixEnd_1851338 : Nat := 4983230072969 + 3 ^ 40 * 1851338 * 2
def baseEnd_1851338 : Nat := 633750831955721910173905

theorem tailTrace_1851338 : CollatzResearch.WordTrace tailWord_1851338 prefixEnd_1851338 633750831955721910173905 := by
  unfold tailWord_1851338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880961041731521050716667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45015896111284056135244445 16880961041731521050716667)
  ·
    refine ⟨25321441562597281576075001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16880961041731521050716667 25321441562597281576075001)
    ·
      refine ⟨18991081171947961182056251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25321441562597281576075001 18991081171947961182056251)
      ·
        refine ⟨28486621757921941773084377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18991081171947961182056251 28486621757921941773084377)
        ·
          refine ⟨21364966318441456329813283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28486621757921941773084377 21364966318441456329813283)
          ·
            refine ⟨32047449477662184494719925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21364966318441456329813283 32047449477662184494719925)
            ·
              refine ⟨3004448388530829796379993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32047449477662184494719925 3004448388530829796379993)
              ·
                refine ⟨2253336291398122347284995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004448388530829796379993 2253336291398122347284995)
                ·
                  refine ⟨3380004437097183520927493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253336291398122347284995 3380004437097183520927493)
                  ·
                    refine ⟨633750831955721910173905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3380004437097183520927493 633750831955721910173905)
                    ·
                      rfl

theorem cell22_1851338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_1851338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851338 prefixEnd_1851338 := by exact prefixLift 1851338
  have htrace : WordTrace (prefixWord ++ tailWord_1851338) baseStart_1851338 baseEnd_1851338 := by
    simpa [prefixWord, tailWord_1851338, baseEnd_1851338] using wordTrace_append hprefix tailTrace_1851338
  have hstable : (prefixWord ++ tailWord_1851338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851338).length < 2 ^ (prefixWord ++ tailWord_1851338).sum := by decide
  have hdescent : baseEnd_1851338 < baseStart_1851338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851351 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1851351 : Nat := 118140960795 + 1851351 * 2 ^ 59
def prefixEnd_1851351 : Nat := 4983230072969 + 3 ^ 40 * 1851351 * 2
def baseEnd_1851351 : Nat := 633755282121394209598865

theorem tailTrace_1851351 : CollatzResearch.WordTrace tailWord_1851351 prefixEnd_1851351 633755282121394209598865 := by
  unfold tailWord_1851351
  simp only [CollatzResearch.WordTrace]
  refine ⟨67524318315878987423089907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45016212210585991615393271 67524318315878987423089907)
  ·
    refine ⟨101286477473818481134634861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67524318315878987423089907 101286477473818481134634861)
    ·
      refine ⟨37982429052681930425488073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101286477473818481134634861 37982429052681930425488073)
      ·
        refine ⟨28486821789511447819116055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37982429052681930425488073 28486821789511447819116055)
        ·
          refine ⟨42730232684267171728674083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28486821789511447819116055 42730232684267171728674083)
          ·
            refine ⟨64095349026400757593011125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42730232684267171728674083 64095349026400757593011125)
            ·
              refine ⟨6008938971225071024344793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64095349026400757593011125 6008938971225071024344793)
              ·
                refine ⟨4506704228418803268258595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6008938971225071024344793 4506704228418803268258595)
                ·
                  refine ⟨6760056342628204902387893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506704228418803268258595 6760056342628204902387893)
                  ·
                    refine ⟨633755282121394209598865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6760056342628204902387893 633755282121394209598865)
                    ·
                      rfl

theorem cell22_1851351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1851351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851351 prefixEnd_1851351 := by exact prefixLift 1851351
  have htrace : WordTrace (prefixWord ++ tailWord_1851351) baseStart_1851351 baseEnd_1851351 := by
    simpa [prefixWord, tailWord_1851351, baseEnd_1851351] using wordTrace_append hprefix tailTrace_1851351
  have hstable : (prefixWord ++ tailWord_1851351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851351).length < 2 ^ (prefixWord ++ tailWord_1851351).sum := by decide
  have hdescent : baseEnd_1851351 < baseStart_1851351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851488 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_1851488 : Nat := 118140960795 + 1851488 * 2 ^ 59
def prefixEnd_1851488 : Nat := 4983230072969 + 3 ^ 40 * 1851488 * 2
def baseEnd_1851488 : Nat := 211267393340390506307815

theorem tailTrace_1851488 : CollatzResearch.WordTrace tailWord_1851488 prefixEnd_1851488 211267393340390506307815 := by
  unfold tailWord_1851488
  simp only [CollatzResearch.WordTrace]
  refine ⟨33764657558191329910413559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45019543410921773213884745 33764657558191329910413559)
  ·
    refine ⟨50646986337286994865620339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33764657558191329910413559 50646986337286994865620339)
    ·
      refine ⟨75970479505930492298430509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50646986337286994865620339 75970479505930492298430509)
      ·
        refine ⟨28488929814723934611911441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75970479505930492298430509 28488929814723934611911441)
        ·
          refine ⟨21366697361042950958933581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28488929814723934611911441 21366697361042950958933581)
          ·
            refine ⟨8012511510391106609600093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21366697361042950958933581 8012511510391106609600093)
            ·
              refine ⟨3004691816396664978600035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8012511510391106609600093 3004691816396664978600035)
              ·
                refine ⟨4507037724594997467900053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004691816396664978600035 4507037724594997467900053)
                ·
                  refine ⟨211267393340390506307815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4507037724594997467900053 211267393340390506307815)
                  ·
                    rfl

theorem cell22_1851488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_1851488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851488 prefixEnd_1851488 := by exact prefixLift 1851488
  have htrace : WordTrace (prefixWord ++ tailWord_1851488) baseStart_1851488 baseEnd_1851488 := by
    simpa [prefixWord, tailWord_1851488, baseEnd_1851488] using wordTrace_append hprefix tailTrace_1851488
  have hstable : (prefixWord ++ tailWord_1851488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851488).length < 2 ^ (prefixWord ++ tailWord_1851488).sum := by decide
  have hdescent : baseEnd_1851488 < baseStart_1851488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851569 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 2, 4]
def baseStart_1851569 : Nat := 118140960795 + 1851569 * 2 ^ 59
def prefixEnd_1851569 : Nat := 4983230072969 + 3 ^ 40 * 1851569 * 2
def baseEnd_1851569 : Nat := 633829907976514307648197

theorem tailTrace_1851569 : CollatzResearch.WordTrace tailWord_1851569 prefixEnd_1851569 633829907976514307648197 := by
  unfold tailWord_1851569
  simp only [CollatzResearch.WordTrace]
  refine ⟨67532269429089210654525761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45021512952726140436350507 67532269429089210654525761)
  ·
    refine ⟨50649202071816907990894321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67532269429089210654525761 50649202071816907990894321)
    ·
      refine ⟨37986901553862680993170741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50649202071816907990894321 37986901553862680993170741)
      ·
        refine ⟨3561272020674626343109757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37986901553862680993170741 3561272020674626343109757)
        ·
          refine ⟨1335477007752984878666159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3561272020674626343109757 1335477007752984878666159)
          ·
            refine ⟨2003215511629477317999239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335477007752984878666159 2003215511629477317999239)
            ·
              refine ⟨3004823267444215976998859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003215511629477317999239 3004823267444215976998859)
              ·
                refine ⟨4507234901166323965498289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004823267444215976998859 4507234901166323965498289)
                ·
                  refine ⟨3380426175874742974123717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507234901166323965498289 3380426175874742974123717)
                  ·
                    refine ⟨633829907976514307648197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3380426175874742974123717 633829907976514307648197)
                    ·
                      rfl

theorem cell22_1851569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_1851569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851569 prefixEnd_1851569 := by exact prefixLift 1851569
  have htrace : WordTrace (prefixWord ++ tailWord_1851569) baseStart_1851569 baseEnd_1851569 := by
    simpa [prefixWord, tailWord_1851569, baseEnd_1851569] using wordTrace_append hprefix tailTrace_1851569
  have hstable : (prefixWord ++ tailWord_1851569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851569).length < 2 ^ (prefixWord ++ tailWord_1851569).sum := by decide
  have hdescent : baseEnd_1851569 < baseStart_1851569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851618 : List Nat := [3, 3, 4, 1, 2, 1, 2, 6]
def baseStart_1851618 : Nat := 118140960795 + 1851618 * 2 ^ 59
def prefixEnd_1851618 : Nat := 4983230072969 + 3 ^ 40 * 1851618 * 2
def baseEnd_1851618 : Nat := 70427409075321612574783

theorem tailTrace_1851618 : CollatzResearch.WordTrace tailWord_1851618 prefixEnd_1851618 70427409075321612574783 := by
  unfold tailWord_1851618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883514151477923005764877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45022704403941128015373005 16883514151477923005764877)
  ·
    refine ⟨6331317806804221127161829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16883514151477923005764877 6331317806804221127161829)
    ·
      refine ⟨1187122088775791461342843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6331317806804221127161829 1187122088775791461342843)
      ·
        refine ⟨1780683133163687192014265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187122088775791461342843 1780683133163687192014265)
        ·
          refine ⟨1335512349872765394010699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780683133163687192014265 1335512349872765394010699)
          ·
            refine ⟨2003268524809148091016049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335512349872765394010699 2003268524809148091016049)
            ·
              refine ⟨1502451393606861068262037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003268524809148091016049 1502451393606861068262037)
              ·
                refine ⟨70427409075321612574783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1502451393606861068262037 70427409075321612574783)
                ·
                  rfl

theorem cell22_1851618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_1851618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851618 prefixEnd_1851618 := by exact prefixLift 1851618
  have htrace : WordTrace (prefixWord ++ tailWord_1851618) baseStart_1851618 baseEnd_1851618 := by
    simpa [prefixWord, tailWord_1851618, baseEnd_1851618] using wordTrace_append hprefix tailTrace_1851618
  have hstable : (prefixWord ++ tailWord_1851618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851618).length < 2 ^ (prefixWord ++ tailWord_1851618).sum := by decide
  have hdescent : baseEnd_1851618 < baseStart_1851618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851653 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1851653 : Nat := 118140960795 + 1851653 * 2 ^ 59
def prefixEnd_1851653 : Nat := 4983230072969 + 3 ^ 40 * 1851653 * 2
def baseEnd_1851653 : Nat := 633858662893166088547939

theorem tailTrace_1851653 : CollatzResearch.WordTrace tailWord_1851653 prefixEnd_1851653 633858662893166088547939 := by
  unfold tailWord_1851653
  simp only [CollatzResearch.WordTrace]
  refine ⟨67535333160784893000583613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45023555440523262000389075 67535333160784893000583613)
  ·
    refine ⟨25325749935294334875218855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67535333160784893000583613 25325749935294334875218855)
    ·
      refine ⟨37988624902941502312828283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25325749935294334875218855 37988624902941502312828283)
      ·
        refine ⟨56982937354412253469242425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37988624902941502312828283 56982937354412253469242425)
        ·
          refine ⟨42737203015809190101931819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56982937354412253469242425 42737203015809190101931819)
          ·
            refine ⟨64105804523713785152897729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42737203015809190101931819 64105804523713785152897729)
            ·
              refine ⟨48079353392785338864673297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64105804523713785152897729 48079353392785338864673297)
              ·
                refine ⟨36059515044589004148504973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48079353392785338864673297 36059515044589004148504973)
                ·
                  refine ⟨13522318141720876555689365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36059515044589004148504973 13522318141720876555689365)
                  ·
                    refine ⟨633858662893166088547939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13522318141720876555689365 633858662893166088547939)
                    ·
                      rfl

theorem cell22_1851653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1851653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851653 prefixEnd_1851653 := by exact prefixLift 1851653
  have htrace : WordTrace (prefixWord ++ tailWord_1851653) baseStart_1851653 baseEnd_1851653 := by
    simpa [prefixWord, tailWord_1851653, baseEnd_1851653] using wordTrace_append hprefix tailTrace_1851653
  have hstable : (prefixWord ++ tailWord_1851653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851653).length < 2 ^ (prefixWord ++ tailWord_1851653).sum := by decide
  have hdescent : baseEnd_1851653 < baseStart_1851653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851672 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_1851672 : Nat := 118140960795 + 1851672 * 2 ^ 59
def prefixEnd_1851672 : Nat := 4983230072969 + 3 ^ 40 * 1851672 * 2
def baseEnd_1851672 : Nat := 633865166981456372322881

theorem tailTrace_1851672 : CollatzResearch.WordTrace tailWord_1851672 prefixEnd_1851672 633865166981456372322881 := by
  unfold tailWord_1851672
  simp only [CollatzResearch.WordTrace]
  refine ⟨33768013073858029622762635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45024017431810706163683513 33768013073858029622762635)
  ·
    refine ⟨50652019610787044434143953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33768013073858029622762635 50652019610787044434143953)
    ·
      refine ⟨37989014708090283325607965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50652019610787044434143953 37989014708090283325607965)
      ·
        refine ⟨14245880515533856247102987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37989014708090283325607965 14245880515533856247102987)
        ·
          refine ⟨21368820773300784370654481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245880515533856247102987 21368820773300784370654481)
          ·
            refine ⟨16026615579975588277990861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21368820773300784370654481 16026615579975588277990861)
            ·
              refine ⟨6009980842490845604246573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16026615579975588277990861 6009980842490845604246573)
              ·
                refine ⟨2253742815934067101592465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6009980842490845604246573 2253742815934067101592465)
                ·
                  refine ⟨1690307111950550326194349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253742815934067101592465 1690307111950550326194349)
                  ·
                    refine ⟨633865166981456372322881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1690307111950550326194349 633865166981456372322881)
                    ·
                      rfl

theorem cell22_1851672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_1851672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851672 prefixEnd_1851672 := by exact prefixLift 1851672
  have htrace : WordTrace (prefixWord ++ tailWord_1851672) baseStart_1851672 baseEnd_1851672 := by
    simpa [prefixWord, tailWord_1851672, baseEnd_1851672] using wordTrace_append hprefix tailTrace_1851672
  have hstable : (prefixWord ++ tailWord_1851672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851672).length < 2 ^ (prefixWord ++ tailWord_1851672).sum := by decide
  have hdescent : baseEnd_1851672 < baseStart_1851672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851751 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1851751 : Nat := 118140960795 + 1851751 * 2 ^ 59
def prefixEnd_1851751 : Nat := 4983230072969 + 3 ^ 40 * 1851751 * 2
def baseEnd_1851751 : Nat := 633892210295926499597639

theorem tailTrace_1851751 : CollatzResearch.WordTrace tailWord_1851751 prefixEnd_1851751 633892210295926499597639 := by
  unfold tailWord_1851751
  simp only [CollatzResearch.WordTrace]
  refine ⟨67538907514429855737651107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45025938342953237158434071 67538907514429855737651107)
  ·
    refine ⟨101308361271644783606476661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67538907514429855737651107 101308361271644783606476661)
    ·
      refine ⟨9497658869216698463107187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101308361271644783606476661 9497658869216698463107187)
      ·
        refine ⟨14246488303825047694660781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9497658869216698463107187 14246488303825047694660781)
        ·
          refine ⟨5342433113934392885497793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14246488303825047694660781 5342433113934392885497793)
          ·
            refine ⟨4006824835450794664123345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342433113934392885497793 4006824835450794664123345)
            ·
              refine ⟨3005118626588095998092509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006824835450794664123345 3005118626588095998092509)
              ·
                refine ⟨1126919484970535999284691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3005118626588095998092509 1126919484970535999284691)
                ·
                  refine ⟨1690379227455803998927037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126919484970535999284691 1690379227455803998927037)
                  ·
                    refine ⟨633892210295926499597639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1690379227455803998927037 633892210295926499597639)
                    ·
                      rfl

theorem cell22_1851751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1851751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851751 prefixEnd_1851751 := by exact prefixLift 1851751
  have htrace : WordTrace (prefixWord ++ tailWord_1851751) baseStart_1851751 baseEnd_1851751 := by
    simpa [prefixWord, tailWord_1851751, baseEnd_1851751] using wordTrace_append hprefix tailTrace_1851751
  have hstable : (prefixWord ++ tailWord_1851751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851751).length < 2 ^ (prefixWord ++ tailWord_1851751).sum := by decide
  have hdescent : baseEnd_1851751 < baseStart_1851751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851807 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 6, 3]
def baseStart_1851807 : Nat := 118140960795 + 1851807 * 2 ^ 59
def prefixEnd_1851807 : Nat := 4983230072969 + 3 ^ 40 * 1851807 * 2
def baseEnd_1851807 : Nat := 633911380240361020197467

theorem tailTrace_1851807 : CollatzResearch.WordTrace tailWord_1851807 prefixEnd_1851807 633911380240361020197467 := by
  unfold tailWord_1851807
  simp only [CollatzResearch.WordTrace]
  refine ⟨67540950002226977301689675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45027300001484651534459783 67540950002226977301689675)
  ·
    refine ⟨101311425003340465952534513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67540950002226977301689675 101311425003340465952534513)
    ·
      refine ⟨75983568752505349464400885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101311425003340465952534513 75983568752505349464400885)
      ·
        refine ⟨7123459570547376512287583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75983568752505349464400885 7123459570547376512287583)
        ·
          refine ⟨10685189355821064768431375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123459570547376512287583 10685189355821064768431375)
          ·
            refine ⟨16027784033731597152647063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685189355821064768431375 16027784033731597152647063)
            ·
              refine ⟨24041676050597395728970595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16027784033731597152647063 24041676050597395728970595)
              ·
                refine ⟨36062514075896093593455893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24041676050597395728970595 36062514075896093593455893)
                ·
                  refine ⟨1690430347307629387193245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36062514075896093593455893 1690430347307629387193245)
                  ·
                    refine ⟨633911380240361020197467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1690430347307629387193245 633911380240361020197467)
                    ·
                      rfl

theorem cell22_1851807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_1851807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851807 prefixEnd_1851807 := by exact prefixLift 1851807
  have htrace : WordTrace (prefixWord ++ tailWord_1851807) baseStart_1851807 baseEnd_1851807 := by
    simpa [prefixWord, tailWord_1851807, baseEnd_1851807] using wordTrace_append hprefix tailTrace_1851807
  have hstable : (prefixWord ++ tailWord_1851807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851807).length < 2 ^ (prefixWord ++ tailWord_1851807).sum := by decide
  have hdescent : baseEnd_1851807 < baseStart_1851807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851837 : List Nat := [1, 4, 1, 2, 2, 3, 2, 7]
def baseStart_1851837 : Nat := 118140960795 + 1851837 * 2 ^ 59
def prefixEnd_1851837 : Nat := 4983230072969 + 3 ^ 40 * 1851837 * 2
def baseEnd_1851837 : Nat := 70435738872605660216375

theorem tailTrace_1851837 : CollatzResearch.WordTrace tailWord_1851837 prefixEnd_1851837 70435738872605660216375 := by
  unfold tailWord_1851837
  simp only [CollatzResearch.WordTrace]
  refine ⟨67542044192118292425281765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45028029461412194950187843 67542044192118292425281765)
  ·
    refine ⟨12664133286022179829740331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67542044192118292425281765 12664133286022179829740331)
    ·
      refine ⟨18996199929033269744610497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12664133286022179829740331 18996199929033269744610497)
      ·
        refine ⟨14247149946774952308457873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18996199929033269744610497 14247149946774952308457873)
        ·
          refine ⟨10685362460081214231343405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14247149946774952308457873 10685362460081214231343405)
          ·
            refine ⟨4007010922530455336753777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10685362460081214231343405 4007010922530455336753777)
            ·
              refine ⟨3005258191897841502565333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4007010922530455336753777 3005258191897841502565333)
              ·
                refine ⟨70435738872605660216375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3005258191897841502565333 70435738872605660216375)
                ·
                  rfl

theorem cell22_1851837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 7].length) (baseStart_1851837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851837 prefixEnd_1851837 := by exact prefixLift 1851837
  have htrace : WordTrace (prefixWord ++ tailWord_1851837) baseStart_1851837 baseEnd_1851837 := by
    simpa [prefixWord, tailWord_1851837, baseEnd_1851837] using wordTrace_append hprefix tailTrace_1851837
  have hstable : (prefixWord ++ tailWord_1851837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851837).length < 2 ^ (prefixWord ++ tailWord_1851837).sum := by decide
  have hdescent : baseEnd_1851837 < baseStart_1851837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851944 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_1851944 : Nat := 118140960795 + 1851944 * 2 ^ 59
def prefixEnd_1851944 : Nat := 4983230072969 + 3 ^ 40 * 1851944 * 2
def baseEnd_1851944 : Nat := 211319426046712776507349

theorem tailTrace_1851944 : CollatzResearch.WordTrace tailWord_1851944 prefixEnd_1851944 211319426046712776507349 := by
  unfold tailWord_1851944
  simp only [CollatzResearch.WordTrace]
  refine ⟨33772973401365324849713443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45030631201820433132951257 33772973401365324849713443)
  ·
    refine ⟨50659460102047987274570165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33772973401365324849713443 50659460102047987274570165)
    ·
      refine ⟨4749324384566998806990953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50659460102047987274570165 4749324384566998806990953)
      ·
        refine ⟨3561993288425249105243215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4749324384566998806990953 3561993288425249105243215)
        ·
          refine ⟨5342989932637873657864823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561993288425249105243215 5342989932637873657864823)
          ·
            refine ⟨8014484898956810486797235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342989932637873657864823 8014484898956810486797235)
            ·
              refine ⟨12021727348435215730195853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8014484898956810486797235 12021727348435215730195853)
              ·
                refine ⟨4508147755663205898823445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12021727348435215730195853 4508147755663205898823445)
                ·
                  refine ⟨211319426046712776507349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4508147755663205898823445 211319426046712776507349)
                  ·
                    rfl

theorem cell22_1851944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_1851944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851944 prefixEnd_1851944 := by exact prefixLift 1851944
  have htrace : WordTrace (prefixWord ++ tailWord_1851944) baseStart_1851944 baseEnd_1851944 := by
    simpa [prefixWord, tailWord_1851944, baseEnd_1851944] using wordTrace_append hprefix tailTrace_1851944
  have hstable : (prefixWord ++ tailWord_1851944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851944).length < 2 ^ (prefixWord ++ tailWord_1851944).sum := by decide
  have hdescent : baseEnd_1851944 < baseStart_1851944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851957 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1851957 : Nat := 118140960795 + 1851957 * 2 ^ 59
def prefixEnd_1851957 : Nat := 4983230072969 + 3 ^ 40 * 1851957 * 2
def baseEnd_1851957 : Nat := 633962728305810628947007

theorem tailTrace_1851957 : CollatzResearch.WordTrace tailWord_1851957 prefixEnd_1851957 633962728305810628947007 := by
  unfold tailWord_1851957
  simp only [CollatzResearch.WordTrace]
  refine ⟨67546420951683552919650125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45030947301122368613100083 67546420951683552919650125)
  ·
    refine ⟨25329907856881332344868797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67546420951683552919650125 25329907856881332344868797)
    ·
      refine ⟨9498715446330499629325799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25329907856881332344868797 9498715446330499629325799)
      ·
        refine ⟨14248073169495749443988699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9498715446330499629325799 14248073169495749443988699)
        ·
          refine ⟨21372109754243624165983049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14248073169495749443988699 21372109754243624165983049)
          ·
            refine ⟨16029082315682718124487287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372109754243624165983049 16029082315682718124487287)
            ·
              refine ⟨24043623473524077186730931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16029082315682718124487287 24043623473524077186730931)
              ·
                refine ⟨36065435210286115780096397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24043623473524077186730931 36065435210286115780096397)
                ·
                  refine ⟨13524538203857293417536149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36065435210286115780096397 13524538203857293417536149)
                  ·
                    refine ⟨633962728305810628947007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13524538203857293417536149 633962728305810628947007)
                    ·
                      rfl

theorem cell22_1851957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1851957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1851957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1851957 prefixEnd_1851957 := by exact prefixLift 1851957
  have htrace : WordTrace (prefixWord ++ tailWord_1851957) baseStart_1851957 baseEnd_1851957 := by
    simpa [prefixWord, tailWord_1851957, baseEnd_1851957] using wordTrace_append hprefix tailTrace_1851957
  have hstable : (prefixWord ++ tailWord_1851957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851957).length < 2 ^ (prefixWord ++ tailWord_1851957).sum := by decide
  have hdescent : baseEnd_1851957 < baseStart_1851957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852079 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 6]
def baseStart_1852079 : Nat := 118140960795 + 1852079 * 2 ^ 59
def prefixEnd_1852079 : Nat := 4983230072969 + 3 ^ 40 * 1852079 * 2
def baseEnd_1852079 : Nat := 211334830466347659132211

theorem tailTrace_1852079 : CollatzResearch.WordTrace tailWord_1852079 prefixEnd_1852079 211334830466347659132211 := by
  unfold tailWord_1852079
  simp only [CollatzResearch.WordTrace]
  refine ⟨67550870657241567755591291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45033913771494378503727527 67550870657241567755591291)
  ·
    refine ⟨101326305985862351633386937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67550870657241567755591291 101326305985862351633386937)
    ·
      refine ⟨75994729489396763725040203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101326305985862351633386937 75994729489396763725040203)
      ·
        refine ⟨113992094234095145587560305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75994729489396763725040203 113992094234095145587560305)
        ·
          refine ⟨85494070675571359190670229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113992094234095145587560305 85494070675571359190670229)
          ·
            refine ⟨4007534562917407462062667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85494070675571359190670229 4007534562917407462062667)
            ·
              refine ⟨6011301844376111193094001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007534562917407462062667 6011301844376111193094001)
              ·
                refine ⟨4508476383282083394820501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011301844376111193094001 4508476383282083394820501)
                ·
                  refine ⟨211334830466347659132211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4508476383282083394820501 211334830466347659132211)
                  ·
                    rfl

theorem cell22_1852079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 6].length) (baseStart_1852079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852079 prefixEnd_1852079 := by exact prefixLift 1852079
  have htrace : WordTrace (prefixWord ++ tailWord_1852079) baseStart_1852079 baseEnd_1852079 := by
    simpa [prefixWord, tailWord_1852079, baseEnd_1852079] using wordTrace_append hprefix tailTrace_1852079
  have hstable : (prefixWord ++ tailWord_1852079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852079).length < 2 ^ (prefixWord ++ tailWord_1852079).sum := by decide
  have hdescent : baseEnd_1852079 < baseStart_1852079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852096 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 4]
def baseStart_1852096 : Nat := 118140960795 + 1852096 * 2 ^ 59
def prefixEnd_1852096 : Nat := 4983230072969 + 3 ^ 40 * 1852096 * 2
def baseEnd_1852096 : Nat := 211336770282153533240527

theorem tailTrace_1852096 : CollatzResearch.WordTrace tailWord_1852096 prefixEnd_1852096 211336770282153533240527 := by
  unfold tailWord_1852096
  simp only [CollatzResearch.WordTrace]
  refine ⟨33775745349089989829480071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45034327132119986439306761 33775745349089989829480071)
  ·
    refine ⟨50663618023634984744220107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33775745349089989829480071 50663618023634984744220107)
    ·
      refine ⟨75995427035452477116330161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50663618023634984744220107 75995427035452477116330161)
      ·
        refine ⟨56996570276589357837247621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75995427035452477116330161 56996570276589357837247621)
        ·
          refine ⟨10686856926860504594483929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56996570276589357837247621 10686856926860504594483929)
          ·
            refine ⟨8015142695145378445862947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10686856926860504594483929 8015142695145378445862947)
            ·
              refine ⟨12022714042718067668794421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8015142695145378445862947 12022714042718067668794421)
              ·
                refine ⟨1127129441504818843949477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12022714042718067668794421 1127129441504818843949477)
                ·
                  refine ⟨211336770282153533240527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127129441504818843949477 211336770282153533240527)
                  ·
                    rfl

theorem cell22_1852096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_1852096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852096 prefixEnd_1852096 := by exact prefixLift 1852096
  have htrace : WordTrace (prefixWord ++ tailWord_1852096) baseStart_1852096 baseEnd_1852096 := by
    simpa [prefixWord, tailWord_1852096, baseEnd_1852096] using wordTrace_append hprefix tailTrace_1852096
  have hstable : (prefixWord ++ tailWord_1852096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852096).length < 2 ^ (prefixWord ++ tailWord_1852096).sum := by decide
  have hdescent : baseEnd_1852096 < baseStart_1852096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852102 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1852102 : Nat := 118140960795 + 1852102 * 2 ^ 59
def prefixEnd_1852102 : Nat := 4983230072969 + 3 ^ 40 * 1852102 * 2
def baseEnd_1852102 : Nat := 211337454923026194690521

theorem tailTrace_1852102 : CollatzResearch.WordTrace tailWord_1852102 prefixEnd_1852102 211337454923026194690521 := by
  unfold tailWord_1852102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110990923004945083864955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45034473024105495122452373 2110990923004945083864955)
  ·
    refine ⟨3166486384507417625797433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110990923004945083864955 3166486384507417625797433)
    ·
      refine ⟨2374864788380563219348075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3166486384507417625797433 2374864788380563219348075)
      ·
        refine ⟨3562297182570844829022113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374864788380563219348075 3562297182570844829022113)
        ·
          refine ⟨2671722886928133621766585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3562297182570844829022113 2671722886928133621766585)
          ·
            refine ⟨2003792165196100216324939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2671722886928133621766585 2003792165196100216324939)
            ·
              refine ⟨3005688247794150324487409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003792165196100216324939 3005688247794150324487409)
              ·
                refine ⟨2254266185845612743365557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005688247794150324487409 2254266185845612743365557)
                ·
                  refine ⟨211337454923026194690521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254266185845612743365557 211337454923026194690521)
                  ·
                    rfl

theorem cell22_1852102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1852102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852102 prefixEnd_1852102 := by exact prefixLift 1852102
  have htrace : WordTrace (prefixWord ++ tailWord_1852102) baseStart_1852102 baseEnd_1852102 := by
    simpa [prefixWord, tailWord_1852102, baseEnd_1852102] using wordTrace_append hprefix tailTrace_1852102
  have hstable : (prefixWord ++ tailWord_1852102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852102).length < 2 ^ (prefixWord ++ tailWord_1852102).sum := by decide
  have hdescent : baseEnd_1852102 < baseStart_1852102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852169 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 7]
def baseStart_1852169 : Nat := 118140960795 + 1852169 * 2 ^ 59
def prefixEnd_1852169 : Nat := 4983230072969 + 3 ^ 40 * 1852169 * 2
def baseEnd_1852169 : Nat := 211345100079437580882119

theorem tailTrace_1852169 : CollatzResearch.WordTrace tailWord_1852169 prefixEnd_1852169 211345100079437580882119 := by
  unfold tailWord_1852169
  simp only [CollatzResearch.WordTrace]
  refine ⟨67554153226915513126367561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45036102151277008750911707 67554153226915513126367561)
  ·
    refine ⟨50665614920186634844775671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67554153226915513126367561 50665614920186634844775671)
    ·
      refine ⟨75998422380279952267163507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50665614920186634844775671 75998422380279952267163507)
      ·
        refine ⟨113997633570419928400745261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75998422380279952267163507 113997633570419928400745261)
        ·
          refine ⟨42749112588907473150279473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113997633570419928400745261 42749112588907473150279473)
          ·
            refine ⟨32061834441680604862709605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42749112588907473150279473 32061834441680604862709605)
            ·
              refine ⟨6011593957815113411758051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32061834441680604862709605 6011593957815113411758051)
              ·
                refine ⟨9017390936722670117637077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011593957815113411758051 9017390936722670117637077)
                ·
                  refine ⟨211345100079437580882119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9017390936722670117637077 211345100079437580882119)
                  ·
                    rfl

theorem cell22_1852169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_1852169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852169 prefixEnd_1852169 := by exact prefixLift 1852169
  have htrace : WordTrace (prefixWord ++ tailWord_1852169) baseStart_1852169 baseEnd_1852169 := by
    simpa [prefixWord, tailWord_1852169, baseEnd_1852169] using wordTrace_append hprefix tailTrace_1852169
  have hstable : (prefixWord ++ tailWord_1852169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852169).length < 2 ^ (prefixWord ++ tailWord_1852169).sum := by decide
  have hdescent : baseEnd_1852169 < baseStart_1852169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852184 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_1852184 : Nat := 118140960795 + 1852184 * 2 ^ 59
def prefixEnd_1852184 : Nat := 4983230072969 + 3 ^ 40 * 1852184 * 2
def baseEnd_1852184 : Nat := 634040435044857703521311

theorem tailTrace_1852184 : CollatzResearch.WordTrace tailWord_1852184 prefixEnd_1852184 634040435044857703521311 := by
  unfold tailWord_1852184
  simp only [CollatzResearch.WordTrace]
  refine ⟨33777350160930585344081803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45036466881240780458775737 33777350160930585344081803)
  ·
    refine ⟨50666025241395878016122705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33777350160930585344081803 50666025241395878016122705)
    ·
      refine ⟨37999518931046908512092029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50666025241395878016122705 37999518931046908512092029)
      ·
        refine ⟨14249819599142590692034511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37999518931046908512092029 14249819599142590692034511)
        ·
          refine ⟨21374729398713886038051767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14249819599142590692034511 21374729398713886038051767)
          ·
            refine ⟨32062094098070829057077651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21374729398713886038051767 32062094098070829057077651)
            ·
              refine ⟨48093141147106243585616477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32062094098070829057077651 48093141147106243585616477)
              ·
                refine ⟨18034927930164841344606179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48093141147106243585616477 18034927930164841344606179)
                ·
                  refine ⟨27052391895247262016909269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18034927930164841344606179 27052391895247262016909269)
                  ·
                    refine ⟨634040435044857703521311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27052391895247262016909269 634040435044857703521311)
                    ·
                      rfl

theorem cell22_1852184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_1852184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852184 prefixEnd_1852184 := by exact prefixLift 1852184
  have htrace : WordTrace (prefixWord ++ tailWord_1852184) baseStart_1852184 baseEnd_1852184 := by
    simpa [prefixWord, tailWord_1852184, baseEnd_1852184] using wordTrace_append hprefix tailTrace_1852184
  have hstable : (prefixWord ++ tailWord_1852184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852184).length < 2 ^ (prefixWord ++ tailWord_1852184).sum := by decide
  have hdescent : baseEnd_1852184 < baseStart_1852184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852186 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_1852186 : Nat := 118140960795 + 1852186 * 2 ^ 59
def prefixEnd_1852186 : Nat := 4983230072969 + 3 ^ 40 * 1852186 * 2
def baseEnd_1852186 : Nat := 211347039895243454990435

theorem tailTrace_1852186 : CollatzResearch.WordTrace tailWord_1852186 prefixEnd_1852186 211347039895243454990435 := by
  unfold tailWord_1852186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888693316963481257434103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45036515511902616686490941 16888693316963481257434103)
  ·
    refine ⟨25333039975445221886151155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16888693316963481257434103 25333039975445221886151155)
    ·
      refine ⟨37999559963167832829226733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25333039975445221886151155 37999559963167832829226733)
      ·
        refine ⟨14249834986187937310960025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37999559963167832829226733 14249834986187937310960025)
        ·
          refine ⟨10687376239640952983220019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14249834986187937310960025 10687376239640952983220019)
          ·
            refine ⟨16031064359461429474830029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10687376239640952983220019 16031064359461429474830029)
            ·
              refine ⟨6011649134798036053061261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16031064359461429474830029 6011649134798036053061261)
              ·
                refine ⟨2254368425549263519897973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6011649134798036053061261 2254368425549263519897973)
                ·
                  refine ⟨211347039895243454990435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254368425549263519897973 211347039895243454990435)
                  ·
                    rfl

theorem cell22_1852186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_1852186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852186 prefixEnd_1852186 := by exact prefixLift 1852186
  have htrace : WordTrace (prefixWord ++ tailWord_1852186) baseStart_1852186 baseEnd_1852186 := by
    simpa [prefixWord, tailWord_1852186, baseEnd_1852186] using wordTrace_append hprefix tailTrace_1852186
  have hstable : (prefixWord ++ tailWord_1852186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852186).length < 2 ^ (prefixWord ++ tailWord_1852186).sum := by decide
  have hdescent : baseEnd_1852186 < baseStart_1852186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852396 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_1852396 : Nat := 118140960795 + 1852396 * 2 ^ 59
def prefixEnd_1852396 : Nat := 4983230072969 + 3 ^ 40 * 1852396 * 2
def baseEnd_1852396 : Nat := 634113006977359817220661

theorem tailTrace_1852396 : CollatzResearch.WordTrace tailWord_1852396 prefixEnd_1852396 634113006977359817220661 := by
  unfold tailWord_1852396
  simp only [CollatzResearch.WordTrace]
  refine ⟨33781216298546565447440521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45041621731395420596587361 33781216298546565447440521)
  ·
    refine ⟨25335912223909924085580391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33781216298546565447440521 25335912223909924085580391)
    ·
      refine ⟨38003868335864886128370587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25335912223909924085580391 38003868335864886128370587)
      ·
        refine ⟨57005802503797329192555881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38003868335864886128370587 57005802503797329192555881)
        ·
          refine ⟨42754351877847996894416911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57005802503797329192555881 42754351877847996894416911)
          ·
            refine ⟨64131527816771995341625367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42754351877847996894416911 64131527816771995341625367)
            ·
              refine ⟨96197291725157993012438051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64131527816771995341625367 96197291725157993012438051)
              ·
                refine ⟨144295937587736989518657077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96197291725157993012438051 144295937587736989518657077)
                ·
                  refine ⟨13527744148850342767374101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144295937587736989518657077 13527744148850342767374101)
                  ·
                    refine ⟨634113006977359817220661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13527744148850342767374101 634113006977359817220661)
                    ·
                      rfl

theorem cell22_1852396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_1852396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852396 prefixEnd_1852396 := by exact prefixLift 1852396
  have htrace : WordTrace (prefixWord ++ tailWord_1852396) baseStart_1852396 baseEnd_1852396 := by
    simpa [prefixWord, tailWord_1852396, baseEnd_1852396] using wordTrace_append hprefix tailTrace_1852396
  have hstable : (prefixWord ++ tailWord_1852396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852396).length < 2 ^ (prefixWord ++ tailWord_1852396).sum := by decide
  have hdescent : baseEnd_1852396 < baseStart_1852396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852430 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1852430 : Nat := 118140960795 + 1852430 * 2 ^ 59
def prefixEnd_1852430 : Nat := 4983230072969 + 3 ^ 40 * 1852430 * 2
def baseEnd_1852430 : Nat := 634124645872195061870557

theorem tailTrace_1852430 : CollatzResearch.WordTrace tailWord_1852430 prefixEnd_1852430 634124645872195061870557 := by
  unfold tailWord_1852430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445459084871244337702343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45042448452646636467745829 8445459084871244337702343)
  ·
    refine ⟨12668188627306866506553515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8445459084871244337702343 12668188627306866506553515)
    ·
      refine ⟨19002282940960299759830273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12668188627306866506553515 19002282940960299759830273)
      ·
        refine ⟨14251712205720224819872705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19002282940960299759830273 14251712205720224819872705)
        ·
          refine ⟨10688784154290168614904529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14251712205720224819872705 10688784154290168614904529)
          ·
            refine ⟨8016588115717626461178397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10688784154290168614904529 8016588115717626461178397)
            ·
              refine ⟨3006220543394109922941899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8016588115717626461178397 3006220543394109922941899)
              ·
                refine ⟨4509330815091164884412849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006220543394109922941899 4509330815091164884412849)
                ·
                  refine ⟨3381998111318373663309637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4509330815091164884412849 3381998111318373663309637)
                  ·
                    refine ⟨634124645872195061870557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3381998111318373663309637 634124645872195061870557)
                    ·
                      rfl

theorem cell22_1852430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1852430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852430 prefixEnd_1852430 := by exact prefixLift 1852430
  have htrace : WordTrace (prefixWord ++ tailWord_1852430) baseStart_1852430 baseEnd_1852430 := by
    simpa [prefixWord, tailWord_1852430, baseEnd_1852430] using wordTrace_append hprefix tailTrace_1852430
  have hstable : (prefixWord ++ tailWord_1852430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852430).length < 2 ^ (prefixWord ++ tailWord_1852430).sum := by decide
  have hdescent : baseEnd_1852430 < baseStart_1852430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852460 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_1852460 : Nat := 118140960795 + 1852460 * 2 ^ 59
def prefixEnd_1852460 : Nat := 4983230072969 + 3 ^ 40 * 1852460 * 2
def baseEnd_1852460 : Nat := 634134915485284983620465

theorem tailTrace_1852460 : CollatzResearch.WordTrace tailWord_1852460 prefixEnd_1852460 634134915485284983620465 := by
  unfold tailWord_1852460
  simp only [CollatzResearch.WordTrace]
  refine ⟨33782383434430634912605417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45043177912574179883473889 33782383434430634912605417)
  ·
    refine ⟨25336787575822976184454063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33782383434430634912605417 25336787575822976184454063)
    ·
      refine ⟨38005181363734464276681095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25336787575822976184454063 38005181363734464276681095)
      ·
        refine ⟨57007772045601696415021643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38005181363734464276681095 57007772045601696415021643)
        ·
          refine ⟨85511658068402544622532465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57007772045601696415021643 85511658068402544622532465)
          ·
            refine ⟨64133743551301908466899349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85511658068402544622532465 64133743551301908466899349)
            ·
              refine ⟨3006269228967276959385907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64133743551301908466899349 3006269228967276959385907)
              ·
                refine ⟨4509403843450915439078861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006269228967276959385907 4509403843450915439078861)
                ·
                  refine ⟨1691026441294093289654573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4509403843450915439078861 1691026441294093289654573)
                  ·
                    refine ⟨634134915485284983620465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691026441294093289654573 634134915485284983620465)
                    ·
                      rfl

theorem cell22_1852460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_1852460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852460 prefixEnd_1852460 := by exact prefixLift 1852460
  have htrace : WordTrace (prefixWord ++ tailWord_1852460) baseStart_1852460 baseEnd_1852460 := by
    simpa [prefixWord, tailWord_1852460, baseEnd_1852460] using wordTrace_append hprefix tailTrace_1852460
  have hstable : (prefixWord ++ tailWord_1852460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852460).length < 2 ^ (prefixWord ++ tailWord_1852460).sum := by decide
  have hdescent : baseEnd_1852460 < baseStart_1852460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852503 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1852503 : Nat := 118140960795 + 1852503 * 2 ^ 59
def prefixEnd_1852503 : Nat := 4983230072969 + 3 ^ 40 * 1852503 * 2
def baseEnd_1852503 : Nat := 634149635264047204795333

theorem tailTrace_1852503 : CollatzResearch.WordTrace tailWord_1852503 prefixEnd_1852503 634149635264047204795333 := by
  unfold tailWord_1852503
  simp only [CollatzResearch.WordTrace]
  refine ⟨67566335207705488169026163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45044223471803658779350775 67566335207705488169026163)
  ·
    refine ⟨101349502811558232253539245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67566335207705488169026163 101349502811558232253539245)
    ·
      refine ⟨38006063554334337095077217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101349502811558232253539245 38006063554334337095077217)
      ·
        refine ⟨28504547665750752821307913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38006063554334337095077217 28504547665750752821307913)
        ·
          refine ⟨21378410749313064615980935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28504547665750752821307913 21378410749313064615980935)
          ·
            refine ⟨32067616123969596923971403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21378410749313064615980935 32067616123969596923971403)
            ·
              refine ⟨48101424185954395385957105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32067616123969596923971403 48101424185954395385957105)
              ·
                refine ⟨36076068139465796539467829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48101424185954395385957105 36076068139465796539467829)
                ·
                  refine ⟨3382131388074918425575109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36076068139465796539467829 3382131388074918425575109)
                  ·
                    refine ⟨634149635264047204795333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3382131388074918425575109 634149635264047204795333)
                    ·
                      rfl

theorem cell22_1852503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1852503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852503 prefixEnd_1852503 := by exact prefixLift 1852503
  have htrace : WordTrace (prefixWord ++ tailWord_1852503) baseStart_1852503 baseEnd_1852503 := by
    simpa [prefixWord, tailWord_1852503, baseEnd_1852503] using wordTrace_append hprefix tailTrace_1852503
  have hstable : (prefixWord ++ tailWord_1852503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852503).length < 2 ^ (prefixWord ++ tailWord_1852503).sum := by decide
  have hdescent : baseEnd_1852503 < baseStart_1852503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852567 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 2, 3]
def baseStart_1852567 : Nat := 118140960795 + 1852567 * 2 ^ 59
def prefixEnd_1852567 : Nat := 4983230072969 + 3 ^ 40 * 1852567 * 2
def baseEnd_1852567 : Nat := 634171543771972371195137

theorem tailTrace_1852567 : CollatzResearch.WordTrace tailWord_1852567 prefixEnd_1852567 634171543771972371195137 := by
  unfold tailWord_1852567
  simp only [CollatzResearch.WordTrace]
  refine ⟨67568669479473627099355955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45045779652982418066237303 67568669479473627099355955)
  ·
    refine ⟨101353004219210440649033933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67568669479473627099355955 101353004219210440649033933)
    ·
      refine ⟨38007376582203915243387725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101353004219210440649033933 38007376582203915243387725)
      ·
        refine ⟨14252766218326468216270397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38007376582203915243387725 14252766218326468216270397)
        ·
          refine ⟨5344787331872425581101399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14252766218326468216270397 5344787331872425581101399)
          ·
            refine ⟨8017180997808638371652099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344787331872425581101399 8017180997808638371652099)
            ·
              refine ⟨12025771496712957557478149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017180997808638371652099 12025771496712957557478149)
              ·
                refine ⟨2254832155633679542027153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12025771496712957557478149 2254832155633679542027153)
                ·
                  refine ⟨1691124116725259656520365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254832155633679542027153 1691124116725259656520365)
                  ·
                    refine ⟨634171543771972371195137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691124116725259656520365 634171543771972371195137)
                    ·
                      rfl

theorem cell22_1852567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_1852567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852567 prefixEnd_1852567 := by exact prefixLift 1852567
  have htrace : WordTrace (prefixWord ++ tailWord_1852567) baseStart_1852567 baseEnd_1852567 := by
    simpa [prefixWord, tailWord_1852567, baseEnd_1852567] using wordTrace_append hprefix tailTrace_1852567
  have hstable : (prefixWord ++ tailWord_1852567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852567).length < 2 ^ (prefixWord ++ tailWord_1852567).sum := by decide
  have hdescent : baseEnd_1852567 < baseStart_1852567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852580 : List Nat := [2, 3, 1, 2, 3, 1, 3, 7]
def baseStart_1852580 : Nat := 118140960795 + 1852580 * 2 ^ 59
def prefixEnd_1852580 : Nat := 4983230072969 + 3 ^ 40 * 1852580 * 2
def baseEnd_1852580 : Nat := 70463999326404963402233

theorem tailTrace_1852580 : CollatzResearch.WordTrace tailWord_1852580 prefixEnd_1852580 70463999326404963402233 := by
  unfold tailWord_1852580
  simp only [CollatzResearch.WordTrace]
  refine ⟨33784571814213265159789597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45046095752284353546386129 33784571814213265159789597)
  ·
    refine ⟨12669214430329974434921099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33784571814213265159789597 12669214430329974434921099)
    ·
      refine ⟨19003821645494961652381649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12669214430329974434921099 19003821645494961652381649)
      ·
        refine ⟨14252866234121221239286237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19003821645494961652381649 14252866234121221239286237)
        ·
          refine ⟨5344824837795457964732339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14252866234121221239286237 5344824837795457964732339)
          ·
            refine ⟨8017237256693186947098509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344824837795457964732339 8017237256693186947098509)
            ·
              refine ⟨3006463971259945105161941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8017237256693186947098509 3006463971259945105161941)
              ·
                refine ⟨70463999326404963402233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3006463971259945105161941 70463999326404963402233)
                ·
                  rfl

theorem cell22_1852580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_1852580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852580 prefixEnd_1852580 := by exact prefixLift 1852580
  have htrace : WordTrace (prefixWord ++ tailWord_1852580) baseStart_1852580 baseEnd_1852580 := by
    simpa [prefixWord, tailWord_1852580, baseEnd_1852580] using wordTrace_append hprefix tailTrace_1852580
  have hstable : (prefixWord ++ tailWord_1852580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852580).length < 2 ^ (prefixWord ++ tailWord_1852580).sum := by decide
  have hdescent : baseEnd_1852580 < baseStart_1852580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852595 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 5, 3]
def baseStart_1852595 : Nat := 118140960795 + 1852595 * 2 ^ 59
def prefixEnd_1852595 : Nat := 4983230072969 + 3 ^ 40 * 1852595 * 2
def baseEnd_1852595 : Nat := 634181128744189631495051

theorem tailTrace_1852595 : CollatzResearch.WordTrace tailWord_1852595 prefixEnd_1852595 634181128744189631495051 := by
  unfold tailWord_1852595
  simp only [CollatzResearch.WordTrace]
  refine ⟨67569690723372187881375239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45046460482248125254250159 67569690723372187881375239)
  ·
    refine ⟨101354536085058281822062859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67569690723372187881375239 101354536085058281822062859)
    ·
      refine ⟨152031804127587422733094289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101354536085058281822062859 152031804127587422733094289)
      ·
        refine ⟨114023853095690567049820717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152031804127587422733094289 114023853095690567049820717)
        ·
          refine ⟨42758944910883962643682769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114023853095690567049820717 42758944910883962643682769)
          ·
            refine ⟨32069208683162971982762077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42758944910883962643682769 32069208683162971982762077)
            ·
              refine ⟨12025953256186114493535779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32069208683162971982762077 12025953256186114493535779)
              ·
                refine ⟨18038929884279171740303669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12025953256186114493535779 18038929884279171740303669)
                ·
                  refine ⟨1691149676651172350653469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18038929884279171740303669 1691149676651172350653469)
                  ·
                    refine ⟨634181128744189631495051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691149676651172350653469 634181128744189631495051)
                    ·
                      rfl

theorem cell22_1852595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 3].length) (baseStart_1852595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852595 prefixEnd_1852595 := by exact prefixLift 1852595
  have htrace : WordTrace (prefixWord ++ tailWord_1852595) baseStart_1852595 baseEnd_1852595 := by
    simpa [prefixWord, tailWord_1852595, baseEnd_1852595] using wordTrace_append hprefix tailTrace_1852595
  have hstable : (prefixWord ++ tailWord_1852595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852595).length < 2 ^ (prefixWord ++ tailWord_1852595).sum := by decide
  have hdescent : baseEnd_1852595 < baseStart_1852595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852629 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_1852629 : Nat := 118140960795 + 1852629 * 2 ^ 59
def prefixEnd_1852629 : Nat := 4983230072969 + 3 ^ 40 * 1852629 * 2
def baseEnd_1852629 : Nat := 634192767639024876144947

theorem tailTrace_1852629 : CollatzResearch.WordTrace tailWord_1852629 prefixEnd_1852629 634192767639024876144947 := by
  unfold tailWord_1852629
  simp only [CollatzResearch.WordTrace]
  refine ⟨67570930805249011688112941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45047287203499341125408627 67570930805249011688112941)
  ·
    refine ⟨25339099051968379383042353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67570930805249011688112941 25339099051968379383042353)
    ·
      refine ⟨19004324288976284537281765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25339099051968379383042353 19004324288976284537281765)
      ·
        refine ⟨3563310804183053350740331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19004324288976284537281765 3563310804183053350740331)
        ·
          refine ⟨5344966206274580026110497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563310804183053350740331 5344966206274580026110497)
          ·
            refine ⟨4008724654705935019582873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344966206274580026110497 4008724654705935019582873)
            ·
              refine ⟨3006543491029451264687155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4008724654705935019582873 3006543491029451264687155)
              ·
                refine ⟨4509815236544176897030733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006543491029451264687155 4509815236544176897030733)
                ·
                  refine ⟨1691180713704066336386525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4509815236544176897030733 1691180713704066336386525)
                  ·
                    refine ⟨634192767639024876144947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691180713704066336386525 634192767639024876144947)
                    ·
                      rfl

theorem cell22_1852629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_1852629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852629 prefixEnd_1852629 := by exact prefixLift 1852629
  have htrace : WordTrace (prefixWord ++ tailWord_1852629) baseStart_1852629 baseEnd_1852629 := by
    simpa [prefixWord, tailWord_1852629, baseEnd_1852629] using wordTrace_append hprefix tailTrace_1852629
  have hstable : (prefixWord ++ tailWord_1852629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852629).length < 2 ^ (prefixWord ++ tailWord_1852629).sum := by decide
  have hdescent : baseEnd_1852629 < baseStart_1852629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852640 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_1852640 : Nat := 118140960795 + 1852640 * 2 ^ 59
def prefixEnd_1852640 : Nat := 4983230072969 + 3 ^ 40 * 1852640 * 2
def baseEnd_1852640 : Nat := 634196533163824514119913

theorem tailTrace_1852640 : CollatzResearch.WordTrace tailWord_1852640 prefixEnd_1852640 634196533163824514119913 := by
  unfold tailWord_1852640
  simp only [CollatzResearch.WordTrace]
  refine ⟨33785666004104580283381687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45047554672139440377842249 33785666004104580283381687)
  ·
    refine ⟨50678499006156870425072531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33785666004104580283381687 50678499006156870425072531)
    ·
      refine ⟨76017748509235305637608797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50678499006156870425072531 76017748509235305637608797)
      ·
        refine ⟨28506655690963239614103299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76017748509235305637608797 28506655690963239614103299)
        ·
          refine ⟨42759983536444859421154949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28506655690963239614103299 42759983536444859421154949)
          ·
            refine ⟨8017496913083411141466553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42759983536444859421154949 8017496913083411141466553)
            ·
              refine ⟨6013122684812558356099915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8017496913083411141466553 6013122684812558356099915)
              ·
                refine ⟨9019684027218837534149873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013122684812558356099915 9019684027218837534149873)
                ·
                  refine ⟨6764763020414128150612405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9019684027218837534149873 6764763020414128150612405)
                  ·
                    refine ⟨634196533163824514119913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6764763020414128150612405 634196533163824514119913)
                    ·
                      rfl

theorem cell22_1852640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_1852640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852640 prefixEnd_1852640 := by exact prefixLift 1852640
  have htrace : WordTrace (prefixWord ++ tailWord_1852640) baseStart_1852640 baseEnd_1852640 := by
    simpa [prefixWord, tailWord_1852640, baseEnd_1852640] using wordTrace_append hprefix tailTrace_1852640
  have hstable : (prefixWord ++ tailWord_1852640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852640).length < 2 ^ (prefixWord ++ tailWord_1852640).sum := by decide
  have hdescent : baseEnd_1852640 < baseStart_1852640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852700 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1852700 : Nat := 118140960795 + 1852700 * 2 ^ 59
def prefixEnd_1852700 : Nat := 4983230072969 + 3 ^ 40 * 1852700 * 2
def baseEnd_1852700 : Nat := 634217072390004357619729

theorem tailTrace_1852700 : CollatzResearch.WordTrace tailWord_1852700 prefixEnd_1852700 634217072390004357619729 := by
  unfold tailWord_1852700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33786760193995895406973777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45049013591994527209298369 33786760193995895406973777)
  ·
    refine ⟨25340070145496921555230333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33786760193995895406973777 25340070145496921555230333)
    ·
      refine ⟨9502526304561345583211375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25340070145496921555230333 9502526304561345583211375)
      ·
        refine ⟨14253789456842018374817063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9502526304561345583211375 14253789456842018374817063)
        ·
          refine ⟨21380684185263027562225595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14253789456842018374817063 21380684185263027562225595)
          ·
            refine ⟨32071026277894541343338393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21380684185263027562225595 32071026277894541343338393)
            ·
              refine ⟨24053269708420906007503795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32071026277894541343338393 24053269708420906007503795)
              ·
                refine ⟨36079904562631359011255693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24053269708420906007503795 36079904562631359011255693)
                ·
                  refine ⟨13529964210986759629220885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36079904562631359011255693 13529964210986759629220885)
                  ·
                    refine ⟨634217072390004357619729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13529964210986759629220885 634217072390004357619729)
                    ·
                      rfl

theorem cell22_1852700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1852700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852700 prefixEnd_1852700 := by exact prefixLift 1852700
  have htrace : WordTrace (prefixWord ++ tailWord_1852700) baseStart_1852700 baseEnd_1852700 := by
    simpa [prefixWord, tailWord_1852700, baseEnd_1852700] using wordTrace_append hprefix tailTrace_1852700
  have hstable : (prefixWord ++ tailWord_1852700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852700).length < 2 ^ (prefixWord ++ tailWord_1852700).sum := by decide
  have hdescent : baseEnd_1852700 < baseStart_1852700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852706 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1852706 : Nat := 118140960795 + 1852706 * 2 ^ 59
def prefixEnd_1852706 : Nat := 4983230072969 + 3 ^ 40 * 1852706 * 2
def baseEnd_1852706 : Nat := 634219126312622341969711

theorem tailTrace_1852706 : CollatzResearch.WordTrace tailWord_1852706 prefixEnd_1852706 634219126312622341969711 := by
  unfold tailWord_1852706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16893434806492513459666493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45049159483980035892443981 16893434806492513459666493)
  ·
    refine ⟨6335038052434692547374935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16893434806492513459666493 6335038052434692547374935)
    ·
      refine ⟨9502557078652038821062403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6335038052434692547374935 9502557078652038821062403)
      ·
        refine ⟨14253835617978058231593605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9502557078652038821062403 14253835617978058231593605)
        ·
          refine ⟨2672594178370885918423801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14253835617978058231593605 2672594178370885918423801)
          ·
            refine ⟨2004445633778164438817851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2672594178370885918423801 2004445633778164438817851)
            ·
              refine ⟨3006668450667246658226777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004445633778164438817851 3006668450667246658226777)
              ·
                refine ⟨2255001338000434993670083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006668450667246658226777 2255001338000434993670083)
                ·
                  refine ⟨3382502007000652490505125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255001338000434993670083 3382502007000652490505125)
                  ·
                    refine ⟨634219126312622341969711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3382502007000652490505125 634219126312622341969711)
                    ·
                      rfl

theorem cell22_1852706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1852706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852706 prefixEnd_1852706 := by exact prefixLift 1852706
  have htrace : WordTrace (prefixWord ++ tailWord_1852706) baseStart_1852706 baseEnd_1852706 := by
    simpa [prefixWord, tailWord_1852706, baseEnd_1852706] using wordTrace_append hprefix tailTrace_1852706
  have hstable : (prefixWord ++ tailWord_1852706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852706).length < 2 ^ (prefixWord ++ tailWord_1852706).sum := by decide
  have hdescent : baseEnd_1852706 < baseStart_1852706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852745 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_1852745 : Nat := 118140960795 + 1852745 * 2 ^ 59
def prefixEnd_1852745 : Nat := 4983230072969 + 3 ^ 40 * 1852745 * 2
def baseEnd_1852745 : Nat := 634232476809639240244591

theorem tailTrace_1852745 : CollatzResearch.WordTrace tailWord_1852745 prefixEnd_1852745 634232476809639240244591 := by
  unfold tailWord_1852745
  simp only [CollatzResearch.WordTrace]
  refine ⟨67575161672828763499335689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45050107781885842332890459 67575161672828763499335689)
  ·
    refine ⟨50681371254621572624501767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67575161672828763499335689 50681371254621572624501767)
    ·
      refine ⟨76022056881932358936752651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50681371254621572624501767 76022056881932358936752651)
      ·
        refine ⟨114033085322898538405128977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76022056881932358936752651 114033085322898538405128977)
        ·
          refine ⟨85524813992173903803846733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114033085322898538405128977 85524813992173903803846733)
          ·
            refine ⟨32071805247065213926442525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85524813992173903803846733 32071805247065213926442525)
            ·
              refine ⟨12026926967649455222415947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32071805247065213926442525 12026926967649455222415947)
              ·
                refine ⟨18040390451474182833623921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12026926967649455222415947 18040390451474182833623921)
                ·
                  refine ⟨13530292838605637125217941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18040390451474182833623921 13530292838605637125217941)
                  ·
                    refine ⟨634232476809639240244591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13530292838605637125217941 634232476809639240244591)
                    ·
                      rfl

theorem cell22_1852745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_1852745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852745 prefixEnd_1852745 := by exact prefixLift 1852745
  have htrace : WordTrace (prefixWord ++ tailWord_1852745) baseStart_1852745 baseEnd_1852745 := by
    simpa [prefixWord, tailWord_1852745, baseEnd_1852745] using wordTrace_append hprefix tailTrace_1852745
  have hstable : (prefixWord ++ tailWord_1852745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852745).length < 2 ^ (prefixWord ++ tailWord_1852745).sum := by decide
  have hdescent : baseEnd_1852745 < baseStart_1852745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852781 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_1852781 : Nat := 118140960795 + 1852781 * 2 ^ 59
def prefixEnd_1852781 : Nat := 4983230072969 + 3 ^ 40 * 1852781 * 2
def baseEnd_1852781 : Nat := 634244800345347146344481

theorem tailTrace_1852781 : CollatzResearch.WordTrace tailWord_1852781 prefixEnd_1852781 634244800345347146344481 := by
  unfold tailWord_1852781
  simp only [CollatzResearch.WordTrace]
  refine ⟨67576474700698341647646197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45050983133798894431764131 67576474700698341647646197)
  ·
    refine ⟨6335294503190469529466831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67576474700698341647646197 6335294503190469529466831)
    ·
      refine ⟨9502941754785704294200247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6335294503190469529466831 9502941754785704294200247)
      ·
        refine ⟨14254412632178556441300371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9502941754785704294200247 14254412632178556441300371)
        ·
          refine ⟨21381618948267834661950557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14254412632178556441300371 21381618948267834661950557)
          ·
            refine ⟨8018107105600437998231459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21381618948267834661950557 8018107105600437998231459)
            ·
              refine ⟨12027160658400656997347189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018107105600437998231459 12027160658400656997347189)
              ·
                refine ⟨1127546311725061593501299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12027160658400656997347189 1127546311725061593501299)
                ·
                  refine ⟨1691319467587592390251949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127546311725061593501299 1691319467587592390251949)
                  ·
                    refine ⟨634244800345347146344481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691319467587592390251949 634244800345347146344481)
                    ·
                      rfl

theorem cell22_1852781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_1852781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852781 prefixEnd_1852781 := by exact prefixLift 1852781
  have htrace : WordTrace (prefixWord ++ tailWord_1852781) baseStart_1852781 baseEnd_1852781 := by
    simpa [prefixWord, tailWord_1852781, baseEnd_1852781] using wordTrace_append hprefix tailTrace_1852781
  have hstable : (prefixWord ++ tailWord_1852781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852781).length < 2 ^ (prefixWord ++ tailWord_1852781).sum := by decide
  have hdescent : baseEnd_1852781 < baseStart_1852781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852886 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1852886 : Nat := 118140960795 + 1852886 * 2 ^ 59
def prefixEnd_1852886 : Nat := 4983230072969 + 3 ^ 40 * 1852886 * 2
def baseEnd_1852886 : Nat := 634280743991161872469159

theorem tailTrace_1852886 : CollatzResearch.WordTrace tailWord_1852886 prefixEnd_1852886 634280743991161872469159 := by
  unfold tailWord_1852886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223769022832371536263657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45053536243545296386812341 4223769022832371536263657)
  ·
    refine ⟨3167826767124278652197743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4223769022832371536263657 3167826767124278652197743)
    ·
      refine ⟨4751740150686417978296615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167826767124278652197743 4751740150686417978296615)
      ·
        refine ⟨7127610226029626967444923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751740150686417978296615 7127610226029626967444923)
        ·
          refine ⟨10691415339044440451167385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127610226029626967444923 10691415339044440451167385)
          ·
            refine ⟨8018561504283330338375539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10691415339044440451167385 8018561504283330338375539)
            ·
              refine ⟨12027842256424995507563309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018561504283330338375539 12027842256424995507563309)
              ·
                refine ⟨4510440846159373315336241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12027842256424995507563309 4510440846159373315336241)
                ·
                  refine ⟨3382830634619529986502181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510440846159373315336241 3382830634619529986502181)
                  ·
                    refine ⟨634280743991161872469159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3382830634619529986502181 634280743991161872469159)
                    ·
                      rfl

theorem cell22_1852886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1852886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852886 prefixEnd_1852886 := by exact prefixLift 1852886
  have htrace : WordTrace (prefixWord ++ tailWord_1852886) baseStart_1852886 baseEnd_1852886 := by
    simpa [prefixWord, tailWord_1852886, baseEnd_1852886] using wordTrace_append hprefix tailTrace_1852886
  have hstable : (prefixWord ++ tailWord_1852886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852886).length < 2 ^ (prefixWord ++ tailWord_1852886).sum := by decide
  have hdescent : baseEnd_1852886 < baseStart_1852886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852914 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1852914 : Nat := 118140960795 + 1852914 * 2 ^ 59
def prefixEnd_1852914 : Nat := 4983230072969 + 3 ^ 40 * 1852914 * 2
def baseEnd_1852914 : Nat := 634290328963379132769073

theorem tailTrace_1852914 : CollatzResearch.WordTrace tailWord_1852914 prefixEnd_1852914 634290328963379132769073 := by
  unfold tailWord_1852914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895331402304126340559449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45054217072811003574825197 16895331402304126340559449)
  ·
    refine ⟨12671498551728094755419587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16895331402304126340559449 12671498551728094755419587)
    ·
      refine ⟨19007247827592142133129381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671498551728094755419587 19007247827592142133129381)
      ·
        refine ⟨3563858967673526649961759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19007247827592142133129381 3563858967673526649961759)
        ·
          refine ⟨5345788451510289974942639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563858967673526649961759 5345788451510289974942639)
          ·
            refine ⟨8018682677265434962413959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345788451510289974942639 8018682677265434962413959)
            ·
              refine ⟨12028024015898152443620939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018682677265434962413959 12028024015898152443620939)
              ·
                refine ⟨18042036023847228665431409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12028024015898152443620939 18042036023847228665431409)
                ·
                  refine ⟨13531527017885421499073557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18042036023847228665431409 13531527017885421499073557)
                  ·
                    refine ⟨634290328963379132769073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13531527017885421499073557 634290328963379132769073)
                    ·
                      rfl

theorem cell22_1852914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1852914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852914 prefixEnd_1852914 := by exact prefixLift 1852914
  have htrace : WordTrace (prefixWord ++ tailWord_1852914) baseStart_1852914 baseEnd_1852914 := by
    simpa [prefixWord, tailWord_1852914, baseEnd_1852914] using wordTrace_append hprefix tailTrace_1852914
  have hstable : (prefixWord ++ tailWord_1852914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852914).length < 2 ^ (prefixWord ++ tailWord_1852914).sum := by decide
  have hdescent : baseEnd_1852914 < baseStart_1852914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852963 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 5]
def baseStart_1852963 : Nat := 118140960795 + 1852963 * 2 ^ 59
def prefixEnd_1852963 : Nat := 4983230072969 + 3 ^ 40 * 1852963 * 2
def baseEnd_1852963 : Nat := 211435700888253112764641

theorem tailTrace_1852963 : CollatzResearch.WordTrace tailWord_1852963 prefixEnd_1852963 211435700888253112764641 := by
  unfold tailWord_1852963
  simp only [CollatzResearch.WordTrace]
  refine ⟨67583112786038986730771543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45055408524025991153847695 67583112786038986730771543)
  ·
    refine ⟨101374669179058480096157315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67583112786038986730771543 101374669179058480096157315)
    ·
      refine ⟨152062003768587720144235973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101374669179058480096157315 152062003768587720144235973)
      ·
        refine ⟨28511625706610197527044245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152062003768587720144235973 28511625706610197527044245)
        ·
          refine ⟨1336482454997353009080199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28511625706610197527044245 1336482454997353009080199)
          ·
            refine ⟨2004723682496029513620299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336482454997353009080199 2004723682496029513620299)
            ·
              refine ⟨3007085523744044270430449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004723682496029513620299 3007085523744044270430449)
              ·
                refine ⟨2255314142808033202822837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3007085523744044270430449 2255314142808033202822837)
                ·
                  refine ⟨211435700888253112764641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2255314142808033202822837 211435700888253112764641)
                  ·
                    rfl

theorem cell22_1852963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 5].length) (baseStart_1852963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852963 prefixEnd_1852963 := by exact prefixLift 1852963
  have htrace : WordTrace (prefixWord ++ tailWord_1852963) baseStart_1852963 baseEnd_1852963 := by
    simpa [prefixWord, tailWord_1852963, baseEnd_1852963] using wordTrace_append hprefix tailTrace_1852963
  have hstable : (prefixWord ++ tailWord_1852963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852963).length < 2 ^ (prefixWord ++ tailWord_1852963).sum := by decide
  have hdescent : baseEnd_1852963 < baseStart_1852963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852972 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_1852972 : Nat := 118140960795 + 1852972 * 2 ^ 59
def prefixEnd_1852972 : Nat := 4983230072969 + 3 ^ 40 * 1852972 * 2
def baseEnd_1852972 : Nat := 634310183548686314818895

theorem tailTrace_1852972 : CollatzResearch.WordTrace tailWord_1852972 prefixEnd_1852972 634310183548686314818895 := by
  unfold tailWord_1852972
  simp only [CollatzResearch.WordTrace]
  refine ⟨33791720521503190633924585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45055627362004254178566113 33791720521503190633924585)
  ·
    refine ⟨25343790391127392975443439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33791720521503190633924585 25343790391127392975443439)
    ·
      refine ⟨38015685586691089463165159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25343790391127392975443439 38015685586691089463165159)
      ·
        refine ⟨57023528380036634194747739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38015685586691089463165159 57023528380036634194747739)
        ·
          refine ⟨85535292570054951292121609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57023528380036634194747739 85535292570054951292121609)
          ·
            refine ⟨64151469427541213469091207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85535292570054951292121609 64151469427541213469091207)
            ·
              refine ⟨96227204141311820203636811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64151469427541213469091207 96227204141311820203636811)
              ·
                refine ⟨144340806211967730305455217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96227204141311820203636811 144340806211967730305455217)
                ·
                  refine ⟨108255604658975797729091413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144340806211967730305455217 108255604658975797729091413)
                  ·
                    refine ⟨634310183548686314818895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 108255604658975797729091413 634310183548686314818895)
                    ·
                      rfl

theorem cell22_1852972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_1852972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1852972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1852972 prefixEnd_1852972 := by exact prefixLift 1852972
  have htrace : WordTrace (prefixWord ++ tailWord_1852972) baseStart_1852972 baseEnd_1852972 := by
    simpa [prefixWord, tailWord_1852972, baseEnd_1852972] using wordTrace_append hprefix tailTrace_1852972
  have hstable : (prefixWord ++ tailWord_1852972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852972).length < 2 ^ (prefixWord ++ tailWord_1852972).sum := by decide
  have hdescent : baseEnd_1852972 < baseStart_1852972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853004 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_1853004 : Nat := 118140960795 + 1853004 * 2 ^ 59
def prefixEnd_1853004 : Nat := 4983230072969 + 3 ^ 40 * 1853004 * 2
def baseEnd_1853004 : Nat := 634321137802648898018797

theorem tailTrace_1853004 : CollatzResearch.WordTrace tailWord_1853004 prefixEnd_1853004 634321137802648898018797 := by
  unfold tailWord_1853004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33792304089445225366507033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45056405452593633822009377 33792304089445225366507033)
  ·
    refine ⟨25344228067083919024880275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33792304089445225366507033 25344228067083919024880275)
    ·
      refine ⟨38016342100625878537320413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25344228067083919024880275 38016342100625878537320413)
      ·
        refine ⟨14256128287734704451495155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38016342100625878537320413 14256128287734704451495155)
        ·
          refine ⟨21384192431602056677242733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14256128287734704451495155 21384192431602056677242733)
          ·
            refine ⟨8019072161850771253966025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21384192431602056677242733 8019072161850771253966025)
            ·
              refine ⟨6014304121388078440474519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019072161850771253966025 6014304121388078440474519)
              ·
                refine ⟨9021456182082117660711779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014304121388078440474519 9021456182082117660711779)
                ·
                  refine ⟨13532184273123176491067669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021456182082117660711779 13532184273123176491067669)
                  ·
                    refine ⟨634321137802648898018797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13532184273123176491067669 634321137802648898018797)
                    ·
                      rfl

theorem cell22_1853004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_1853004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853004 prefixEnd_1853004 := by exact prefixLift 1853004
  have htrace : WordTrace (prefixWord ++ tailWord_1853004) baseStart_1853004 baseEnd_1853004 := by
    simpa [prefixWord, tailWord_1853004, baseEnd_1853004] using wordTrace_append hprefix tailTrace_1853004
  have hstable : (prefixWord ++ tailWord_1853004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853004).length < 2 ^ (prefixWord ++ tailWord_1853004).sum := by decide
  have hdescent : baseEnd_1853004 < baseStart_1853004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853040 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 2, 3]
def baseStart_1853040 : Nat := 118140960795 + 1853040 * 2 ^ 59
def prefixEnd_1853040 : Nat := 4983230072969 + 3 ^ 40 * 1853040 * 2
def baseEnd_1853040 : Nat := 634333461338356804118687

theorem tailTrace_1853040 : CollatzResearch.WordTrace tailWord_1853040 prefixEnd_1853040 634333461338356804118687 := by
  unfold tailWord_1853040
  simp only [CollatzResearch.WordTrace]
  refine ⟨33792960603380014440662287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45057280804506685920883049 33792960603380014440662287)
  ·
    refine ⟨50689440905070021660993431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33792960603380014440662287 50689440905070021660993431)
    ·
      refine ⟨76034161357605032491490147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50689440905070021660993431 76034161357605032491490147)
      ·
        refine ⟨114051242036407548737235221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76034161357605032491490147 114051242036407548737235221)
        ·
          refine ⟨5346151970456603847057901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114051242036407548737235221 5346151970456603847057901)
          ·
            refine ⟨2004806988921226442646713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5346151970456603847057901 2004806988921226442646713)
            ·
              refine ⟨1503605241690919831985035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004806988921226442646713 1503605241690919831985035)
              ·
                refine ⟨2255407862536379747977553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503605241690919831985035 2255407862536379747977553)
                ·
                  refine ⟨1691555896902284810983165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2255407862536379747977553 1691555896902284810983165)
                  ·
                    refine ⟨634333461338356804118687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691555896902284810983165 634333461338356804118687)
                    ·
                      rfl

theorem cell22_1853040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_1853040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853040 prefixEnd_1853040 := by exact prefixLift 1853040
  have htrace : WordTrace (prefixWord ++ tailWord_1853040) baseStart_1853040 baseEnd_1853040 := by
    simpa [prefixWord, tailWord_1853040, baseEnd_1853040] using wordTrace_append hprefix tailTrace_1853040
  have hstable : (prefixWord ++ tailWord_1853040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853040).length < 2 ^ (prefixWord ++ tailWord_1853040).sum := by decide
  have hdescent : baseEnd_1853040 < baseStart_1853040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853068 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_1853068 : Nat := 118140960795 + 1853068 * 2 ^ 59
def prefixEnd_1853068 : Nat := 4983230072969 + 3 ^ 40 * 1853068 * 2
def baseEnd_1853068 : Nat := 634343046310574064418601

theorem tailTrace_1853068 : CollatzResearch.WordTrace tailWord_1853068 prefixEnd_1853068 634343046310574064418601 := by
  unfold tailWord_1853068
  simp only [CollatzResearch.WordTrace]
  refine ⟨33793471225329294831671929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45057961633772393108895905 33793471225329294831671929)
  ·
    refine ⟨25345103418996971123753947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33793471225329294831671929 25345103418996971123753947)
    ·
      refine ⟨38017655128495456685630921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25345103418996971123753947 38017655128495456685630921)
      ·
        refine ⟨28513241346371592514223191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38017655128495456685630921 28513241346371592514223191)
        ·
          refine ⟨42769862019557388771334787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28513241346371592514223191 42769862019557388771334787)
          ·
            refine ⟨64154793029336083157002181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42769862019557388771334787 64154793029336083157002181)
            ·
              refine ⟨12029023693000515591937909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64154793029336083157002181 12029023693000515591937909)
              ·
                refine ⟨1127720971218798336744179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12029023693000515591937909 1127720971218798336744179)
                ·
                  refine ⟨1691581456828197505116269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127720971218798336744179 1691581456828197505116269)
                  ·
                    refine ⟨634343046310574064418601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691581456828197505116269 634343046310574064418601)
                    ·
                      rfl

theorem cell22_1853068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_1853068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853068 prefixEnd_1853068 := by exact prefixLift 1853068
  have htrace : WordTrace (prefixWord ++ tailWord_1853068) baseStart_1853068 baseEnd_1853068 := by
    simpa [prefixWord, tailWord_1853068, baseEnd_1853068] using wordTrace_append hprefix tailTrace_1853068
  have hstable : (prefixWord ++ tailWord_1853068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853068).length < 2 ^ (prefixWord ++ tailWord_1853068).sum := by decide
  have hdescent : baseEnd_1853068 < baseStart_1853068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853111 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1853111 : Nat := 118140960795 + 1853111 * 2 ^ 59
def prefixEnd_1853111 : Nat := 4983230072969 + 3 ^ 40 * 1853111 * 2
def baseEnd_1853111 : Nat := 634357766089336285593469

theorem tailTrace_1853111 : CollatzResearch.WordTrace tailWord_1853111 prefixEnd_1853111 634357766089336285593469 := by
  unfold tailWord_1853111
  simp only [CollatzResearch.WordTrace]
  refine ⟨67588510789502808007159187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45059007193001872004772791 67588510789502808007159187)
  ·
    refine ⟨101382766184254212010738781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67588510789502808007159187 101382766184254212010738781)
    ·
      refine ⟨38018537319095329504027043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101382766184254212010738781 38018537319095329504027043)
      ·
        refine ⟨57027805978642994256040565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38018537319095329504027043 57027805978642994256040565)
        ·
          refine ⟨5346356810497780711503803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57027805978642994256040565 5346356810497780711503803)
          ·
            refine ⟨8019535215746671067255705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346356810497780711503803 8019535215746671067255705)
            ·
              refine ⟨6014651411810003300441779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019535215746671067255705 6014651411810003300441779)
              ·
                refine ⟨9021977117715004950662669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014651411810003300441779 9021977117715004950662669)
                ·
                  refine ⟨3383241419143126856498501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9021977117715004950662669 3383241419143126856498501)
                  ·
                    refine ⟨634357766089336285593469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3383241419143126856498501 634357766089336285593469)
                    ·
                      rfl

theorem cell22_1853111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1853111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853111 prefixEnd_1853111 := by exact prefixLift 1853111
  have htrace : WordTrace (prefixWord ++ tailWord_1853111) baseStart_1853111 baseEnd_1853111 := by
    simpa [prefixWord, tailWord_1853111, baseEnd_1853111] using wordTrace_append hprefix tailTrace_1853111
  have hstable : (prefixWord ++ tailWord_1853111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853111).length < 2 ^ (prefixWord ++ tailWord_1853111).sum := by decide
  have hdescent : baseEnd_1853111 < baseStart_1853111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853171 : List Nat := [1, 1, 1, 2, 2, 3, 6, 6]
def baseStart_1853171 : Nat := 118140960795 + 1853171 * 2 ^ 59
def prefixEnd_1853171 : Nat := 4983230072969 + 3 ^ 40 * 1853171 * 2
def baseEnd_1853171 : Nat := 70486478368390681010365

theorem tailTrace_1853171 : CollatzResearch.WordTrace tailWord_1853171 prefixEnd_1853171 70486478368390681010365 := by
  unfold tailWord_1853171
  simp only [CollatzResearch.WordTrace]
  refine ⟨67590699169285438254343367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45060466112856958836228911 67590699169285438254343367)
  ·
    refine ⟨101386048753928157381515051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67590699169285438254343367 101386048753928157381515051)
    ·
      refine ⟨152079073130892236072272577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101386048753928157381515051 152079073130892236072272577)
      ·
        refine ⟨114059304848169177054204433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152079073130892236072272577 114059304848169177054204433)
        ·
          refine ⟨85544478636126882790653325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114059304848169177054204433 85544478636126882790653325)
          ·
            refine ⟨32079179488547581046494997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85544478636126882790653325 32079179488547581046494997)
            ·
              refine ⟨1503711538525667861554453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32079179488547581046494997 1503711538525667861554453)
              ·
                refine ⟨70486478368390681010365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1503711538525667861554453 70486478368390681010365)
                ·
                  rfl

theorem cell22_1853171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 6].length) (baseStart_1853171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853171 prefixEnd_1853171 := by exact prefixLift 1853171
  have htrace : WordTrace (prefixWord ++ tailWord_1853171) baseStart_1853171 baseEnd_1853171 := by
    simpa [prefixWord, tailWord_1853171, baseEnd_1853171] using wordTrace_append hprefix tailTrace_1853171
  have hstable : (prefixWord ++ tailWord_1853171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853171).length < 2 ^ (prefixWord ++ tailWord_1853171).sum := by decide
  have hdescent : baseEnd_1853171 < baseStart_1853171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853293 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1853293 : Nat := 118140960795 + 1853293 * 2 ^ 59
def prefixEnd_1853293 : Nat := 4983230072969 + 3 ^ 40 * 1853293 * 2
def baseEnd_1853293 : Nat := 634420068408748477542911

theorem tailTrace_1853293 : CollatzResearch.WordTrace tailWord_1853293 prefixEnd_1853293 634420068408748477542911 := by
  unfold tailWord_1853293
  simp only [CollatzResearch.WordTrace]
  refine ⟨67595148874843453090284533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45063432583228968726856355 67595148874843453090284533)
  ·
    refine ⟨6337045207016573727214175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67595148874843453090284533 6337045207016573727214175)
    ·
      refine ⟨9505567810524860590821263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337045207016573727214175 9505567810524860590821263)
      ·
        refine ⟨14258351715787290886231895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9505567810524860590821263 14258351715787290886231895)
        ·
          refine ⟨21387527573680936329347843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14258351715787290886231895 21387527573680936329347843)
          ·
            refine ⟨32081291360521404494021765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21387527573680936329347843 32081291360521404494021765)
            ·
              refine ⟨6015242130097763342629081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32081291360521404494021765 6015242130097763342629081)
              ·
                refine ⟨4511431597573322506971811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6015242130097763342629081 4511431597573322506971811)
                ·
                  refine ⟨6767147396359983760457717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511431597573322506971811 6767147396359983760457717)
                  ·
                    refine ⟨634420068408748477542911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6767147396359983760457717 634420068408748477542911)
                    ·
                      rfl

theorem cell22_1853293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1853293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853293 prefixEnd_1853293 := by exact prefixLift 1853293
  have htrace : WordTrace (prefixWord ++ tailWord_1853293) baseStart_1853293 baseEnd_1853293 := by
    simpa [prefixWord, tailWord_1853293, baseEnd_1853293] using wordTrace_append hprefix tailTrace_1853293
  have hstable : (prefixWord ++ tailWord_1853293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853293).length < 2 ^ (prefixWord ++ tailWord_1853293).sum := by decide
  have hdescent : baseEnd_1853293 < baseStart_1853293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853340 : List Nat := [2, 2, 3, 3, 1, 1, 4, 6]
def baseStart_1853340 : Nat := 118140960795 + 1853340 * 2 ^ 59
def prefixEnd_1853340 : Nat := 4983230072969 + 3 ^ 40 * 1853340 * 2
def baseEnd_1853340 : Nat := 70492906385472891290863

theorem tailTrace_1853340 : CollatzResearch.WordTrace tailWord_1853340 prefixEnd_1853340 70492906385472891290863 := by
  unfold tailWord_1853340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33798431552836590058622737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45064575403782120078163649 33798431552836590058622737)
  ·
    refine ⟨25348823664627442543967053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33798431552836590058622737 25348823664627442543967053)
    ·
      refine ⟨9505808874235290953987645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25348823664627442543967053 9505808874235290953987645)
      ·
        refine ⟨3564678327838234107745367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9505808874235290953987645 3564678327838234107745367)
        ·
          refine ⟨5347017491757351161618051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564678327838234107745367 5347017491757351161618051)
          ·
            refine ⟨8020526237636026742427077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347017491757351161618051 8020526237636026742427077)
            ·
              refine ⟨1503848669556755014205077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8020526237636026742427077 1503848669556755014205077)
              ·
                refine ⟨70492906385472891290863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1503848669556755014205077 70492906385472891290863)
                ·
                  rfl

theorem cell22_1853340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 6].length) (baseStart_1853340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853340 prefixEnd_1853340 := by exact prefixLift 1853340
  have htrace : WordTrace (prefixWord ++ tailWord_1853340) baseStart_1853340 baseEnd_1853340 := by
    simpa [prefixWord, tailWord_1853340, baseEnd_1853340] using wordTrace_append hprefix tailTrace_1853340
  have hstable : (prefixWord ++ tailWord_1853340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853340).length < 2 ^ (prefixWord ++ tailWord_1853340).sum := by decide
  have hdescent : baseEnd_1853340 < baseStart_1853340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853368 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_1853368 : Nat := 118140960795 + 1853368 * 2 ^ 59
def prefixEnd_1853368 : Nat := 4983230072969 + 3 ^ 40 * 1853368 * 2
def baseEnd_1853368 : Nat := 211481914147157760639227

theorem tailTrace_1853368 : CollatzResearch.WordTrace tailWord_1853368 prefixEnd_1853368 211481914147157760639227 := by
  unfold tailWord_1853368
  simp only [CollatzResearch.WordTrace]
  refine ⟨33798942174785870449632379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45065256233047827266176505 33798942174785870449632379)
  ·
    refine ⟨50698413262178805674448569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33798942174785870449632379 50698413262178805674448569)
    ·
      refine ⟨38023809946634104255836427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50698413262178805674448569 38023809946634104255836427)
      ·
        refine ⟨57035714919951156383754641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38023809946634104255836427 57035714919951156383754641)
        ·
          refine ⟨42776786189963367287815981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57035714919951156383754641 42776786189963367287815981)
          ·
            refine ⟨16041294821236262732930993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42776786189963367287815981 16041294821236262732930993)
            ·
              refine ⟨12030971115927197049698245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16041294821236262732930993 12030971115927197049698245)
              ·
                refine ⟨2255807084236349446818421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12030971115927197049698245 2255807084236349446818421)
                ·
                  refine ⟨211481914147157760639227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2255807084236349446818421 211481914147157760639227)
                  ·
                    rfl

theorem cell22_1853368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_1853368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853368 prefixEnd_1853368 := by exact prefixLift 1853368
  have htrace : WordTrace (prefixWord ++ tailWord_1853368) baseStart_1853368 baseEnd_1853368 := by
    simpa [prefixWord, tailWord_1853368, baseEnd_1853368] using wordTrace_append hprefix tailTrace_1853368
  have hstable : (prefixWord ++ tailWord_1853368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853368).length < 2 ^ (prefixWord ++ tailWord_1853368).sum := by decide
  have hdescent : baseEnd_1853368 < baseStart_1853368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853443 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 4, 4]
def baseStart_1853443 : Nat := 118140960795 + 1853443 * 2 ^ 59
def prefixEnd_1853443 : Nat := 4983230072969 + 3 ^ 40 * 1853443 * 2
def baseEnd_1853443 : Nat := 634471416474198086292451

theorem tailTrace_1853443 : CollatzResearch.WordTrace tailWord_1853443 prefixEnd_1853443 634471416474198086292451 := by
  unfold tailWord_1853443
  simp only [CollatzResearch.WordTrace]
  refine ⟨67600619824300028708244983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45067079882866685805496655 67600619824300028708244983)
  ·
    refine ⟨101400929736450043062367475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67600619824300028708244983 101400929736450043062367475)
    ·
      refine ⟨152101394604675064593551213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101400929736450043062367475 152101394604675064593551213)
      ·
        refine ⟨57038022976753149222581705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152101394604675064593551213 57038022976753149222581705)
        ·
          refine ⟨42778517232564861916936279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57038022976753149222581705 42778517232564861916936279)
          ·
            refine ⟨64167775848847292875404419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42778517232564861916936279 64167775848847292875404419)
            ·
              refine ⟨96251663773270939313106629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64167775848847292875404419 96251663773270939313106629)
              ·
                refine ⟨18047186957488301121207493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96251663773270939313106629 18047186957488301121207493)
                ·
                  refine ⟨3383847554529056460226405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18047186957488301121207493 3383847554529056460226405)
                  ·
                    refine ⟨634471416474198086292451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3383847554529056460226405 634471416474198086292451)
                    ·
                      rfl

theorem cell22_1853443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_1853443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853443 prefixEnd_1853443 := by exact prefixLift 1853443
  have htrace : WordTrace (prefixWord ++ tailWord_1853443) baseStart_1853443 baseEnd_1853443 := by
    simpa [prefixWord, tailWord_1853443, baseEnd_1853443] using wordTrace_append hprefix tailTrace_1853443
  have hstable : (prefixWord ++ tailWord_1853443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853443).length < 2 ^ (prefixWord ++ tailWord_1853443).sum := by decide
  have hdescent : baseEnd_1853443 < baseStart_1853443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853445 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_1853445 : Nat := 118140960795 + 1853445 * 2 ^ 59
def prefixEnd_1853445 : Nat := 4983230072969 + 3 ^ 40 * 1853445 * 2
def baseEnd_1853445 : Nat := 634472101115070747742445

theorem tailTrace_1853445 : CollatzResearch.WordTrace tailWord_1853445 prefixEnd_1853445 634472101115070747742445 := by
  unfold tailWord_1853445
  simp only [CollatzResearch.WordTrace]
  refine ⟨67600692770292783049817789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45067128513528522033211859 67600692770292783049817789)
  ·
    refine ⟨25350259788859793643681671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67600692770292783049817789 25350259788859793643681671)
    ·
      refine ⟨38025389683289690465522507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25350259788859793643681671 38025389683289690465522507)
      ·
        refine ⟨57038084524934535698283761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38025389683289690465522507 57038084524934535698283761)
        ·
          refine ⟨42778563393700901773712821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57038084524934535698283761 42778563393700901773712821)
          ·
            refine ⟨4010490318159459541285577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42778563393700901773712821 4010490318159459541285577)
            ·
              refine ⟨3007867738619594655964183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4010490318159459541285577 3007867738619594655964183)
              ·
                refine ⟨4511801607929391983946275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007867738619594655964183 4511801607929391983946275)
                ·
                  refine ⟨6767702411894087975919413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511801607929391983946275 6767702411894087975919413)
                  ·
                    refine ⟨634472101115070747742445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6767702411894087975919413 634472101115070747742445)
                    ·
                      rfl

theorem cell22_1853445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_1853445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853445 prefixEnd_1853445 := by exact prefixLift 1853445
  have htrace : WordTrace (prefixWord ++ tailWord_1853445) baseStart_1853445 baseEnd_1853445 := by
    simpa [prefixWord, tailWord_1853445, baseEnd_1853445] using wordTrace_append hprefix tailTrace_1853445
  have hstable : (prefixWord ++ tailWord_1853445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853445).length < 2 ^ (prefixWord ++ tailWord_1853445).sum := by decide
  have hdescent : baseEnd_1853445 < baseStart_1853445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853479 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1853479 : Nat := 118140960795 + 1853479 * 2 ^ 59
def prefixEnd_1853479 : Nat := 4983230072969 + 3 ^ 40 * 1853479 * 2
def baseEnd_1853479 : Nat := 634483740009905992392341

theorem tailTrace_1853479 : CollatzResearch.WordTrace tailWord_1853479 prefixEnd_1853479 634483740009905992392341 := by
  unfold tailWord_1853479
  simp only [CollatzResearch.WordTrace]
  refine ⟨67601932852169606856555491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45067955234779737904370327 67601932852169606856555491)
  ·
    refine ⟨101402899278254410284833237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67601932852169606856555491 101402899278254410284833237)
    ·
      refine ⟨2376630451834087741050779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101402899278254410284833237 2376630451834087741050779)
      ·
        refine ⟨3564945677751131611576169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376630451834087741050779 3564945677751131611576169)
        ·
          refine ⟨2673709258313348708682127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3564945677751131611576169 2673709258313348708682127)
          ·
            refine ⟨4010563887470023063023191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673709258313348708682127 4010563887470023063023191)
            ·
              refine ⟨6015845831205034594534787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010563887470023063023191 6015845831205034594534787)
              ·
                refine ⟨9023768746807551891802181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015845831205034594534787 9023768746807551891802181)
                ·
                  refine ⟨1691956640026415979712909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9023768746807551891802181 1691956640026415979712909)
                  ·
                    refine ⟨634483740009905992392341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1691956640026415979712909 634483740009905992392341)
                    ·
                      rfl

theorem cell22_1853479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1853479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853479 prefixEnd_1853479 := by exact prefixLift 1853479
  have htrace : WordTrace (prefixWord ++ tailWord_1853479) baseStart_1853479 baseEnd_1853479 := by
    simpa [prefixWord, tailWord_1853479, baseEnd_1853479] using wordTrace_append hprefix tailTrace_1853479
  have hstable : (prefixWord ++ tailWord_1853479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853479).length < 2 ^ (prefixWord ++ tailWord_1853479).sum := by decide
  have hdescent : baseEnd_1853479 < baseStart_1853479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853541 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_1853541 : Nat := 118140960795 + 1853541 * 2 ^ 59
def prefixEnd_1853541 : Nat := 4983230072969 + 3 ^ 40 * 1853541 * 2
def baseEnd_1853541 : Nat := 634504963876958497342151

theorem tailTrace_1853541 : CollatzResearch.WordTrace tailWord_1853541 prefixEnd_1853541 634504963876958497342151 := by
  unfold tailWord_1853541
  simp only [CollatzResearch.WordTrace]
  refine ⟨67604194177944991445312477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45069462785296660963541651 67604194177944991445312477)
  ·
    refine ⟨25351572816729371791992179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67604194177944991445312477 25351572816729371791992179)
    ·
      refine ⟨38027359225094057687988269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25351572816729371791992179 38027359225094057687988269)
      ·
        refine ⟨14260259709410271632995601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38027359225094057687988269 14260259709410271632995601)
        ·
          refine ⟨10695194782057703724746701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14260259709410271632995601 10695194782057703724746701)
          ·
            refine ⟨4010698043271638896780013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10695194782057703724746701 4010698043271638896780013)
            ·
              refine ⟨1504011766226864586292505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4010698043271638896780013 1504011766226864586292505)
              ·
                refine ⟨1128008824670148439719379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504011766226864586292505 1128008824670148439719379)
                ·
                  refine ⟨1692013237005222659579069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128008824670148439719379 1692013237005222659579069)
                  ·
                    refine ⟨634504963876958497342151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692013237005222659579069 634504963876958497342151)
                    ·
                      rfl

theorem cell22_1853541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_1853541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853541 prefixEnd_1853541 := by exact prefixLift 1853541
  have htrace : WordTrace (prefixWord ++ tailWord_1853541) baseStart_1853541 baseEnd_1853541 := by
    simpa [prefixWord, tailWord_1853541, baseEnd_1853541] using wordTrace_append hprefix tailTrace_1853541
  have hstable : (prefixWord ++ tailWord_1853541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853541).length < 2 ^ (prefixWord ++ tailWord_1853541).sum := by decide
  have hdescent : baseEnd_1853541 < baseStart_1853541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853554 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1853554 : Nat := 118140960795 + 1853554 * 2 ^ 59
def prefixEnd_1853554 : Nat := 4983230072969 + 3 ^ 40 * 1853554 * 2
def baseEnd_1853554 : Nat := 211503138014210265589037

theorem tailTrace_1853554 : CollatzResearch.WordTrace tailWord_1853554 prefixEnd_1853554 211503138014210265589037 := by
  unfold tailWord_1853554
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901167081724473666383929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45069778884598596443690477 16901167081724473666383929)
  ·
    refine ⟨12675875311293355249787947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16901167081724473666383929 12675875311293355249787947)
    ·
      refine ⟨19013812966940032874681921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12675875311293355249787947 19013812966940032874681921)
      ·
        refine ⟨14260359725205024656011441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19013812966940032874681921 14260359725205024656011441)
        ·
          refine ⟨10695269793903768492008581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14260359725205024656011441 10695269793903768492008581)
          ·
            refine ⟨2005363086356956592251609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10695269793903768492008581 2005363086356956592251609)
            ·
              refine ⟨1504022314767717444188707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005363086356956592251609 1504022314767717444188707)
              ·
                refine ⟨2256033472151576166283061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504022314767717444188707 2256033472151576166283061)
                ·
                  refine ⟨211503138014210265589037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2256033472151576166283061 211503138014210265589037)
                  ·
                    rfl

theorem cell22_1853554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1853554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853554 prefixEnd_1853554 := by exact prefixLift 1853554
  have htrace : WordTrace (prefixWord ++ tailWord_1853554) baseStart_1853554 baseEnd_1853554 := by
    simpa [prefixWord, tailWord_1853554, baseEnd_1853554] using wordTrace_append hprefix tailTrace_1853554
  have hstable : (prefixWord ++ tailWord_1853554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853554).length < 2 ^ (prefixWord ++ tailWord_1853554).sum := by decide
  have hdescent : baseEnd_1853554 < baseStart_1853554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853595 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 2, 4]
def baseStart_1853595 : Nat := 118140960795 + 1853595 * 2 ^ 59
def prefixEnd_1853595 : Nat := 4983230072969 + 3 ^ 40 * 1853595 * 2
def baseEnd_1853595 : Nat := 634523449180520356491985

theorem tailTrace_1853595 : CollatzResearch.WordTrace tailWord_1853595 prefixEnd_1853595 634523449180520356491985 := by
  unfold tailWord_1853595
  simp only [CollatzResearch.WordTrace]
  refine ⟨67606163719749358667778239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45070775813166239111852159 67606163719749358667778239)
  ·
    refine ⟨101409245579624038001667359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67606163719749358667778239 101409245579624038001667359)
    ·
      refine ⟨152113868369436057002501039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101409245579624038001667359 152113868369436057002501039)
      ·
        refine ⟨228170802554154085503751559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152113868369436057002501039 228170802554154085503751559)
        ·
          refine ⟨342256203831231128255627339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228170802554154085503751559 342256203831231128255627339)
          ·
            refine ⟨513384305746846692383441009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342256203831231128255627339 513384305746846692383441009)
            ·
              refine ⟨385038229310135019287580757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513384305746846692383441009 385038229310135019287580757)
              ·
                refine ⟨4512166749728144757276337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 385038229310135019287580757 4512166749728144757276337)
                ·
                  refine ⟨3384125062296108567957253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4512166749728144757276337 3384125062296108567957253)
                  ·
                    refine ⟨634523449180520356491985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384125062296108567957253 634523449180520356491985)
                    ·
                      rfl

theorem cell22_1853595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_1853595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853595 prefixEnd_1853595 := by exact prefixLift 1853595
  have htrace : WordTrace (prefixWord ++ tailWord_1853595) baseStart_1853595 baseEnd_1853595 := by
    simpa [prefixWord, tailWord_1853595, baseEnd_1853595] using wordTrace_append hprefix tailTrace_1853595
  have hstable : (prefixWord ++ tailWord_1853595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853595).length < 2 ^ (prefixWord ++ tailWord_1853595).sum := by decide
  have hdescent : baseEnd_1853595 < baseStart_1853595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853599 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 4]
def baseStart_1853599 : Nat := 118140960795 + 1853599 * 2 ^ 59
def prefixEnd_1853599 : Nat := 4983230072969 + 3 ^ 40 * 1853599 * 2
def baseEnd_1853599 : Nat := 211508272820755226463991

theorem tailTrace_1853599 : CollatzResearch.WordTrace tailWord_1853599 prefixEnd_1853599 211508272820755226463991 := by
  unfold tailWord_1853599
  simp only [CollatzResearch.WordTrace]
  refine ⟨67606309611734867350923851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45070873074489911567282567 67606309611734867350923851)
  ·
    refine ⟨101409464417602301026385777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67606309611734867350923851 101409464417602301026385777)
    ·
      refine ⟨76057098313201725769789333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101409464417602301026385777 76057098313201725769789333)
      ·
        refine ⟨3565176483431330895458875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76057098313201725769789333 3565176483431330895458875)
        ·
          refine ⟨5347764725146996343188313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565176483431330895458875 5347764725146996343188313)
          ·
            refine ⟨4010823543860247257391235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5347764725146996343188313 4010823543860247257391235)
            ·
              refine ⟨6016235315790370886086853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010823543860247257391235 6016235315790370886086853)
              ·
                refine ⟨1128044121710694541141285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6016235315790370886086853 1128044121710694541141285)
                ·
                  refine ⟨211508272820755226463991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128044121710694541141285 211508272820755226463991)
                  ·
                    rfl

theorem cell22_1853599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 4].length) (baseStart_1853599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853599 prefixEnd_1853599 := by exact prefixLift 1853599
  have htrace : WordTrace (prefixWord ++ tailWord_1853599) baseStart_1853599 baseEnd_1853599 := by
    simpa [prefixWord, tailWord_1853599, baseEnd_1853599] using wordTrace_append hprefix tailTrace_1853599
  have hstable : (prefixWord ++ tailWord_1853599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853599).length < 2 ^ (prefixWord ++ tailWord_1853599).sum := by decide
  have hdescent : baseEnd_1853599 < baseStart_1853599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853642 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_1853642 : Nat := 118140960795 + 1853642 * 2 ^ 59
def prefixEnd_1853642 : Nat := 4983230072969 + 3 ^ 40 * 1853642 * 2
def baseEnd_1853642 : Nat := 634539538241027900566841

theorem tailTrace_1853642 : CollatzResearch.WordTrace tailWord_1853642 prefixEnd_1853642 634539538241027900566841 := by
  unfold tailWord_1853642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901969487644771423684795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45071918633719390463159453 16901969487644771423684795)
  ·
    refine ⟨25352954231467157135527193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16901969487644771423684795 25352954231467157135527193)
    ·
      refine ⟨19014715673600367851645395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25352954231467157135527193 19014715673600367851645395)
      ·
        refine ⟨28522073510400551777468093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19014715673600367851645395 28522073510400551777468093)
        ·
          refine ⟨10695777566400206916550535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28522073510400551777468093 10695777566400206916550535)
          ·
            refine ⟨16043666349600310374825803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10695777566400206916550535 16043666349600310374825803)
            ·
              refine ⟨24065499524400465562238705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16043666349600310374825803 24065499524400465562238705)
              ·
                refine ⟨18049124643300349171679029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24065499524400465562238705 18049124643300349171679029)
                ·
                  refine ⟨1692105435309407734844909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18049124643300349171679029 1692105435309407734844909)
                  ·
                    refine ⟨634539538241027900566841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692105435309407734844909 634539538241027900566841)
                    ·
                      rfl

theorem cell22_1853642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_1853642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853642 prefixEnd_1853642 := by exact prefixLift 1853642
  have htrace : WordTrace (prefixWord ++ tailWord_1853642) baseStart_1853642 baseEnd_1853642 := by
    simpa [prefixWord, tailWord_1853642, baseEnd_1853642] using wordTrace_append hprefix tailTrace_1853642
  have hstable : (prefixWord ++ tailWord_1853642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853642).length < 2 ^ (prefixWord ++ tailWord_1853642).sum := by decide
  have hdescent : baseEnd_1853642 < baseStart_1853642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853717 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 6]
def baseStart_1853717 : Nat := 118140960795 + 1853717 * 2 ^ 59
def prefixEnd_1853717 : Nat := 4983230072969 + 3 ^ 40 * 1853717 * 2
def baseEnd_1853717 : Nat := 211521737424584234980537

theorem tailTrace_1853717 : CollatzResearch.WordTrace tailWord_1853717 prefixEnd_1853717 211521737424584234980537 := by
  unfold tailWord_1853717
  simp only [CollatzResearch.WordTrace]
  refine ⟨67610613425307373503719405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45073742283538249002479603 67610613425307373503719405)
  ·
    refine ⟨25353980034490265063894777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67610613425307373503719405 25353980034490265063894777)
    ·
      refine ⟨19015485025867698797921083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25353980034490265063894777 19015485025867698797921083)
      ·
        refine ⟨28523227538801548196881625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19015485025867698797921083 28523227538801548196881625)
        ·
          refine ⟨21392420654101161147661219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28523227538801548196881625 21392420654101161147661219)
          ·
            refine ⟨32088630981151741721491829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21392420654101161147661219 32088630981151741721491829)
            ·
              refine ⟨3008309154482975786389859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32088630981151741721491829 3008309154482975786389859)
              ·
                refine ⟨4512463731724463679584789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008309154482975786389859 4512463731724463679584789)
                ·
                  refine ⟨211521737424584234980537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4512463731724463679584789 211521737424584234980537)
                  ·
                    rfl

theorem cell22_1853717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_1853717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853717 prefixEnd_1853717 := by exact prefixLift 1853717
  have htrace : WordTrace (prefixWord ++ tailWord_1853717) baseStart_1853717 baseEnd_1853717 := by
    simpa [prefixWord, tailWord_1853717, baseEnd_1853717] using wordTrace_append hprefix tailTrace_1853717
  have hstable : (prefixWord ++ tailWord_1853717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853717).length < 2 ^ (prefixWord ++ tailWord_1853717).sum := by decide
  have hdescent : baseEnd_1853717 < baseStart_1853717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853886 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1853886 : Nat := 118140960795 + 1853886 * 2 ^ 59
def prefixEnd_1853886 : Nat := 4983230072969 + 3 ^ 40 * 1853886 * 2
def baseEnd_1853886 : Nat := 211541021475830865822031

theorem tailTrace_1853886 : CollatzResearch.WordTrace tailWord_1853886 prefixEnd_1853886 211541021475830865822031 := by
  unfold tailWord_1853886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8452097170211889420827689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45077851574463410244414341 8452097170211889420827689)
  ·
    refine ⟨6339072877658917065620767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8452097170211889420827689 6339072877658917065620767)
    ·
      refine ⟨9508609316488375598431151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6339072877658917065620767 9508609316488375598431151)
      ·
        refine ⟨14262913974732563397646727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9508609316488375598431151 14262913974732563397646727)
        ·
          refine ⟨21394370962098845096470091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262913974732563397646727 21394370962098845096470091)
          ·
            refine ⟨32091556443148267644705137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21394370962098845096470091 32091556443148267644705137)
            ·
              refine ⟨24068667332361200733528853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32091556443148267644705137 24068667332361200733528853)
              ·
                refine ⟨1128218781204431284384165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24068667332361200733528853 1128218781204431284384165)
                ·
                  refine ⟨211541021475830865822031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128218781204431284384165 211541021475830865822031)
                  ·
                    rfl

theorem cell22_1853886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1853886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853886 prefixEnd_1853886 := by exact prefixLift 1853886
  have htrace : WordTrace (prefixWord ++ tailWord_1853886) baseStart_1853886 baseEnd_1853886 := by
    simpa [prefixWord, tailWord_1853886, baseEnd_1853886] using wordTrace_append hprefix tailTrace_1853886
  have hstable : (prefixWord ++ tailWord_1853886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853886).length < 2 ^ (prefixWord ++ tailWord_1853886).sum := by decide
  have hdescent : baseEnd_1853886 < baseStart_1853886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853897 : List Nat := [1, 2, 1, 1, 2, 1, 5, 9]
def baseStart_1853897 : Nat := 118140960795 + 1853897 * 2 ^ 59
def prefixEnd_1853897 : Nat := 4983230072969 + 3 ^ 40 * 1853897 * 2
def baseEnd_1853897 : Nat := 70514092216921359493451

theorem tailTrace_1853897 : CollatzResearch.WordTrace tailWord_1853897 prefixEnd_1853897 70514092216921359493451 := by
  unfold tailWord_1853897
  simp only [CollatzResearch.WordTrace]
  refine ⟨67617178564655264245271945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45078119043103509496847963 67617178564655264245271945)
  ·
    refine ⟨50712883923491448183953959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67617178564655264245271945 50712883923491448183953959)
    ·
      refine ⟨76069325885237172275930939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50712883923491448183953959 76069325885237172275930939)
      ·
        refine ⟨114103988827855758413896409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76069325885237172275930939 114103988827855758413896409)
        ·
          refine ⟨85577991620891818810422307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114103988827855758413896409 85577991620891818810422307)
          ·
            refine ⟨128366987431337728215633461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85577991620891818810422307 128366987431337728215633461)
            ·
              refine ⟨12034405071687912020215637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128366987431337728215633461 12034405071687912020215637)
              ·
                refine ⟨70514092216921359493451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12034405071687912020215637 70514092216921359493451)
                ·
                  rfl

theorem cell22_1853897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 9].length) (baseStart_1853897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853897 prefixEnd_1853897 := by exact prefixLift 1853897
  have htrace : WordTrace (prefixWord ++ tailWord_1853897) baseStart_1853897 baseEnd_1853897 := by
    simpa [prefixWord, tailWord_1853897, baseEnd_1853897] using wordTrace_append hprefix tailTrace_1853897
  have hstable : (prefixWord ++ tailWord_1853897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853897).length < 2 ^ (prefixWord ++ tailWord_1853897).sum := by decide
  have hdescent : baseEnd_1853897 < baseStart_1853897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853922 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1853922 : Nat := 118140960795 + 1853922 * 2 ^ 59
def prefixEnd_1853922 : Nat := 4983230072969 + 3 ^ 40 * 1853922 * 2
def baseEnd_1853922 : Nat := 634635387963200503565983

theorem tailTrace_1853922 : CollatzResearch.WordTrace tailWord_1853922 prefixEnd_1853922 634635387963200503565983 := by
  unfold tailWord_1853922
  simp only [CollatzResearch.WordTrace]
  refine ⟨16904522597391173378733005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45078726926376462343288013 16904522597391173378733005)
  ·
    refine ⟨6339195974021690017024877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16904522597391173378733005 6339195974021690017024877)
    ·
      refine ⟨2377198490258133756384329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6339195974021690017024877 2377198490258133756384329)
      ·
        refine ⟨1782898867693600317288247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2377198490258133756384329 1782898867693600317288247)
        ·
          refine ⟨2674348301540400475932371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782898867693600317288247 2674348301540400475932371)
          ·
            refine ⟨4011522452310600713898557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674348301540400475932371 4011522452310600713898557)
            ·
              refine ⟨1504320919616475267711959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4011522452310600713898557 1504320919616475267711959)
              ·
                refine ⟨2256481379424712901567939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504320919616475267711959 2256481379424712901567939)
                ·
                  refine ⟨3384722069137069352351909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256481379424712901567939 3384722069137069352351909)
                  ·
                    refine ⟨634635387963200503565983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384722069137069352351909 634635387963200503565983)
                    ·
                      rfl

theorem cell22_1853922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1853922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853922 prefixEnd_1853922 := by exact prefixLift 1853922
  have htrace : WordTrace (prefixWord ++ tailWord_1853922) baseStart_1853922 baseEnd_1853922 := by
    simpa [prefixWord, tailWord_1853922, baseEnd_1853922] using wordTrace_append hprefix tailTrace_1853922
  have hstable : (prefixWord ++ tailWord_1853922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853922).length < 2 ^ (prefixWord ++ tailWord_1853922).sum := by decide
  have hdescent : baseEnd_1853922 < baseStart_1853922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853929 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_1853929 : Nat := 118140960795 + 1853929 * 2 ^ 59
def prefixEnd_1853929 : Nat := 4983230072969 + 3 ^ 40 * 1853929 * 2
def baseEnd_1853929 : Nat := 634637784206254818640961

theorem tailTrace_1853929 : CollatzResearch.WordTrace tailWord_1853929 prefixEnd_1853929 634637784206254818640961 := by
  unfold tailWord_1853929
  simp only [CollatzResearch.WordTrace]
  refine ⟨67618345700539333710436841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45078897133692889140291227 67618345700539333710436841)
  ·
    refine ⟨50713759275404500282827631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67618345700539333710436841 50713759275404500282827631)
    ·
      refine ⟨76070638913106750424241447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50713759275404500282827631 76070638913106750424241447)
      ·
        refine ⟨114105958369660125636362171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76070638913106750424241447 114105958369660125636362171)
        ·
          refine ⟨171158937554490188454543257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114105958369660125636362171 171158937554490188454543257)
          ·
            refine ⟨128369203165867641340907443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171158937554490188454543257 128369203165867641340907443)
            ·
              refine ⟨192553804748801462011361165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128369203165867641340907443 192553804748801462011361165)
              ·
                refine ⟨72207676780800548254260437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192553804748801462011361165 72207676780800548254260437)
                ·
                  refine ⟨1692367424550012849709229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 72207676780800548254260437 1692367424550012849709229)
                  ·
                    refine ⟨634637784206254818640961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692367424550012849709229 634637784206254818640961)
                    ·
                      rfl

theorem cell22_1853929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_1853929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853929 prefixEnd_1853929 := by exact prefixLift 1853929
  have htrace : WordTrace (prefixWord ++ tailWord_1853929) baseStart_1853929 baseEnd_1853929 := by
    simpa [prefixWord, tailWord_1853929, baseEnd_1853929] using wordTrace_append hprefix tailTrace_1853929
  have hstable : (prefixWord ++ tailWord_1853929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853929).length < 2 ^ (prefixWord ++ tailWord_1853929).sum := by decide
  have hdescent : baseEnd_1853929 < baseStart_1853929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853965 : List Nat := [1, 7, 1, 1, 1, 2, 3, 6]
def baseStart_1853965 : Nat := 118140960795 + 1853965 * 2 ^ 59
def prefixEnd_1853965 : Nat := 4983230072969 + 3 ^ 40 * 1853965 * 2
def baseEnd_1853965 : Nat := 70516678637995858304539

theorem tailTrace_1853965 : CollatzResearch.WordTrace tailWord_1853965 prefixEnd_1853965 70516678637995858304539 := by
  unfold tailWord_1853965
  simp only [CollatzResearch.WordTrace]
  refine ⟨67619658728408911858747349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45079772485605941239164899 67619658728408911858747349)
  ·
    refine ⟨1584835751447083871689391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67619658728408911858747349 1584835751447083871689391)
    ·
      refine ⟨2377253627170625807534087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584835751447083871689391 2377253627170625807534087)
      ·
        refine ⟨3565880440755938711301131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377253627170625807534087 3565880440755938711301131)
        ·
          refine ⟨5348820661133908066951697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565880440755938711301131 5348820661133908066951697)
          ·
            refine ⟨4011615495850431050213773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348820661133908066951697 4011615495850431050213773)
            ·
              refine ⟨1504355810943911643830165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4011615495850431050213773 1504355810943911643830165)
              ·
                refine ⟨70516678637995858304539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1504355810943911643830165 70516678637995858304539)
                ·
                  rfl

theorem cell22_1853965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 6].length) (baseStart_1853965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853965 prefixEnd_1853965 := by exact prefixLift 1853965
  have htrace : WordTrace (prefixWord ++ tailWord_1853965) baseStart_1853965 baseEnd_1853965 := by
    simpa [prefixWord, tailWord_1853965, baseEnd_1853965] using wordTrace_append hprefix tailTrace_1853965
  have hstable : (prefixWord ++ tailWord_1853965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853965).length < 2 ^ (prefixWord ++ tailWord_1853965).sum := by decide
  have hdescent : baseEnd_1853965 < baseStart_1853965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853980 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_1853980 : Nat := 118140960795 + 1853980 * 2 ^ 59
def prefixEnd_1853980 : Nat := 4983230072969 + 3 ^ 40 * 1853980 * 2
def baseEnd_1853980 : Nat := 634655242548507685615805

theorem tailTrace_1853980 : CollatzResearch.WordTrace tailWord_1853980 prefixEnd_1853980 634655242548507685615805 := by
  unfold tailWord_1853980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810102911677284710271697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45080137215569712947028929 33810102911677284710271697)
  ·
    refine ⟨25357577183757963532703773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33810102911677284710271697 25357577183757963532703773)
    ·
      refine ⟨9509091443909236324763915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25357577183757963532703773 9509091443909236324763915)
      ·
        refine ⟨14263637165863854487145873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509091443909236324763915 14263637165863854487145873)
        ·
          refine ⟨10697727874397890865359405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14263637165863854487145873 10697727874397890865359405)
          ·
            refine ⟨4011647952899209074509777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10697727874397890865359405 4011647952899209074509777)
            ·
              refine ⟨3008735964674406805882333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011647952899209074509777 3008735964674406805882333)
              ·
                refine ⟨1128275986752902552205875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3008735964674406805882333 1128275986752902552205875)
                ·
                  refine ⟨1692413980129353828308813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128275986752902552205875 1692413980129353828308813)
                  ·
                    refine ⟨634655242548507685615805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692413980129353828308813 634655242548507685615805)
                    ·
                      rfl

theorem cell22_1853980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_1853980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1853980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1853980 prefixEnd_1853980 := by exact prefixLift 1853980
  have htrace : WordTrace (prefixWord ++ tailWord_1853980) baseStart_1853980 baseEnd_1853980 := by
    simpa [prefixWord, tailWord_1853980, baseEnd_1853980] using wordTrace_append hprefix tailTrace_1853980
  have hstable : (prefixWord ++ tailWord_1853980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853980).length < 2 ^ (prefixWord ++ tailWord_1853980).sum := by decide
  have hdescent : baseEnd_1853980 < baseStart_1853980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854023 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1854023 : Nat := 118140960795 + 1854023 * 2 ^ 59
def prefixEnd_1854023 : Nat := 4983230072969 + 3 ^ 40 * 1854023 * 2
def baseEnd_1854023 : Nat := 634669962327269906790673

theorem tailTrace_1854023 : CollatzResearch.WordTrace tailWord_1854023 prefixEnd_1854023 634669962327269906790673 := by
  unfold tailWord_1854023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67621774162198787764358723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45081182774799191842905815 67621774162198787764358723)
  ·
    refine ⟨101432661243298181646538085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67621774162198787764358723 101432661243298181646538085)
    ·
      refine ⟨19018623983118409058725891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101432661243298181646538085 19018623983118409058725891)
      ·
        refine ⟨28527935974677613588088837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19018623983118409058725891 28527935974677613588088837)
        ·
          refine ⟨5348987995252052547766657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28527935974677613588088837 5348987995252052547766657)
          ·
            refine ⟨4011740996439039410824993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348987995252052547766657 4011740996439039410824993)
            ·
              refine ⟨3008805747329279558118745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011740996439039410824993 3008805747329279558118745)
              ·
                refine ⟨2256604310496959668589059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008805747329279558118745 2256604310496959668589059)
                ·
                  refine ⟨3384906465745439502883589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256604310496959668589059 3384906465745439502883589)
                  ·
                    refine ⟨634669962327269906790673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384906465745439502883589 634669962327269906790673)
                    ·
                      rfl

theorem cell22_1854023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1854023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854023 prefixEnd_1854023 := by exact prefixLift 1854023
  have htrace : WordTrace (prefixWord ++ tailWord_1854023) baseStart_1854023 baseEnd_1854023 := by
    simpa [prefixWord, tailWord_1854023, baseEnd_1854023] using wordTrace_append hprefix tailTrace_1854023
  have hstable : (prefixWord ++ tailWord_1854023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854023).length < 2 ^ (prefixWord ++ tailWord_1854023).sum := by decide
  have hdescent : baseEnd_1854023 < baseStart_1854023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854049 : List Nat := [1, 2, 3, 1, 1, 4, 10]
def baseStart_1854049 : Nat := 118140960795 + 1854049 * 2 ^ 59
def prefixEnd_1854049 : Nat := 4983230072969 + 3 ^ 40 * 1854049 * 2
def baseEnd_1854049 : Nat := 23506624542911648357059

theorem tailTrace_1854049 : CollatzResearch.WordTrace tailWord_1854049 prefixEnd_1854049 23506624542911648357059 := by
  unfold tailWord_1854049
  simp only [CollatzResearch.WordTrace]
  refine ⟨67622722460104594204805201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45081814973403062803203467 67622722460104594204805201)
  ·
    refine ⟨50717041845078445653603901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67622722460104594204805201 50717041845078445653603901)
    ·
      refine ⟨19018890691904417120101463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50717041845078445653603901 19018890691904417120101463)
      ·
        refine ⟨28528336037856625680152195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19018890691904417120101463 28528336037856625680152195)
        ·
          refine ⟨42792504056784938520228293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28528336037856625680152195 42792504056784938520228293)
          ·
            refine ⟨8023594510647175972542805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42792504056784938520228293 8023594510647175972542805)
            ·
              refine ⟨23506624542911648357059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8023594510647175972542805 23506624542911648357059)
              ·
                rfl

theorem cell22_1854049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 10].length) (baseStart_1854049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854049 prefixEnd_1854049 := by exact prefixLift 1854049
  have htrace : WordTrace (prefixWord ++ tailWord_1854049) baseStart_1854049 baseEnd_1854049 := by
    simpa [prefixWord, tailWord_1854049, baseEnd_1854049] using wordTrace_append hprefix tailTrace_1854049
  have hstable : (prefixWord ++ tailWord_1854049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854049).length < 2 ^ (prefixWord ++ tailWord_1854049).sum := by decide
  have hdescent : baseEnd_1854049 < baseStart_1854049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854051 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 2, 4]
def baseStart_1854051 : Nat := 118140960795 + 1854051 * 2 ^ 59
def prefixEnd_1854051 : Nat := 4983230072969 + 3 ^ 40 * 1854051 * 2
def baseEnd_1854051 : Nat := 634679547299487167090587

theorem tailTrace_1854051 : CollatzResearch.WordTrace tailWord_1854051 prefixEnd_1854051 634679547299487167090587 := by
  unfold tailWord_1854051
  simp only [CollatzResearch.WordTrace]
  refine ⟨67622795406097348546378007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45081863604064899030918671 67622795406097348546378007)
  ·
    refine ⟨101434193109146022819567011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67622795406097348546378007 101434193109146022819567011)
    ·
      refine ⟨152151289663719034229350517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101434193109146022819567011 152151289663719034229350517)
      ·
        refine ⟨14264183405973659459001611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152151289663719034229350517 14264183405973659459001611)
        ·
          refine ⟨21396275108960489188502417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14264183405973659459001611 21396275108960489188502417)
          ·
            refine ⟨16047206331720366891376813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21396275108960489188502417 16047206331720366891376813)
            ·
              refine ⟨6017702374395137584266305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16047206331720366891376813 6017702374395137584266305)
              ·
                refine ⟨4513276780796353188199729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6017702374395137584266305 4513276780796353188199729)
                ·
                  refine ⟨3384957585597264891149797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513276780796353188199729 3384957585597264891149797)
                  ·
                    refine ⟨634679547299487167090587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384957585597264891149797 634679547299487167090587)
                    ·
                      rfl

theorem cell22_1854051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_1854051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854051 prefixEnd_1854051 := by exact prefixLift 1854051
  have htrace : WordTrace (prefixWord ++ tailWord_1854051) baseStart_1854051 baseEnd_1854051 := by
    simpa [prefixWord, tailWord_1854051, baseEnd_1854051] using wordTrace_append hprefix tailTrace_1854051
  have hstable : (prefixWord ++ tailWord_1854051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854051).length < 2 ^ (prefixWord ++ tailWord_1854051).sum := by decide
  have hdescent : baseEnd_1854051 < baseStart_1854051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854079 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_1854079 : Nat := 118140960795 + 1854079 * 2 ^ 59
def prefixEnd_1854079 : Nat := 4983230072969 + 3 ^ 40 * 1854079 * 2
def baseEnd_1854079 : Nat := 634689132271704427390501

theorem tailTrace_1854079 : CollatzResearch.WordTrace tailWord_1854079 prefixEnd_1854079 634689132271704427390501 := by
  unfold tailWord_1854079
  simp only [CollatzResearch.WordTrace]
  refine ⟨67623816649995909328397291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45082544433330606218931527 67623816649995909328397291)
  ·
    refine ⟨101435724974993863992595937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67623816649995909328397291 101435724974993863992595937)
    ·
      refine ⟨76076793731245397994446953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101435724974993863992595937 76076793731245397994446953)
      ·
        refine ⟨57057595298434048495835215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76076793731245397994446953 57057595298434048495835215)
        ·
          refine ⟨85586392947651072743752823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57057595298434048495835215 85586392947651072743752823)
          ·
            refine ⟨128379589421476609115629235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85586392947651072743752823 128379589421476609115629235)
            ·
              refine ⟨192569384132214913673443853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128379589421476609115629235 192569384132214913673443853)
              ·
                refine ⟨72213519049580592627541445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192569384132214913673443853 72213519049580592627541445)
                ·
                  refine ⟨13540034821796361117664021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72213519049580592627541445 13540034821796361117664021)
                  ·
                    refine ⟨634689132271704427390501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13540034821796361117664021 634689132271704427390501)
                    ·
                      rfl

theorem cell22_1854079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_1854079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854079 prefixEnd_1854079 := by exact prefixLift 1854079
  have htrace : WordTrace (prefixWord ++ tailWord_1854079) baseStart_1854079 baseEnd_1854079 := by
    simpa [prefixWord, tailWord_1854079, baseEnd_1854079] using wordTrace_append hprefix tailTrace_1854079
  have hstable : (prefixWord ++ tailWord_1854079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854079).length < 2 ^ (prefixWord ++ tailWord_1854079).sum := by decide
  have hdescent : baseEnd_1854079 < baseStart_1854079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854162 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_1854162 : Nat := 118140960795 + 1854162 * 2 ^ 59
def prefixEnd_1854162 : Nat := 4983230072969 + 3 ^ 40 * 1854162 * 2
def baseEnd_1854162 : Nat := 211572514955973292521749

theorem tailTrace_1854162 : CollatzResearch.WordTrace tailWord_1854162 prefixEnd_1854162 211572514955973292521749 := by
  unfold tailWord_1854162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16906710977173803625917185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45084562605796809669112493 16906710977173803625917185)
  ·
    refine ⟨12680033232880352719437889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16906710977173803625917185 12680033232880352719437889)
    ·
      refine ⟨9510024924660264539578417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12680033232880352719437889 9510024924660264539578417)
      ·
        refine ⟨7132518693495198404683813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9510024924660264539578417 7132518693495198404683813)
        ·
          refine ⟨1337347255030349700878215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7132518693495198404683813 1337347255030349700878215)
          ·
            refine ⟨2006020882545524551317323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337347255030349700878215 2006020882545524551317323)
            ·
              refine ⟨3009031323818286826975985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006020882545524551317323 3009031323818286826975985)
              ·
                refine ⟨2256773492863715120231989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009031323818286826975985 2256773492863715120231989)
                ·
                  refine ⟨211572514955973292521749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2256773492863715120231989 211572514955973292521749)
                  ·
                    rfl

theorem cell22_1854162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_1854162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854162 prefixEnd_1854162 := by exact prefixLift 1854162
  have htrace : WordTrace (prefixWord ++ tailWord_1854162) baseStart_1854162 baseEnd_1854162 := by
    simpa [prefixWord, tailWord_1854162, baseEnd_1854162] using wordTrace_append hprefix tailTrace_1854162
  have hstable : (prefixWord ++ tailWord_1854162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854162).length < 2 ^ (prefixWord ++ tailWord_1854162).sum := by decide
  have hdescent : baseEnd_1854162 < baseStart_1854162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854233 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_1854233 : Nat := 118140960795 + 1854233 * 2 ^ 59
def prefixEnd_1854233 : Nat := 4983230072969 + 3 ^ 40 * 1854233 * 2
def baseEnd_1854233 : Nat := 634741849618899359040029

theorem tailTrace_1854233 : CollatzResearch.WordTrace tailWord_1854233 prefixEnd_1854233 634741849618899359040029 := by
  unfold tailWord_1854233
  simp only [CollatzResearch.WordTrace]
  refine ⟨67629433491437993629503353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45086288994291995753002235 67629433491437993629503353)
  ·
    refine ⟨50722075118578495222127515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67629433491437993629503353 50722075118578495222127515)
    ·
      refine ⟨76083112677867742833191273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50722075118578495222127515 76083112677867742833191273)
      ·
        refine ⟨57062334508400807124893455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76083112677867742833191273 57062334508400807124893455)
        ·
          refine ⟨85593501762601210687340183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57062334508400807124893455 85593501762601210687340183)
          ·
            refine ⟨128390252643901816031010275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85593501762601210687340183 128390252643901816031010275)
            ·
              refine ⟨192585378965852724046515413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128390252643901816031010275 192585378965852724046515413)
              ·
                refine ⟨4513719819512173219840205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192585378965852724046515413 4513719819512173219840205)
                ·
                  refine ⟨1692644932317064957440077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4513719819512173219840205 1692644932317064957440077)
                  ·
                    refine ⟨634741849618899359040029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692644932317064957440077 634741849618899359040029)
                    ·
                      rfl

theorem cell22_1854233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_1854233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854233 prefixEnd_1854233 := by exact prefixLift 1854233
  have htrace : WordTrace (prefixWord ++ tailWord_1854233) baseStart_1854233 baseEnd_1854233 := by
    simpa [prefixWord, tailWord_1854233, baseEnd_1854233] using wordTrace_append hprefix tailTrace_1854233
  have hstable : (prefixWord ++ tailWord_1854233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854233).length < 2 ^ (prefixWord ++ tailWord_1854233).sum := by decide
  have hdescent : baseEnd_1854233 < baseStart_1854233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854284 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_1854284 : Nat := 118140960795 + 1854284 * 2 ^ 59
def prefixEnd_1854284 : Nat := 4983230072969 + 3 ^ 40 * 1854284 * 2
def baseEnd_1854284 : Nat := 634759307961152226014873

theorem tailTrace_1854284 : CollatzResearch.WordTrace tailWord_1854284 prefixEnd_1854284 634759307961152226014873 := by
  unfold tailWord_1854284
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815646807126614669804953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45087529076168819559739937 33815646807126614669804953)
  ·
    refine ⟨25361735105344961002353715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33815646807126614669804953 25361735105344961002353715)
    ·
      refine ⟨38042602658017441503530573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25361735105344961002353715 38042602658017441503530573)
      ·
        refine ⟨14265975996756540563823965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38042602658017441503530573 14265975996756540563823965)
        ·
          refine ⟨5349740998783702711433987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14265975996756540563823965 5349740998783702711433987)
          ·
            refine ⟨8024611498175554067150981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5349740998783702711433987 8024611498175554067150981)
            ·
              refine ⟨1504614655907916387590809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8024611498175554067150981 1504614655907916387590809)
              ·
                refine ⟨1128460991930937290693107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504614655907916387590809 1128460991930937290693107)
                ·
                  refine ⟨1692691487896405936039661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128460991930937290693107 1692691487896405936039661)
                  ·
                    refine ⟨634759307961152226014873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692691487896405936039661 634759307961152226014873)
                    ·
                      rfl

theorem cell22_1854284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_1854284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854284 prefixEnd_1854284 := by exact prefixLift 1854284
  have htrace : WordTrace (prefixWord ++ tailWord_1854284) baseStart_1854284 baseEnd_1854284 := by
    simpa [prefixWord, tailWord_1854284, baseEnd_1854284] using wordTrace_append hprefix tailTrace_1854284
  have hstable : (prefixWord ++ tailWord_1854284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854284).length < 2 ^ (prefixWord ++ tailWord_1854284).sum := by decide
  have hdescent : baseEnd_1854284 < baseStart_1854284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854291 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 10]
def baseStart_1854291 : Nat := 118140960795 + 1854291 * 2 ^ 59
def prefixEnd_1854291 : Nat := 4983230072969 + 3 ^ 40 * 1854291 * 2
def baseEnd_1854291 : Nat := 211587234734735513696617

theorem tailTrace_1854291 : CollatzResearch.WordTrace tailWord_1854291 prefixEnd_1854291 211587234734735513696617 := by
  unfold tailWord_1854291
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631548925227869535114727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45087699283485246356743151 67631548925227869535114727)
  ·
    refine ⟨101447323387841804302672091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67631548925227869535114727 101447323387841804302672091)
    ·
      refine ⟨152170985081762706454008137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101447323387841804302672091 152170985081762706454008137)
      ·
        refine ⟨114128238811322029840506103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152170985081762706454008137 114128238811322029840506103)
        ·
          refine ⟨171192358216983044760759155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114128238811322029840506103 171192358216983044760759155)
          ·
            refine ⟨256788537325474567141138733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171192358216983044760759155 256788537325474567141138733)
            ·
              refine ⟨96295701497052962677927025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256788537325474567141138733 96295701497052962677927025)
              ·
                refine ⟨72221776122789722008445269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96295701497052962677927025 72221776122789722008445269)
                ·
                  refine ⟨211587234734735513696617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72221776122789722008445269 211587234734735513696617)
                  ·
                    rfl

theorem cell22_1854291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_1854291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854291 prefixEnd_1854291 := by exact prefixLift 1854291
  have htrace : WordTrace (prefixWord ++ tailWord_1854291) baseStart_1854291 baseEnd_1854291 := by
    simpa [prefixWord, tailWord_1854291, baseEnd_1854291] using wordTrace_append hprefix tailTrace_1854291
  have hstable : (prefixWord ++ tailWord_1854291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854291).length < 2 ^ (prefixWord ++ tailWord_1854291).sum := by decide
  have hdescent : baseEnd_1854291 < baseStart_1854291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854293 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1854293 : Nat := 118140960795 + 1854293 * 2 ^ 59
def prefixEnd_1854293 : Nat := 4983230072969 + 3 ^ 40 * 1854293 * 2
def baseEnd_1854293 : Nat := 634762388845079202539845

theorem tailTrace_1854293 : CollatzResearch.WordTrace tailWord_1854293 prefixEnd_1854293 634762388845079202539845 := by
  unfold tailWord_1854293
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631621871220623876687533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45087747914147082584458355 67631621871220623876687533)
  ·
    refine ⟨25361858201707733953757825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67631621871220623876687533 25361858201707733953757825)
    ·
      refine ⟨19021393651280800465318369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25361858201707733953757825 19021393651280800465318369)
      ·
        refine ⟨14266045238460600348988777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19021393651280800465318369 14266045238460600348988777)
        ·
          refine ⟨10699533928845450261741583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14266045238460600348988777 10699533928845450261741583)
          ·
            refine ⟨16049300893268175392612375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10699533928845450261741583 16049300893268175392612375)
            ·
              refine ⟨24073951339902263088918563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16049300893268175392612375 24073951339902263088918563)
              ·
                refine ⟨36110927009853394633377845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24073951339902263088918563 36110927009853394633377845)
                ·
                  refine ⟨3385399407173755746879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36110927009853394633377845 3385399407173755746879173)
                  ·
                    refine ⟨634762388845079202539845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3385399407173755746879173 634762388845079202539845)
                    ·
                      rfl

theorem cell22_1854293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1854293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854293 prefixEnd_1854293 := by exact prefixLift 1854293
  have htrace : WordTrace (prefixWord ++ tailWord_1854293) baseStart_1854293 baseEnd_1854293 := by
    simpa [prefixWord, tailWord_1854293, baseEnd_1854293] using wordTrace_append hprefix tailTrace_1854293
  have hstable : (prefixWord ++ tailWord_1854293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854293).length < 2 ^ (prefixWord ++ tailWord_1854293).sum := by decide
  have hdescent : baseEnd_1854293 < baseStart_1854293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854308 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1854308 : Nat := 118140960795 + 1854308 * 2 ^ 59
def prefixEnd_1854308 : Nat := 4983230072969 + 3 ^ 40 * 1854308 * 2
def baseEnd_1854308 : Nat := 211589174550541387804933

theorem tailTrace_1854308 : CollatzResearch.WordTrace tailWord_1854308 prefixEnd_1854308 211589174550541387804933 := by
  unfold tailWord_1854308
  simp only [CollatzResearch.WordTrace]
  refine ⟨33816084483083140719241789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45088112644110854292322385 33816084483083140719241789)
  ·
    refine ⟨12681031681156177769715671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33816084483083140719241789 12681031681156177769715671)
    ·
      refine ⟨19021547521734266654573507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681031681156177769715671 19021547521734266654573507)
      ·
        refine ⟨28532321282601399981860261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19021547521734266654573507 28532321282601399981860261)
        ·
          refine ⟨5349810240487762496598799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28532321282601399981860261 5349810240487762496598799)
          ·
            refine ⟨8024715360731643744898199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5349810240487762496598799 8024715360731643744898199)
            ·
              refine ⟨12037073041097465617347299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8024715360731643744898199 12037073041097465617347299)
              ·
                refine ⟨18055609561646198426020949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12037073041097465617347299 18055609561646198426020949)
                ·
                  refine ⟨211589174550541387804933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18055609561646198426020949 211589174550541387804933)
                  ·
                    rfl

theorem cell22_1854308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1854308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854308 prefixEnd_1854308 := by exact prefixLift 1854308
  have htrace : WordTrace (prefixWord ++ tailWord_1854308) baseStart_1854308 baseEnd_1854308 := by
    simpa [prefixWord, tailWord_1854308, baseEnd_1854308] using wordTrace_append hprefix tailTrace_1854308
  have hstable : (prefixWord ++ tailWord_1854308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854308).length < 2 ^ (prefixWord ++ tailWord_1854308).sum := by decide
  have hdescent : baseEnd_1854308 < baseStart_1854308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854323 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 1, 5]
def baseStart_1854323 : Nat := 118140960795 + 1854323 * 2 ^ 59
def prefixEnd_1854323 : Nat := 4983230072969 + 3 ^ 40 * 1854323 * 2
def baseEnd_1854323 : Nat := 634772658458169124289753

theorem tailTrace_1854323 : CollatzResearch.WordTrace tailWord_1854323 prefixEnd_1854323 634772658458169124289753 := by
  unfold tailWord_1854323
  simp only [CollatzResearch.WordTrace]
  refine ⟨67632716061111939000279623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45088477374074626000186415 67632716061111939000279623)
  ·
    refine ⟨101449074091667908500419435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67632716061111939000279623 101449074091667908500419435)
    ·
      refine ⟨152173611137501862750629153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101449074091667908500419435 152173611137501862750629153)
      ·
        refine ⟨114130208353126397062971865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152173611137501862750629153 114130208353126397062971865)
        ·
          refine ⟨85597656264844797797228899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114130208353126397062971865 85597656264844797797228899)
          ·
            refine ⟨128396484397267196695843349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85597656264844797797228899 128396484397267196695843349)
            ·
              refine ⟨6018585206121899845117657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128396484397267196695843349 6018585206121899845117657)
              ·
                refine ⟨4513938904591424883838243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6018585206121899845117657 4513938904591424883838243)
                ·
                  refine ⟨6770908356887137325757365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513938904591424883838243 6770908356887137325757365)
                  ·
                    refine ⟨634772658458169124289753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6770908356887137325757365 634772658458169124289753)
                    ·
                      rfl

theorem cell22_1854323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_1854323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854323 prefixEnd_1854323 := by exact prefixLift 1854323
  have htrace : WordTrace (prefixWord ++ tailWord_1854323) baseStart_1854323 baseEnd_1854323 := by
    simpa [prefixWord, tailWord_1854323, baseEnd_1854323] using wordTrace_append hprefix tailTrace_1854323
  have hstable : (prefixWord ++ tailWord_1854323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854323).length < 2 ^ (prefixWord ++ tailWord_1854323).sum := by decide
  have hdescent : baseEnd_1854323 < baseStart_1854323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854370 : List Nat := [3, 3, 1, 2, 2, 2, 1, 8]
def baseStart_1854370 : Nat := 118140960795 + 1854370 * 2 ^ 59
def prefixEnd_1854370 : Nat := 4983230072969 + 3 ^ 40 * 1854370 * 2
def baseEnd_1854370 : Nat := 70532083057630740929401

theorem tailTrace_1854370 : CollatzResearch.WordTrace tailWord_1854370 prefixEnd_1854370 70532083057630740929401 := by
  unfold tailWord_1854370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908607572985416506810141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45089620194627777351493709 16908607572985416506810141)
  ·
    refine ⟨6340727839869531190053803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16908607572985416506810141 6340727839869531190053803)
    ·
      refine ⟨9511091759804296785080705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6340727839869531190053803 9511091759804296785080705)
      ·
        refine ⟨7133318819853222588810529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9511091759804296785080705 7133318819853222588810529)
        ·
          refine ⟨5349989114889916941607897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7133318819853222588810529 5349989114889916941607897)
          ·
            refine ⟨4012491836167437706205923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5349989114889916941607897 4012491836167437706205923)
            ·
              refine ⟨6018737754251156559308885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012491836167437706205923 6018737754251156559308885)
              ·
                refine ⟨70532083057630740929401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6018737754251156559308885 70532083057630740929401)
                ·
                  rfl

theorem cell22_1854370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_1854370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854370 prefixEnd_1854370 := by exact prefixLift 1854370
  have htrace : WordTrace (prefixWord ++ tailWord_1854370) baseStart_1854370 baseEnd_1854370 := by
    simpa [prefixWord, tailWord_1854370, baseEnd_1854370] using wordTrace_append hprefix tailTrace_1854370
  have hstable : (prefixWord ++ tailWord_1854370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854370).length < 2 ^ (prefixWord ++ tailWord_1854370).sum := by decide
  have hdescent : baseEnd_1854370 < baseStart_1854370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854415 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 5]
def baseStart_1854415 : Nat := 118140960795 + 1854415 * 2 ^ 59
def prefixEnd_1854415 : Nat := 4983230072969 + 3 ^ 40 * 1854415 * 2
def baseEnd_1854415 : Nat := 211601383979437183663157

theorem tailTrace_1854415 : CollatzResearch.WordTrace tailWord_1854415 prefixEnd_1854415 211601383979437183663157 := by
  unfold tailWord_1854415
  simp only [CollatzResearch.WordTrace]
  refine ⟨67636071576778638712628699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45090714384519092475085799 67636071576778638712628699)
  ·
    refine ⟨101454107365167958068943049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67636071576778638712628699 101454107365167958068943049)
    ·
      refine ⟨76090580523875968551707287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101454107365167958068943049 76090580523875968551707287)
      ·
        refine ⟨114135870785813952827560931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76090580523875968551707287 114135870785813952827560931)
        ·
          refine ⟨171203806178720929241341397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114135870785813952827560931 171203806178720929241341397)
          ·
            refine ⟨4012589207313771779093939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 171203806178720929241341397 4012589207313771779093939)
            ·
              refine ⟨6018883810970657668640909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012589207313771779093939 6018883810970657668640909)
              ·
                refine ⟨2257081429113996625740341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6018883810970657668640909 2257081429113996625740341)
                ·
                  refine ⟨211601383979437183663157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2257081429113996625740341 211601383979437183663157)
                  ·
                    rfl

theorem cell22_1854415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 5].length) (baseStart_1854415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854415 prefixEnd_1854415 := by exact prefixLift 1854415
  have htrace : WordTrace (prefixWord ++ tailWord_1854415) baseStart_1854415 baseEnd_1854415 := by
    simpa [prefixWord, tailWord_1854415, baseEnd_1854415] using wordTrace_append hprefix tailTrace_1854415
  have hstable : (prefixWord ++ tailWord_1854415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854415).length < 2 ^ (prefixWord ++ tailWord_1854415).sum := by decide
  have hdescent : baseEnd_1854415 < baseStart_1854415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854453 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1854453 : Nat := 118140960795 + 1854453 * 2 ^ 59
def prefixEnd_1854453 : Nat := 4983230072969 + 3 ^ 40 * 1854453 * 2
def baseEnd_1854453 : Nat := 634817160114892118539355

theorem tailTrace_1854453 : CollatzResearch.WordTrace tailWord_1854453 prefixEnd_1854453 634817160114892118539355 := by
  unfold tailWord_1854453
  simp only [CollatzResearch.WordTrace]
  refine ⟨67637457550640971202512013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45091638367093980801674675 67637457550640971202512013)
  ·
    refine ⟨25364046581490364200942005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67637457550640971202512013 25364046581490364200942005)
    ·
      refine ⟨2377879367014721643838313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25364046581490364200942005 2377879367014721643838313)
      ·
        refine ⟨1783409525261041232878735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2377879367014721643838313 1783409525261041232878735)
        ·
          refine ⟨2675114287891561849318103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783409525261041232878735 2675114287891561849318103)
          ·
            refine ⟨4012671431837342773977155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675114287891561849318103 4012671431837342773977155)
            ·
              refine ⟨6019007147756014160965733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012671431837342773977155 6019007147756014160965733)
              ·
                refine ⟨1128563840204252655181075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6019007147756014160965733 1128563840204252655181075)
                ·
                  refine ⟨1692845760306378982771613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128563840204252655181075 1692845760306378982771613)
                  ·
                    refine ⟨634817160114892118539355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692845760306378982771613 634817160114892118539355)
                    ·
                      rfl

theorem cell22_1854453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1854453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854453 prefixEnd_1854453 := by exact prefixLift 1854453
  have htrace : WordTrace (prefixWord ++ tailWord_1854453) baseStart_1854453 baseEnd_1854453 := by
    simpa [prefixWord, tailWord_1854453, baseEnd_1854453] using wordTrace_append hprefix tailTrace_1854453
  have hstable : (prefixWord ++ tailWord_1854453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854453).length < 2 ^ (prefixWord ++ tailWord_1854453).sum := by decide
  have hdescent : baseEnd_1854453 < baseStart_1854453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854475 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 1, 5]
def baseStart_1854475 : Nat := 118140960795 + 1854475 * 2 ^ 59
def prefixEnd_1854475 : Nat := 4983230072969 + 3 ^ 40 * 1854475 * 2
def baseEnd_1854475 : Nat := 634824691164491394489287

theorem tailTrace_1854475 : CollatzResearch.WordTrace tailWord_1854475 prefixEnd_1854475 634824691164491394489287 := by
  unfold tailWord_1854475
  simp only [CollatzResearch.WordTrace]
  refine ⟨67638259956561268959812879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45092173304374179306541919 67638259956561268959812879)
  ·
    refine ⟨101457389934841903439719319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67638259956561268959812879 101457389934841903439719319)
    ·
      refine ⟨152186084902262855159578979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101457389934841903439719319 152186084902262855159578979)
      ·
        refine ⟨228279127353394282739368469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152186084902262855159578979 228279127353394282739368469)
        ·
          refine ⟨10700584094690357003407897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228279127353394282739368469 10700584094690357003407897)
          ·
            refine ⟨8025438071017767752555923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10700584094690357003407897 8025438071017767752555923)
            ·
              refine ⟨12038157106526651628833885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8025438071017767752555923 12038157106526651628833885)
              ·
                refine ⟨4514308914947494360812707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12038157106526651628833885 4514308914947494360812707)
                ·
                  refine ⟨6771463372421241541219061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514308914947494360812707 6771463372421241541219061)
                  ·
                    refine ⟨634824691164491394489287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6771463372421241541219061 634824691164491394489287)
                    ·
                      rfl

theorem cell22_1854475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_1854475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854475 prefixEnd_1854475 := by exact prefixLift 1854475
  have htrace : WordTrace (prefixWord ++ tailWord_1854475) baseStart_1854475 baseEnd_1854475 := by
    simpa [prefixWord, tailWord_1854475, baseEnd_1854475] using wordTrace_append hprefix tailTrace_1854475
  have hstable : (prefixWord ++ tailWord_1854475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854475).length < 2 ^ (prefixWord ++ tailWord_1854475).sum := by decide
  have hdescent : baseEnd_1854475 < baseStart_1854475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854490 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1854490 : Nat := 118140960795 + 1854490 * 2 ^ 59
def prefixEnd_1854490 : Nat := 4983230072969 + 3 ^ 40 * 1854490 * 2
def baseEnd_1854490 : Nat := 634829825971036355364241

theorem tailTrace_1854490 : CollatzResearch.WordTrace tailWord_1854490 prefixEnd_1854490 634829825971036355364241 := by
  unfold tailWord_1854490
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909701762876731630402231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45092538034337951014405949 16909701762876731630402231)
  ·
    refine ⟨25364552644315097445603347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16909701762876731630402231 25364552644315097445603347)
    ·
      refine ⟨38046828966472646168405021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25364552644315097445603347 38046828966472646168405021)
      ·
        refine ⟨14267560862427242313151883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38046828966472646168405021 14267560862427242313151883)
        ·
          refine ⟨21401341293640863469727825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14267560862427242313151883 21401341293640863469727825)
          ·
            refine ⟨16051005970230647602295869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21401341293640863469727825 16051005970230647602295869)
            ·
              refine ⟨6019127238836492850860951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16051005970230647602295869 6019127238836492850860951)
              ·
                refine ⟨9028690858254739276291427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019127238836492850860951 9028690858254739276291427)
                ·
                  refine ⟨13543036287382108914437141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9028690858254739276291427 13543036287382108914437141)
                  ·
                    refine ⟨634829825971036355364241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13543036287382108914437141 634829825971036355364241)
                    ·
                      rfl

theorem cell22_1854490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1854490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854490 prefixEnd_1854490 := by exact prefixLift 1854490
  have htrace : WordTrace (prefixWord ++ tailWord_1854490) baseStart_1854490 baseEnd_1854490 := by
    simpa [prefixWord, tailWord_1854490, baseEnd_1854490] using wordTrace_append hprefix tailTrace_1854490
  have hstable : (prefixWord ++ tailWord_1854490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854490).length < 2 ^ (prefixWord ++ tailWord_1854490).sum := by decide
  have hdescent : baseEnd_1854490 < baseStart_1854490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854554 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_1854554 : Nat := 118140960795 + 1854554 * 2 ^ 59
def prefixEnd_1854554 : Nat := 4983230072969 + 3 ^ 40 * 1854554 * 2
def baseEnd_1854554 : Nat := 634851734478961521764045

theorem tailTrace_1854554 : CollatzResearch.WordTrace tailWord_1854554 prefixEnd_1854554 634851734478961521764045 := by
  unfold tailWord_1854554
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910285330818766362984679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45094094215516710301292477 16910285330818766362984679)
  ·
    refine ⟨25365427996228149544477019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16910285330818766362984679 25365427996228149544477019)
    ·
      refine ⟨38048141994342224316715529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25365427996228149544477019 38048141994342224316715529)
      ·
        refine ⟨28536106495756668237536647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38048141994342224316715529 28536106495756668237536647)
        ·
          refine ⟨42804159743635002356304971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28536106495756668237536647 42804159743635002356304971)
          ·
            refine ⟨64206239615452503534457457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42804159743635002356304971 64206239615452503534457457)
            ·
              refine ⟨48154679711589377650843093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64206239615452503534457457 48154679711589377650843093)
              ·
                refine ⟨1128625305740376038691635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48154679711589377650843093 1128625305740376038691635)
                ·
                  refine ⟨1692937958610564058037453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128625305740376038691635 1692937958610564058037453)
                  ·
                    refine ⟨634851734478961521764045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692937958610564058037453 634851734478961521764045)
                    ·
                      rfl

theorem cell22_1854554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_1854554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854554 prefixEnd_1854554 := by exact prefixLift 1854554
  have htrace : WordTrace (prefixWord ++ tailWord_1854554) baseStart_1854554 baseEnd_1854554 := by
    simpa [prefixWord, tailWord_1854554, baseEnd_1854554] using wordTrace_append hprefix tailTrace_1854554
  have hstable : (prefixWord ++ tailWord_1854554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854554).length < 2 ^ (prefixWord ++ tailWord_1854554).sum := by decide
  have hdescent : baseEnd_1854554 < baseStart_1854554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854582 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1854582 : Nat := 118140960795 + 1854582 * 2 ^ 59
def prefixEnd_1854582 : Nat := 4983230072969 + 3 ^ 40 * 1854582 * 2
def baseEnd_1854582 : Nat := 634861319451178782063959

theorem tailTrace_1854582 : CollatzResearch.WordTrace tailWord_1854582 prefixEnd_1854582 634861319451178782063959 := by
  unfold tailWord_1854582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4227635160448351639622375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45094775044782417489305333 4227635160448351639622375)
  ·
    refine ⟨6341452740672527459433563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4227635160448351639622375 6341452740672527459433563)
    ·
      refine ⟨9512179111008791189150345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6341452740672527459433563 9512179111008791189150345)
      ·
        refine ⟨7134134333256593391862759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9512179111008791189150345 7134134333256593391862759)
        ·
          refine ⟨10701201499884890087794139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134134333256593391862759 10701201499884890087794139)
          ·
            refine ⟨16051802249827335131691209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701201499884890087794139 16051802249827335131691209)
            ·
              refine ⟨12038851687370501348768407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16051802249827335131691209 12038851687370501348768407)
              ·
                refine ⟨18058277531055752023152611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12038851687370501348768407 18058277531055752023152611)
                ·
                  refine ⟨27087416296583628034728917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18058277531055752023152611 27087416296583628034728917)
                  ·
                    refine ⟨634861319451178782063959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27087416296583628034728917 634861319451178782063959)
                    ·
                      rfl

theorem cell22_1854582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1854582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854582 prefixEnd_1854582 := by exact prefixLift 1854582
  have htrace : WordTrace (prefixWord ++ tailWord_1854582) baseStart_1854582 baseEnd_1854582 := by
    simpa [prefixWord, tailWord_1854582, baseEnd_1854582] using wordTrace_append hprefix tailTrace_1854582
  have hstable : (prefixWord ++ tailWord_1854582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854582).length < 2 ^ (prefixWord ++ tailWord_1854582).sum := by decide
  have hdescent : baseEnd_1854582 < baseStart_1854582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854595 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 8]
def baseStart_1854595 : Nat := 118140960795 + 1854595 * 2 ^ 59
def prefixEnd_1854595 : Nat := 4983230072969 + 3 ^ 40 * 1854595 * 2
def baseEnd_1854595 : Nat := 211621923205617027162973

theorem tailTrace_1854595 : CollatzResearch.WordTrace tailWord_1854595 prefixEnd_1854595 211621923205617027162973 := by
  unfold tailWord_1854595
  simp only [CollatzResearch.WordTrace]
  refine ⟨67642636716126529454181239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45095091144084352969454159 67642636716126529454181239)
  ·
    refine ⟨101463955074189794181271859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67642636716126529454181239 101463955074189794181271859)
    ·
      refine ⟨152195932611284691271907789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101463955074189794181271859 152195932611284691271907789)
      ·
        refine ⟨57073474729231759226965421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152195932611284691271907789 57073474729231759226965421)
        ·
          refine ⟨21402553023461909710112033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57073474729231759226965421 21402553023461909710112033)
          ·
            refine ⟨16051914767596432282584025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21402553023461909710112033 16051914767596432282584025)
            ·
              refine ⟨12038936075697324211938019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16051914767596432282584025 12038936075697324211938019)
              ·
                refine ⟨18058404113545986317907029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12038936075697324211938019 18058404113545986317907029)
                ·
                  refine ⟨211621923205617027162973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18058404113545986317907029 211621923205617027162973)
                  ·
                    rfl

theorem cell22_1854595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_1854595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854595 prefixEnd_1854595 := by exact prefixLift 1854595
  have htrace : WordTrace (prefixWord ++ tailWord_1854595) baseStart_1854595 baseEnd_1854595 := by
    simpa [prefixWord, tailWord_1854595, baseEnd_1854595] using wordTrace_append hprefix tailTrace_1854595
  have hstable : (prefixWord ++ tailWord_1854595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854595).length < 2 ^ (prefixWord ++ tailWord_1854595).sum := by decide
  have hdescent : baseEnd_1854595 < baseStart_1854595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854627 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 4, 3]
def baseStart_1854627 : Nat := 118140960795 + 1854627 * 2 ^ 59
def prefixEnd_1854627 : Nat := 4983230072969 + 3 ^ 40 * 1854627 * 2
def baseEnd_1854627 : Nat := 634876723870813664688821

theorem tailTrace_1854627 : CollatzResearch.WordTrace tailWord_1854627 prefixEnd_1854627 634876723870813664688821 := by
  unfold tailWord_1854627
  simp only [CollatzResearch.WordTrace]
  refine ⟨67643803852010598919346135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45095869234673732612897423 67643803852010598919346135)
  ·
    refine ⟨101465705778015898379019203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67643803852010598919346135 101465705778015898379019203)
    ·
      refine ⟨152198558667023847568528805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101465705778015898379019203 152198558667023847568528805)
      ·
        refine ⟨28537229750066971419099151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152198558667023847568528805 28537229750066971419099151)
        ·
          refine ⟨42805844625100457128648727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28537229750066971419099151 42805844625100457128648727)
          ·
            refine ⟨64208766937650685692973091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42805844625100457128648727 64208766937650685692973091)
            ·
              refine ⟨96313150406476028539459637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64208766937650685692973091 96313150406476028539459637)
              ·
                refine ⟨9029357850607127675574341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96313150406476028539459637 9029357850607127675574341)
                ·
                  refine ⟨1693004596988836439170189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9029357850607127675574341 1693004596988836439170189)
                  ·
                    refine ⟨634876723870813664688821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693004596988836439170189 634876723870813664688821)
                    ·
                      rfl

theorem cell22_1854627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 3].length) (baseStart_1854627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854627 prefixEnd_1854627 := by exact prefixLift 1854627
  have htrace : WordTrace (prefixWord ++ tailWord_1854627) baseStart_1854627 baseEnd_1854627 := by
    simpa [prefixWord, tailWord_1854627, baseEnd_1854627] using wordTrace_append hprefix tailTrace_1854627
  have hstable : (prefixWord ++ tailWord_1854627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854627).length < 2 ^ (prefixWord ++ tailWord_1854627).sum := by decide
  have hdescent : baseEnd_1854627 < baseStart_1854627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854629 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 4]
def baseStart_1854629 : Nat := 118140960795 + 1854629 * 2 ^ 59
def prefixEnd_1854629 : Nat := 4983230072969 + 3 ^ 40 * 1854629 * 2
def baseEnd_1854629 : Nat := 211625802837228775379605

theorem tailTrace_1854629 : CollatzResearch.WordTrace tailWord_1854629 prefixEnd_1854629 211625802837228775379605 := by
  unfold tailWord_1854629
  simp only [CollatzResearch.WordTrace]
  refine ⟨67643876798003353260918941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45095917865335568840612627 67643876798003353260918941)
  ·
    refine ⟨25366453799251257472844603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67643876798003353260918941 25366453799251257472844603)
    ·
      refine ⟨38049680698876886209266905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25366453799251257472844603 38049680698876886209266905)
      ·
        refine ⟨28537260524157664656950179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38049680698876886209266905 28537260524157664656950179)
        ·
          refine ⟨42805890786236496985425269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28537260524157664656950179 42805890786236496985425269)
          ·
            refine ⟨4013052261209671592383619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42805890786236496985425269 4013052261209671592383619)
            ·
              refine ⟨6019578391814507388575429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013052261209671592383619 6019578391814507388575429)
              ·
                refine ⟨1128670948465220135357893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6019578391814507388575429 1128670948465220135357893)
                ·
                  refine ⟨211625802837228775379605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128670948465220135357893 211625802837228775379605)
                  ·
                    rfl

theorem cell22_1854629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_1854629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854629 prefixEnd_1854629 := by exact prefixLift 1854629
  have htrace : WordTrace (prefixWord ++ tailWord_1854629) baseStart_1854629 baseEnd_1854629 := by
    simpa [prefixWord, tailWord_1854629, baseEnd_1854629] using wordTrace_append hprefix tailTrace_1854629
  have hstable : (prefixWord ++ tailWord_1854629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854629).length < 2 ^ (prefixWord ++ tailWord_1854629).sum := by decide
  have hdescent : baseEnd_1854629 < baseStart_1854629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854678 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1854678 : Nat := 118140960795 + 1854678 * 2 ^ 59
def prefixEnd_1854678 : Nat := 4983230072969 + 3 ^ 40 * 1854678 * 2
def baseEnd_1854678 : Nat := 634894182213066531663665

theorem tailTrace_1854678 : CollatzResearch.WordTrace tailWord_1854678 prefixEnd_1854678 634894182213066531663665 := by
  unfold tailWord_1854678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4227853998426614664340793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45097109316550556419635125 4227853998426614664340793)
  ·
    refine ⟨3170890498819960998255595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4227853998426614664340793 3170890498819960998255595)
    ·
      refine ⟨4756335748229941497383393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170890498819960998255595 4756335748229941497383393)
      ·
        refine ⟨3567251811172456123037545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4756335748229941497383393 3567251811172456123037545)
        ·
          refine ⟨2675438858379342092278159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567251811172456123037545 2675438858379342092278159)
          ·
            refine ⟨4013158287569013138417239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675438858379342092278159 4013158287569013138417239)
            ·
              refine ⟨6019737431353519707625859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013158287569013138417239 6019737431353519707625859)
              ·
                refine ⟨9029606147030279561438789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019737431353519707625859 9029606147030279561438789)
                ·
                  refine ⟨1693051152568177417769773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9029606147030279561438789 1693051152568177417769773)
                  ·
                    refine ⟨634894182213066531663665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693051152568177417769773 634894182213066531663665)
                    ·
                      rfl

theorem cell22_1854678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1854678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854678 prefixEnd_1854678 := by exact prefixLift 1854678
  have htrace : WordTrace (prefixWord ++ tailWord_1854678) baseStart_1854678 baseEnd_1854678 := by
    simpa [prefixWord, tailWord_1854678, baseEnd_1854678] using wordTrace_append hprefix tailTrace_1854678
  have hstable : (prefixWord ++ tailWord_1854678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854678).length < 2 ^ (prefixWord ++ tailWord_1854678).sum := by decide
  have hdescent : baseEnd_1854678 < baseStart_1854678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854689 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1854689 : Nat := 118140960795 + 1854689 * 2 ^ 59
def prefixEnd_1854689 : Nat := 4983230072969 + 3 ^ 40 * 1854689 * 2
def baseEnd_1854689 : Nat := 634897947737866169638631

theorem tailTrace_1854689 : CollatzResearch.WordTrace tailWord_1854689 prefixEnd_1854689 634897947737866169638631 := by
  unfold tailWord_1854689
  simp only [CollatzResearch.WordTrace]
  refine ⟨67646065177785983508103121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45097376785190655672068747 67646065177785983508103121)
  ·
    refine ⟨50734548883339487631077341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67646065177785983508103121 50734548883339487631077341)
    ·
      refine ⟨19025455831252307861654003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50734548883339487631077341 19025455831252307861654003)
      ·
        refine ⟨28538183746878461792481005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19025455831252307861654003 28538183746878461792481005)
        ·
          refine ⟨10701818905079423172180377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28538183746878461792481005 10701818905079423172180377)
          ·
            refine ⟨8026364178809567379135283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10701818905079423172180377 8026364178809567379135283)
            ·
              refine ⟨12039546268214351068702925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026364178809567379135283 12039546268214351068702925)
              ·
                refine ⟨4514829850580381650763597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12039546268214351068702925 4514829850580381650763597)
                ·
                  refine ⟨1693061193967643119036349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4514829850580381650763597 1693061193967643119036349)
                  ·
                    refine ⟨634897947737866169638631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693061193967643119036349 634897947737866169638631)
                    ·
                      rfl

theorem cell22_1854689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1854689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854689 prefixEnd_1854689 := by exact prefixLift 1854689
  have htrace : WordTrace (prefixWord ++ tailWord_1854689) baseStart_1854689 baseEnd_1854689 := by
    simpa [prefixWord, tailWord_1854689, baseEnd_1854689] using wordTrace_append hprefix tailTrace_1854689
  have hstable : (prefixWord ++ tailWord_1854689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854689).length < 2 ^ (prefixWord ++ tailWord_1854689).sum := by decide
  have hdescent : baseEnd_1854689 < baseStart_1854689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854708 : List Nat := [2, 6, 1, 2, 1, 1, 1, 8]
def baseStart_1854708 : Nat := 118140960795 + 1854708 * 2 ^ 59
def prefixEnd_1854708 : Nat := 4983230072969 + 3 ^ 40 * 1854708 * 2
def baseEnd_1854708 : Nat := 70544939091795161490397

theorem tailTrace_1854708 : CollatzResearch.WordTrace tailWord_1854708 prefixEnd_1854708 70544939091795161490397 := by
  unfold tailWord_1854708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33823379082358574876522389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45097838776478099835363185 33823379082358574876522389)
  ·
    refine ⟨1585470894485558197336987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33823379082358574876522389 1585470894485558197336987)
    ·
      refine ⟨2378206341728337296005481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585470894485558197336987 2378206341728337296005481)
      ·
        refine ⟨1783654756296252972004111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2378206341728337296005481 1783654756296252972004111)
        ·
          refine ⟨2675482134444379458006167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783654756296252972004111 2675482134444379458006167)
          ·
            refine ⟨4013223201666569187009251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675482134444379458006167 4013223201666569187009251)
            ·
              refine ⟨6019834802499853780513877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013223201666569187009251 6019834802499853780513877)
              ·
                refine ⟨70544939091795161490397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6019834802499853780513877 70544939091795161490397)
                ·
                  rfl

theorem cell22_1854708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 8].length) (baseStart_1854708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854708 prefixEnd_1854708 := by exact prefixLift 1854708
  have htrace : WordTrace (prefixWord ++ tailWord_1854708) baseStart_1854708 baseEnd_1854708 := by
    simpa [prefixWord, tailWord_1854708, baseEnd_1854708] using wordTrace_append hprefix tailTrace_1854708
  have hstable : (prefixWord ++ tailWord_1854708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854708).length < 2 ^ (prefixWord ++ tailWord_1854708).sum := by decide
  have hdescent : baseEnd_1854708 < baseStart_1854708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854723 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 1, 3]
def baseStart_1854723 : Nat := 118140960795 + 1854723 * 2 ^ 59
def prefixEnd_1854723 : Nat := 4983230072969 + 3 ^ 40 * 1854723 * 2
def baseEnd_1854723 : Nat := 634909586632701414288527

theorem tailTrace_1854723 : CollatzResearch.WordTrace tailWord_1854723 prefixEnd_1854723 634909586632701414288527 := by
  unfold tailWord_1854723
  simp only [CollatzResearch.WordTrace]
  refine ⟨67647305259662807314840823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45098203506441871543227215 67647305259662807314840823)
  ·
    refine ⟨101470957889494210972261235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67647305259662807314840823 101470957889494210972261235)
    ·
      refine ⟨152206436834241316458391853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101470957889494210972261235 152206436834241316458391853)
      ·
        refine ⟨57077413812840493671896945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152206436834241316458391853 57077413812840493671896945)
        ·
          refine ⟨42808060359630370253922709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57077413812840493671896945 42808060359630370253922709)
          ·
            refine ⟨2006627829357673605652627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42808060359630370253922709 2006627829357673605652627)
            ·
              refine ⟨3009941744036510408478941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006627829357673605652627 3009941744036510408478941)
              ·
                refine ⟨1128728154013691403179603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009941744036510408478941 1128728154013691403179603)
                ·
                  refine ⟨1693092231020537104769405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128728154013691403179603 1693092231020537104769405)
                  ·
                    refine ⟨634909586632701414288527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693092231020537104769405 634909586632701414288527)
                    ·
                      rfl

theorem cell22_1854723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 3].length) (baseStart_1854723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854723 prefixEnd_1854723 := by exact prefixLift 1854723
  have htrace : WordTrace (prefixWord ++ tailWord_1854723) baseStart_1854723 baseEnd_1854723 := by
    simpa [prefixWord, tailWord_1854723, baseEnd_1854723] using wordTrace_append hprefix tailTrace_1854723
  have hstable : (prefixWord ++ tailWord_1854723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854723).length < 2 ^ (prefixWord ++ tailWord_1854723).sum := by decide
  have hdescent : baseEnd_1854723 < baseStart_1854723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854796 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_1854796 : Nat := 118140960795 + 1854796 * 2 ^ 59
def prefixEnd_1854796 : Nat := 4983230072969 + 3 ^ 40 * 1854796 * 2
def baseEnd_1854796 : Nat := 634934576024553557213303

theorem tailTrace_1854796 : CollatzResearch.WordTrace tailWord_1854796 prefixEnd_1854796 634934576024553557213303 := by
  unfold tailWord_1854796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33824983894199170391124121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45099978525598893854832161 33824983894199170391124121)
  ·
    refine ⟨25368737920649377793343091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33824983894199170391124121 25368737920649377793343091)
    ·
      refine ⟨38053106880974066690014637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25368737920649377793343091 38053106880974066690014637)
      ·
        refine ⟨14269915080365275008755489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38053106880974066690014637 14269915080365275008755489)
        ·
          refine ⟨10702436310273956256566617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14269915080365275008755489 10702436310273956256566617)
          ·
            refine ⟨8026827232705467192424963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10702436310273956256566617 8026827232705467192424963)
            ·
              refine ⟨12040240849058200788637445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026827232705467192424963 12040240849058200788637445)
              ·
                refine ⟨2257545159198412647869521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12040240849058200788637445 2257545159198412647869521)
                ·
                  refine ⟨1693158869398809485902141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257545159198412647869521 1693158869398809485902141)
                  ·
                    refine ⟨634934576024553557213303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693158869398809485902141 634934576024553557213303)
                    ·
                      rfl

theorem cell22_1854796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_1854796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854796 prefixEnd_1854796 := by exact prefixLift 1854796
  have htrace : WordTrace (prefixWord ++ tailWord_1854796) baseStart_1854796 baseEnd_1854796 := by
    simpa [prefixWord, tailWord_1854796, baseEnd_1854796] using wordTrace_append hprefix tailTrace_1854796
  have hstable : (prefixWord ++ tailWord_1854796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854796).length < 2 ^ (prefixWord ++ tailWord_1854796).sum := by decide
  have hdescent : baseEnd_1854796 < baseStart_1854796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854869 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1854869 : Nat := 118140960795 + 1854869 * 2 ^ 59
def prefixEnd_1854869 : Nat := 4983230072969 + 3 ^ 40 * 1854869 * 2
def baseEnd_1854869 : Nat := 634959565416405700138079

theorem tailTrace_1854869 : CollatzResearch.WordTrace tailWord_1854869 prefixEnd_1854869 634959565416405700138079 := by
  unfold tailWord_1854869
  simp only [CollatzResearch.WordTrace]
  refine ⟨67652630317133874249655661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45101753544755916166437107 67652630317133874249655661)
  ·
    refine ⟨25369736368925202843620873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67652630317133874249655661 25369736368925202843620873)
    ·
      refine ⟨19027302276693902132715655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25369736368925202843620873 19027302276693902132715655)
      ·
        refine ⟨28540953415040853199073483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19027302276693902132715655 28540953415040853199073483)
        ·
          refine ⟨42811430122561279798610225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28540953415040853199073483 42811430122561279798610225)
          ·
            refine ⟨32108572591920959848957669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42811430122561279798610225 32108572591920959848957669)
            ·
              refine ⟨6020357360985179971679563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32108572591920959848957669 6020357360985179971679563)
              ·
                refine ⟨9030536041477769957519345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020357360985179971679563 9030536041477769957519345)
                ·
                  refine ⟨6772902031108327468139509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030536041477769957519345 6772902031108327468139509)
                  ·
                    refine ⟨634959565416405700138079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6772902031108327468139509 634959565416405700138079)
                    ·
                      rfl

theorem cell22_1854869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1854869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854869 prefixEnd_1854869 := by exact prefixLift 1854869
  have htrace : WordTrace (prefixWord ++ tailWord_1854869) baseStart_1854869 baseEnd_1854869 := by
    simpa [prefixWord, tailWord_1854869, baseEnd_1854869] using wordTrace_append hprefix tailTrace_1854869
  have hstable : (prefixWord ++ tailWord_1854869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854869).length < 2 ^ (prefixWord ++ tailWord_1854869).sum := by decide
  have hdescent : baseEnd_1854869 < baseStart_1854869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854965 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1854965 : Nat := 118140960795 + 1854965 * 2 ^ 59
def prefixEnd_1854965 : Nat := 4983230072969 + 3 ^ 40 * 1854965 * 2
def baseEnd_1854965 : Nat := 634992428178293449737785

theorem tailTrace_1854965 : CollatzResearch.WordTrace tailWord_1854965 prefixEnd_1854965 634992428178293449737785 := by
  unfold tailWord_1854965
  simp only [CollatzResearch.WordTrace]
  refine ⟨67656131724786082645150349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45104087816524055096766899 67656131724786082645150349)
  ·
    refine ⟨25371049396794780991931381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67656131724786082645150349 25371049396794780991931381)
    ·
      refine ⟨2378535880949510717993567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25371049396794780991931381 2378535880949510717993567)
      ·
        refine ⟨3567803821424266076990351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378535880949510717993567 3567803821424266076990351)
        ·
          refine ⟨5351705732136399115485527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567803821424266076990351 5351705732136399115485527)
          ·
            refine ⟨8027558598204598673228291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351705732136399115485527 8027558598204598673228291)
            ·
              refine ⟨12041337897306898009842437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027558598204598673228291 12041337897306898009842437)
              ·
                refine ⟨2257750855745043376845457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12041337897306898009842437 2257750855745043376845457)
                ·
                  refine ⟨1693313141808782532634093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257750855745043376845457 1693313141808782532634093)
                  ·
                    refine ⟨634992428178293449737785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693313141808782532634093 634992428178293449737785)
                    ·
                      rfl

theorem cell22_1854965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1854965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854965 prefixEnd_1854965 := by exact prefixLift 1854965
  have htrace : WordTrace (prefixWord ++ tailWord_1854965) baseStart_1854965 baseEnd_1854965 := by
    simpa [prefixWord, tailWord_1854965, baseEnd_1854965] using wordTrace_append hprefix tailTrace_1854965
  have hstable : (prefixWord ++ tailWord_1854965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854965).length < 2 ^ (prefixWord ++ tailWord_1854965).sum := by decide
  have hdescent : baseEnd_1854965 < baseStart_1854965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854978 : List Nat := [3, 4, 1, 2, 1, 1, 3, 7]
def baseStart_1854978 : Nat := 118140960795 + 1854978 * 2 ^ 59
def prefixEnd_1854978 : Nat := 4983230072969 + 3 ^ 40 * 1854978 * 2
def baseEnd_1854978 : Nat := 70555208704885083240305

theorem tailTrace_1854978 : CollatzResearch.WordTrace tailWord_1854978 prefixEnd_1854978 70555208704885083240305 := by
  unfold tailWord_1854978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914151468434746466343397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45104403915825990576915725 16914151468434746466343397)
  ·
    refine ⟨3171403400331514962439387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16914151468434746466343397 3171403400331514962439387)
    ·
      refine ⟨4757105100497272443659081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3171403400331514962439387 4757105100497272443659081)
      ·
        refine ⟨3567828825372954332744311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4757105100497272443659081 3567828825372954332744311)
        ·
          refine ⟨5351743238059431499116467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567828825372954332744311 5351743238059431499116467)
          ·
            refine ⟨8027614857089147248674701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351743238059431499116467 8027614857089147248674701)
            ·
              refine ⟨3010355571408430218253013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8027614857089147248674701 3010355571408430218253013)
              ·
                refine ⟨70555208704885083240305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3010355571408430218253013 70555208704885083240305)
                ·
                  rfl

theorem cell22_1854978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_1854978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1854978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1854978 prefixEnd_1854978 := by exact prefixLift 1854978
  have htrace : WordTrace (prefixWord ++ tailWord_1854978) baseStart_1854978 baseEnd_1854978 := by
    simpa [prefixWord, tailWord_1854978, baseEnd_1854978] using wordTrace_append hprefix tailTrace_1854978
  have hstable : (prefixWord ++ tailWord_1854978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854978).length < 2 ^ (prefixWord ++ tailWord_1854978).sum := by decide
  have hdescent : baseEnd_1854978 < baseStart_1854978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855010 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1855010 : Nat := 118140960795 + 1855010 * 2 ^ 59
def prefixEnd_1855010 : Nat := 4983230072969 + 3 ^ 40 * 1855010 * 2
def baseEnd_1855010 : Nat := 635007832597928332362647

theorem tailTrace_1855010 : CollatzResearch.WordTrace tailWord_1855010 prefixEnd_1855010 635007832597928332362647 := by
  unfold tailWord_1855010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914443252405763832634621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45105182006415370220358989 16914443252405763832634621)
  ·
    refine ⟨6342916219652161437237983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16914443252405763832634621 6342916219652161437237983)
    ·
      refine ⟨9514374329478242155856975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342916219652161437237983 9514374329478242155856975)
      ·
        refine ⟨14271561494217363233785463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9514374329478242155856975 14271561494217363233785463)
        ·
          refine ⟨21407342241326044850678195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14271561494217363233785463 21407342241326044850678195)
          ·
            refine ⟨32111013361989067276017293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21407342241326044850678195 32111013361989067276017293)
            ·
              refine ⟨12041630010745900228506485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32111013361989067276017293 12041630010745900228506485)
              ·
                refine ⟨1128902813507428146422483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12041630010745900228506485 1128902813507428146422483)
                ·
                  refine ⟨1693354220261142219633725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128902813507428146422483 1693354220261142219633725)
                  ·
                    refine ⟨635007832597928332362647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693354220261142219633725 635007832597928332362647)
                    ·
                      rfl

theorem cell22_1855010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1855010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855010 prefixEnd_1855010 := by exact prefixLift 1855010
  have htrace : WordTrace (prefixWord ++ tailWord_1855010) baseStart_1855010 baseEnd_1855010 := by
    simpa [prefixWord, tailWord_1855010, baseEnd_1855010] using wordTrace_append hprefix tailTrace_1855010
  have hstable : (prefixWord ++ tailWord_1855010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855010).length < 2 ^ (prefixWord ++ tailWord_1855010).sum := by decide
  have hdescent : baseEnd_1855010 < baseStart_1855010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
