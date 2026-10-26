import V185TrunkScan22Chunk377

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3371256 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_3371256 : Nat := 118140960795 + 3371256 * 2 ^ 59
def prefixEnd_3371256 : Nat := 4983230072969 + 3 ^ 40 * 3371256 * 2
def baseEnd_3371256 : Nat := 384683274967548262021307

theorem tailTrace_3371256 : CollatzResearch.WordTrace tailWord_3371256 prefixEnd_3371256 384683274967548262021307 := by
  unfold tailWord_3371256
  simp only [CollatzResearch.WordTrace]
  refine ⟨61479903937261375765470811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81973205249681834353961081 61479903937261375765470811)
  ·
    refine ⟨92219855905892063648206217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61479903937261375765470811 92219855905892063648206217)
    ·
      refine ⟨69164891929419047736154663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92219855905892063648206217 69164891929419047736154663)
      ·
        refine ⟨103747337894128571604231995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69164891929419047736154663 103747337894128571604231995)
        ·
          refine ⟨155621006841192857406347993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103747337894128571604231995 155621006841192857406347993)
          ·
            refine ⟨116715755130894643054760995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155621006841192857406347993 116715755130894643054760995)
            ·
              refine ⟨175073632696341964582141493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116715755130894643054760995 175073632696341964582141493)
              ·
                refine ⟨16413153065282059179575765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175073632696341964582141493 16413153065282059179575765)
                ·
                  refine ⟨384683274967548262021307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16413153065282059179575765 384683274967548262021307)
                  ·
                    rfl

theorem cell22_3371256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_3371256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371256 prefixEnd_3371256 := by exact prefixLift 3371256
  have htrace : WordTrace (prefixWord ++ tailWord_3371256) baseStart_3371256 baseEnd_3371256 := by
    simpa [prefixWord, tailWord_3371256, baseEnd_3371256] using wordTrace_append hprefix tailTrace_3371256
  have hstable : (prefixWord ++ tailWord_3371256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371256).length < 2 ^ (prefixWord ++ tailWord_3371256).sum := by decide
  have hdescent : baseEnd_3371256 < baseStart_3371256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371273 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 5]
def baseStart_3371273 : Nat := 118140960795 + 3371273 * 2 ^ 59
def prefixEnd_3371273 : Nat := 4983230072969 + 3 ^ 40 * 3371273 * 2
def baseEnd_3371273 : Nat := 384685214783354136129623

theorem tailTrace_3371273 : CollatzResearch.WordTrace tailWord_3371273 prefixEnd_3371273 384685214783354136129623 := by
  unfold tailWord_3371273
  simp only [CollatzResearch.WordTrace]
  refine ⟨122960427915461163434310473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81973618610307442289540315 122960427915461163434310473)
  ·
    refine ⟨92220320936595872575732855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122960427915461163434310473 92220320936595872575732855)
    ·
      refine ⟨138330481404893808863599283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92220320936595872575732855 138330481404893808863599283)
      ·
        refine ⟨207495722107340713295398925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138330481404893808863599283 207495722107340713295398925)
        ·
          refine ⟨77810895790252767485774597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207495722107340713295398925 77810895790252767485774597)
          ·
            refine ⟨14589542960672393903582737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77810895790252767485774597 14589542960672393903582737)
            ·
              refine ⟨10942157220504295427687053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14589542960672393903582737 10942157220504295427687053)
              ·
                refine ⟨4103308957689110785382645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10942157220504295427687053 4103308957689110785382645)
                ·
                  refine ⟨384685214783354136129623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4103308957689110785382645 384685214783354136129623)
                  ·
                    rfl

theorem cell22_3371273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_3371273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371273 prefixEnd_3371273 := by exact prefixLift 3371273
  have htrace : WordTrace (prefixWord ++ tailWord_3371273) baseStart_3371273 baseEnd_3371273 := by
    simpa [prefixWord, tailWord_3371273, baseEnd_3371273] using wordTrace_append hprefix tailTrace_3371273
  have hstable : (prefixWord ++ tailWord_3371273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371273).length < 2 ^ (prefixWord ++ tailWord_3371273).sum := by decide
  have hdescent : baseEnd_3371273 < baseStart_3371273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371365 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3371365 : Nat := 118140960795 + 3371365 * 2 ^ 59
def prefixEnd_3371365 : Nat := 4983230072969 + 3 ^ 40 * 3371365 * 2
def baseEnd_3371365 : Nat := 1154087137830204835088587

theorem tailTrace_3371365 : CollatzResearch.WordTrace tailWord_3371365 prefixEnd_3371365 1154087137830204835088587 := by
  unfold tailWord_3371365
  simp only [CollatzResearch.WordTrace]
  refine ⟨122963783431127863146659549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81975855620751908764439699 122963783431127863146659549)
  ·
    refine ⟨46111418786672948679997331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122963783431127863146659549 46111418786672948679997331)
    ·
      refine ⟨69167128180009423019995997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46111418786672948679997331 69167128180009423019995997)
      ·
        refine ⟨25937673067503533632498499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69167128180009423019995997 25937673067503533632498499)
        ·
          refine ⟨38906509601255300448747749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25937673067503533632498499 38906509601255300448747749)
          ·
            refine ⟨7294970550235368834140203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38906509601255300448747749 7294970550235368834140203)
            ·
              refine ⟨10942455825353053251210305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294970550235368834140203 10942455825353053251210305)
              ·
                refine ⟨8206841869014789938407729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10942455825353053251210305 8206841869014789938407729)
                ·
                  refine ⟨6155131401761092453805797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8206841869014789938407729 6155131401761092453805797)
                  ·
                    refine ⟨1154087137830204835088587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6155131401761092453805797 1154087137830204835088587)
                    ·
                      rfl

theorem cell22_3371365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3371365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371365 prefixEnd_3371365 := by exact prefixLift 3371365
  have htrace : WordTrace (prefixWord ++ tailWord_3371365) baseStart_3371365 baseEnd_3371365 := by
    simpa [prefixWord, tailWord_3371365, baseEnd_3371365] using wordTrace_append hprefix tailTrace_3371365
  have hstable : (prefixWord ++ tailWord_3371365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371365).length < 2 ^ (prefixWord ++ tailWord_3371365).sum := by decide
  have hdescent : baseEnd_3371365 < baseStart_3371365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371414 : List Nat := [5, 3, 1, 2, 1, 10]
def baseStart_3371414 : Nat := 118140960795 + 3371414 * 2 ^ 59
def prefixEnd_3371414 : Nat := 4983230072969 + 3 ^ 40 * 3371414 * 2
def baseEnd_3371414 : Nat := 14248196438661543711277

theorem tailTrace_3371414 : CollatzResearch.WordTrace tailWord_3371414 prefixEnd_3371414 14248196438661543711277 := by
  unfold tailWord_3371414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685348162996896532199581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81977047071966896343462197 7685348162996896532199581)
  ·
    refine ⟨2882005561123836199574843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7685348162996896532199581 2882005561123836199574843)
    ·
      refine ⟨4323008341685754299362265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882005561123836199574843 4323008341685754299362265)
      ·
        refine ⟨3242256256264315724521699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323008341685754299362265 3242256256264315724521699)
        ·
          refine ⟨4863384384396473586782549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242256256264315724521699 4863384384396473586782549)
          ·
            refine ⟨14248196438661543711277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4863384384396473586782549 14248196438661543711277)
            ·
              rfl

theorem cell22_3371414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 10].length) (baseStart_3371414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371414 prefixEnd_3371414 := by exact prefixLift 3371414
  have htrace : WordTrace (prefixWord ++ tailWord_3371414) baseStart_3371414 baseEnd_3371414 := by
    simpa [prefixWord, tailWord_3371414, baseEnd_3371414] using wordTrace_append hprefix tailTrace_3371414
  have hstable : (prefixWord ++ tailWord_3371414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371414).length < 2 ^ (prefixWord ++ tailWord_3371414).sum := by decide
  have hdescent : baseEnd_3371414 < baseStart_3371414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371487 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 4]
def baseStart_3371487 : Nat := 118140960795 + 3371487 * 2 ^ 59
def prefixEnd_3371487 : Nat := 4983230072969 + 3 ^ 40 * 3371487 * 2
def baseEnd_3371487 : Nat := 384709633641145727846071

theorem tailTrace_3371487 : CollatzResearch.WordTrace tailWord_3371487 prefixEnd_3371487 384709633641145727846071 := by
  unfold tailWord_3371487
  simp only [CollatzResearch.WordTrace]
  refine ⟨122968233136685877982600715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81978822091123918655067143 122968233136685877982600715)
  ·
    refine ⟨184452349705028816973901073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122968233136685877982600715 184452349705028816973901073)
    ·
      refine ⟨138339262278771612730425805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184452349705028816973901073 138339262278771612730425805)
      ·
        refine ⟨51877223354539354773909677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138339262278771612730425805 51877223354539354773909677)
        ·
          refine ⟨19453958757952258040216129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51877223354539354773909677 19453958757952258040216129)
          ·
            refine ⟨14590469068464193530162097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19453958757952258040216129 14590469068464193530162097)
            ·
              refine ⟨10942851801348145147621573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14590469068464193530162097 10942851801348145147621573)
              ·
                refine ⟨2051784712752777215179045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10942851801348145147621573 2051784712752777215179045)
                ·
                  refine ⟨384709633641145727846071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051784712752777215179045 384709633641145727846071)
                  ·
                    rfl

theorem cell22_3371487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 4].length) (baseStart_3371487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371487 prefixEnd_3371487 := by exact prefixLift 3371487
  have htrace : WordTrace (prefixWord ++ tailWord_3371487) baseStart_3371487 baseEnd_3371487 := by
    simpa [prefixWord, tailWord_3371487, baseEnd_3371487] using wordTrace_append hprefix tailTrace_3371487
  have hstable : (prefixWord ++ tailWord_3371487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371487).length < 2 ^ (prefixWord ++ tailWord_3371487).sum := by decide
  have hdescent : baseEnd_3371487 < baseStart_3371487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371502 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3371502 : Nat := 118140960795 + 3371502 * 2 ^ 59
def prefixEnd_3371502 : Nat := 4983230072969 + 3 ^ 40 * 3371502 * 2
def baseEnd_3371502 : Nat := 1154134035729982144413167

theorem tailTrace_3371502 : CollatzResearch.WordTrace tailWord_3371502 prefixEnd_3371502 1154134035729982144413167 := by
  unfold tailWord_3371502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371097528953941943049595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81979186821087690362931173 15371097528953941943049595)
  ·
    refine ⟨23056646293430912914574393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15371097528953941943049595 23056646293430912914574393)
    ·
      refine ⟨17292484720073184685930795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23056646293430912914574393 17292484720073184685930795)
      ·
        refine ⟨25938727080109777028896193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17292484720073184685930795 25938727080109777028896193)
        ·
          refine ⟨19454045310082332771672145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25938727080109777028896193 19454045310082332771672145)
          ·
            refine ⟨14590533982561749578754109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19454045310082332771672145 14590533982561749578754109)
            ·
              refine ⟨5471450243460656092032791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14590533982561749578754109 5471450243460656092032791)
              ·
                refine ⟨8207175365190984138049187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471450243460656092032791 8207175365190984138049187)
                ·
                  refine ⟨12310763047786476207073781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8207175365190984138049187 12310763047786476207073781)
                  ·
                    refine ⟨1154134035729982144413167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12310763047786476207073781 1154134035729982144413167)
                    ·
                      rfl

theorem cell22_3371502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3371502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371502 prefixEnd_3371502 := by exact prefixLift 3371502
  have htrace : WordTrace (prefixWord ++ tailWord_3371502) baseStart_3371502 baseEnd_3371502 := by
    simpa [prefixWord, tailWord_3371502, baseEnd_3371502] using wordTrace_append hprefix tailTrace_3371502
  have hstable : (prefixWord ++ tailWord_3371502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371502).length < 2 ^ (prefixWord ++ tailWord_3371502).sum := by decide
  have hdescent : baseEnd_3371502 < baseStart_3371502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371641 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 1, 4]
def baseStart_3371641 : Nat := 118140960795 + 3371641 * 2 ^ 59
def prefixEnd_3371641 : Nat := 4983230072969 + 3 ^ 40 * 3371641 * 2
def baseEnd_3371641 : Nat := 1154181618270632115187741

theorem tailTrace_3371641 : CollatzResearch.WordTrace tailWord_3371641 prefixEnd_3371641 1154181618270632115187741 := by
  unfold tailWord_3371641
  simp only [CollatzResearch.WordTrace]
  refine ⟨122973849978127962283706777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81982566652085308189137851 122973849978127962283706777)
  ·
    refine ⟨92230387483595971712780083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122973849978127962283706777 92230387483595971712780083)
    ·
      refine ⟨138345581225393957569170125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92230387483595971712780083 138345581225393957569170125)
      ·
        refine ⟨51879592959522734088438797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138345581225393957569170125 51879592959522734088438797)
        ·
          refine ⟨19454847359821025283164549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51879592959522734088438797 19454847359821025283164549)
          ·
            refine ⟨3647783879966442240593353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19454847359821025283164549 3647783879966442240593353)
            ·
              refine ⟨2735837909974831680445015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647783879966442240593353 2735837909974831680445015)
              ·
                refine ⟨4103756864962247520667523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735837909974831680445015 4103756864962247520667523)
                ·
                  refine ⟨6155635297443371281001285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103756864962247520667523 6155635297443371281001285)
                  ·
                    refine ⟨1154181618270632115187741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6155635297443371281001285 1154181618270632115187741)
                    ·
                      rfl

theorem cell22_3371641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_3371641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371641 prefixEnd_3371641 := by exact prefixLift 3371641
  have htrace : WordTrace (prefixWord ++ tailWord_3371641) baseStart_3371641 baseEnd_3371641 := by
    simpa [prefixWord, tailWord_3371641, baseEnd_3371641] using wordTrace_append hprefix tailTrace_3371641
  have hstable : (prefixWord ++ tailWord_3371641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371641).length < 2 ^ (prefixWord ++ tailWord_3371641).sum := by decide
  have hdescent : baseEnd_3371641 < baseStart_3371641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371671 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 2, 3]
def baseStart_3371671 : Nat := 118140960795 + 3371671 * 2 ^ 59
def prefixEnd_3371671 : Nat := 4983230072969 + 3 ^ 40 * 3371671 * 2
def baseEnd_3371671 : Nat := 1154191887883722036937649

theorem tailTrace_3371671 : CollatzResearch.WordTrace tailWord_3371671 prefixEnd_3371671 1154191887883722036937649 := by
  unfold tailWord_3371671
  simp only [CollatzResearch.WordTrace]
  refine ⟨122974944168019277407298867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81983296112012851604865911 122974944168019277407298867)
  ·
    refine ⟨184462416252028916110948301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122974944168019277407298867 184462416252028916110948301)
    ·
      refine ⟨69173406094510843541605613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184462416252028916110948301 69173406094510843541605613)
      ·
        refine ⟨25940027285441566328102105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69173406094510843541605613 25940027285441566328102105)
        ·
          refine ⟨19455020464081174746076579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25940027285441566328102105 19455020464081174746076579)
          ·
            refine ⟨29182530696121762119114869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19455020464081174746076579 29182530696121762119114869)
            ·
              refine ⟨2735862252761415198667019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29182530696121762119114869 2735862252761415198667019)
              ·
                refine ⟨4103793379142122798000529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735862252761415198667019 4103793379142122798000529)
                ·
                  refine ⟨3077845034356592098500397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103793379142122798000529 3077845034356592098500397)
                  ·
                    refine ⟨1154191887883722036937649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3077845034356592098500397 1154191887883722036937649)
                    ·
                      rfl

theorem cell22_3371671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_3371671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371671 prefixEnd_3371671 := by exact prefixLift 3371671
  have htrace : WordTrace (prefixWord ++ tailWord_3371671) baseStart_3371671 baseEnd_3371671 := by
    simpa [prefixWord, tailWord_3371671, baseEnd_3371671] using wordTrace_append hprefix tailTrace_3371671
  have hstable : (prefixWord ++ tailWord_3371671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371671).length < 2 ^ (prefixWord ++ tailWord_3371671).sum := by decide
  have hdescent : baseEnd_3371671 < baseStart_3371671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371690 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_3371690 : Nat := 118140960795 + 3371690 * 2 ^ 59
def prefixEnd_3371690 : Nat := 4983230072969 + 3 ^ 40 * 3371690 * 2
def baseEnd_3371690 : Nat := 384732797324004106904197

theorem tailTrace_3371690 : CollatzResearch.WordTrace tailWord_3371690 prefixEnd_3371690 384732797324004106904197 := by
  unfold tailWord_3371690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30743909288737610913060131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81983758103300295768160349 30743909288737610913060131)
  ·
    refine ⟨46115863933106416369590197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30743909288737610913060131 46115863933106416369590197)
    ·
      refine ⟨4323362243728726534649081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46115863933106416369590197 4323362243728726534649081)
      ·
        refine ⟨3242521682796544900986811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323362243728726534649081 3242521682796544900986811)
        ·
          refine ⟨4863782524194817351480217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242521682796544900986811 4863782524194817351480217)
          ·
            refine ⟨3647836893146113013610163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4863782524194817351480217 3647836893146113013610163)
            ·
              refine ⟨5471755339719169520415245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647836893146113013610163 5471755339719169520415245)
              ·
                refine ⟨2051908252394688570155717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5471755339719169520415245 2051908252394688570155717)
                ·
                  refine ⟨384732797324004106904197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051908252394688570155717 384732797324004106904197)
                  ·
                    rfl

theorem cell22_3371690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_3371690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371690 prefixEnd_3371690 := by exact prefixLift 3371690
  have htrace : WordTrace (prefixWord ++ tailWord_3371690) baseStart_3371690 baseEnd_3371690 := by
    simpa [prefixWord, tailWord_3371690, baseEnd_3371690] using wordTrace_append hprefix tailTrace_3371690
  have hstable : (prefixWord ++ tailWord_3371690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371690).length < 2 ^ (prefixWord ++ tailWord_3371690).sum := by decide
  have hdescent : baseEnd_3371690 < baseStart_3371690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371712 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_3371712 : Nat := 118140960795 + 3371712 * 2 ^ 59
def prefixEnd_3371712 : Nat := 4983230072969 + 3 ^ 40 * 3371712 * 2
def baseEnd_3371712 : Nat := 384735307673870532220841

theorem tailTrace_3371712 : CollatzResearch.WordTrace tailWord_3371712 prefixEnd_3371712 384735307673870532220841 := by
  unfold tailWord_3371712
  simp only [CollatzResearch.WordTrace]
  refine ⟨61488219780435370704770695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81984293040580494273027593 61488219780435370704770695)
  ·
    refine ⟨92232329670653056057156043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61488219780435370704770695 92232329670653056057156043)
    ·
      refine ⟨138348494505979584085734065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92232329670653056057156043 138348494505979584085734065)
      ·
        refine ⟨103761370879484688064300549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138348494505979584085734065 103761370879484688064300549)
        ·
          refine ⟨19455257039903379012056353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103761370879484688064300549 19455257039903379012056353)
          ·
            refine ⟨14591442779927534259042265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19455257039903379012056353 14591442779927534259042265)
            ·
              refine ⟨10943582084945650694281699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14591442779927534259042265 10943582084945650694281699)
              ·
                refine ⟨16415373127418476041422549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943582084945650694281699 16415373127418476041422549)
                ·
                  refine ⟨384735307673870532220841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16415373127418476041422549 384735307673870532220841)
                  ·
                    rfl

theorem cell22_3371712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_3371712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371712 prefixEnd_3371712 := by exact prefixLift 3371712
  have htrace : WordTrace (prefixWord ++ tailWord_3371712) baseStart_3371712 baseEnd_3371712 := by
    simpa [prefixWord, tailWord_3371712, baseEnd_3371712] using wordTrace_append hprefix tailTrace_3371712
  have hstable : (prefixWord ++ tailWord_3371712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371712).length < 2 ^ (prefixWord ++ tailWord_3371712).sum := by decide
  have hdescent : baseEnd_3371712 < baseStart_3371712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371716 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3371716 : Nat := 118140960795 + 3371716 * 2 ^ 59
def prefixEnd_3371716 : Nat := 4983230072969 + 3 ^ 40 * 3371716 * 2
def baseEnd_3371716 : Nat := 1154207292303356919562511

theorem tailTrace_3371716 : CollatzResearch.WordTrace tailWord_3371716 prefixEnd_3371716 1154207292303356919562511 := by
  unfold tailWord_3371716
  simp only [CollatzResearch.WordTrace]
  refine ⟨61488292726428125046343501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81984390301904166728458001 61488292726428125046343501)
  ·
    refine ⟨23058109772410546892378813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61488292726428125046343501 23058109772410546892378813)
    ·
      refine ⟨8646791164653955084642055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23058109772410546892378813 8646791164653955084642055)
      ·
        refine ⟨12970186746980932626963083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8646791164653955084642055 12970186746980932626963083)
        ·
          refine ⟨19455280120471398940444625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12970186746980932626963083 19455280120471398940444625)
          ·
            refine ⟨14591460090353549205333469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19455280120471398940444625 14591460090353549205333469)
            ·
              refine ⟨5471797533882580952000051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14591460090353549205333469 5471797533882580952000051)
              ·
                refine ⟨8207696300823871428000077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471797533882580952000051 8207696300823871428000077)
                ·
                  refine ⟨3077886112808951785500029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8207696300823871428000077 3077886112808951785500029)
                  ·
                    refine ⟨1154207292303356919562511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3077886112808951785500029 1154207292303356919562511)
                    ·
                      rfl

theorem cell22_3371716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3371716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371716 prefixEnd_3371716 := by exact prefixLift 3371716
  have htrace : WordTrace (prefixWord ++ tailWord_3371716) baseStart_3371716 baseEnd_3371716 := by
    simpa [prefixWord, tailWord_3371716, baseEnd_3371716] using wordTrace_append hprefix tailTrace_3371716
  have hstable : (prefixWord ++ tailWord_3371716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371716).length < 2 ^ (prefixWord ++ tailWord_3371716).sum := by decide
  have hdescent : baseEnd_3371716 < baseStart_3371716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371718 : List Nat := [6, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3371718 : Nat := 118140960795 + 3371718 * 2 ^ 59
def prefixEnd_3371718 : Nat := 4983230072969 + 3 ^ 40 * 3371718 * 2
def baseEnd_3371718 : Nat := 128245330771581064556945

theorem tailTrace_3371718 : CollatzResearch.WordTrace tailWord_3371718 prefixEnd_3371718 128245330771581064556945 := by
  unfold tailWord_3371718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843020574964031388570619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81984438932566002956173205 3843020574964031388570619)
  ·
    refine ⟨5764530862446047082855929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3843020574964031388570619 5764530862446047082855929)
    ·
      refine ⟨4323398146834535312141947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5764530862446047082855929 4323398146834535312141947)
      ·
        refine ⟨6485097220251802968212921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323398146834535312141947 6485097220251802968212921)
        ·
          refine ⟨4863822915188852226159691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6485097220251802968212921 4863822915188852226159691)
          ·
            refine ⟨7295734372783278339239537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863822915188852226159691 7295734372783278339239537)
            ·
              refine ⟨5471800779587458754429653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7295734372783278339239537 5471800779587458754429653)
              ·
                refine ⟨128245330771581064556945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5471800779587458754429653 128245330771581064556945)
                ·
                  rfl

theorem cell22_3371718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3371718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371718 prefixEnd_3371718 := by exact prefixLift 3371718
  have htrace : WordTrace (prefixWord ++ tailWord_3371718) baseStart_3371718 baseEnd_3371718 := by
    simpa [prefixWord, tailWord_3371718, baseEnd_3371718] using wordTrace_append hprefix tailTrace_3371718
  have hstable : (prefixWord ++ tailWord_3371718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371718).length < 2 ^ (prefixWord ++ tailWord_3371718).sum := by decide
  have hdescent : baseEnd_3371718 < baseStart_3371718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371787 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_3371787 : Nat := 118140960795 + 3371787 * 2 ^ 59
def prefixEnd_3371787 : Nat := 4983230072969 + 3 ^ 40 * 3371787 * 2
def baseEnd_3371787 : Nat := 1154231597054336401037293

theorem tailTrace_3371787 : CollatzResearch.WordTrace tailWord_3371787 prefixEnd_3371787 1154231597054336401037293 := by
  unfold tailWord_3371787
  simp only [CollatzResearch.WordTrace]
  refine ⟨122979175035599029218521615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81986116690399352812347743 122979175035599029218521615)
  ·
    refine ⟨184468762553398543827782423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122979175035599029218521615 184468762553398543827782423)
    ·
      refine ⟨276703143830097815741673635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184468762553398543827782423 276703143830097815741673635)
      ·
        refine ⟨415054715745146723612510453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276703143830097815741673635 415054715745146723612510453)
        ·
          refine ⟨38911379601107505338672855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415054715745146723612510453 38911379601107505338672855)
          ·
            refine ⟨58367069401661258008009283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38911379601107505338672855 58367069401661258008009283)
            ·
              refine ⟨87550604102491887012013925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58367069401661258008009283 87550604102491887012013925)
              ·
                refine ⟨16415738269217228814752611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87550604102491887012013925 16415738269217228814752611)
                ·
                  refine ⟨24623607403825843222128917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16415738269217228814752611 24623607403825843222128917)
                  ·
                    refine ⟨1154231597054336401037293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24623607403825843222128917 1154231597054336401037293)
                    ·
                      rfl

theorem cell22_3371787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_3371787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371787 prefixEnd_3371787 := by exact prefixLift 3371787
  have htrace : WordTrace (prefixWord ++ tailWord_3371787) baseStart_3371787 baseEnd_3371787 := by
    simpa [prefixWord, tailWord_3371787, baseEnd_3371787] using wordTrace_append hprefix tailTrace_3371787
  have hstable : (prefixWord ++ tailWord_3371787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371787).length < 2 ^ (prefixWord ++ tailWord_3371787).sum := by decide
  have hdescent : baseEnd_3371787 < baseStart_3371787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371804 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3371804 : Nat := 118140960795 + 3371804 * 2 ^ 59
def prefixEnd_3371804 : Nat := 4983230072969 + 3 ^ 40 * 3371804 * 2
def baseEnd_3371804 : Nat := 1154237416501754023362241

theorem tailTrace_3371804 : CollatzResearch.WordTrace tailWord_3371804 prefixEnd_3371804 1154237416501754023362241 := by
  unfold tailWord_3371804
  simp only [CollatzResearch.WordTrace]
  refine ⟨61489897538268720560945233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81986530051024960747926977 61489897538268720560945233)
  ·
    refine ⟨46117423153701540420708925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61489897538268720560945233 46117423153701540420708925)
    ·
      refine ⟨17294033682638077657765847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46117423153701540420708925 17294033682638077657765847)
      ·
        refine ⟨25941050523957116486648771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17294033682638077657765847 25941050523957116486648771)
        ·
          refine ⟨38911575785935674729973157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25941050523957116486648771 38911575785935674729973157)
          ·
            refine ⟨7295920459862939011869967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38911575785935674729973157 7295920459862939011869967)
            ·
              refine ⟨10943880689794408517804951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295920459862939011869967 10943880689794408517804951)
              ·
                refine ⟨16415821034691612776707427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943880689794408517804951 16415821034691612776707427)
                ·
                  refine ⟨24623731552037419165061141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16415821034691612776707427 24623731552037419165061141)
                  ·
                    refine ⟨1154237416501754023362241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24623731552037419165061141 1154237416501754023362241)
                    ·
                      rfl

theorem cell22_3371804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3371804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371804 prefixEnd_3371804 := by exact prefixLift 3371804
  have htrace : WordTrace (prefixWord ++ tailWord_3371804) baseStart_3371804 baseEnd_3371804 := by
    simpa [prefixWord, tailWord_3371804, baseEnd_3371804] using wordTrace_append hprefix tailTrace_3371804
  have hstable : (prefixWord ++ tailWord_3371804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371804).length < 2 ^ (prefixWord ++ tailWord_3371804).sum := by decide
  have hdescent : baseEnd_3371804 < baseStart_3371804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371911 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3371911 : Nat := 118140960795 + 3371911 * 2 ^ 59
def prefixEnd_3371911 : Nat := 4983230072969 + 3 ^ 40 * 3371911 * 2
def baseEnd_3371911 : Nat := 1154274044788441410936913

theorem tailTrace_3371911 : CollatzResearch.WordTrace tailWord_3371911 prefixEnd_3371911 1154274044788441410936913 := by
  unfold tailWord_3371911
  simp only [CollatzResearch.WordTrace]
  refine ⟨122983697687149798396035587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81989131791433198930690391 122983697687149798396035587)
  ·
    refine ⟨184475546530724697594053381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122983697687149798396035587 184475546530724697594053381)
    ·
      refine ⟨34589164974510880798885009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184475546530724697594053381 34589164974510880798885009)
      ·
        refine ⟨25941873730883160599163757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34589164974510880798885009 25941873730883160599163757)
        ·
          refine ⟨9728202649081185224686409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25941873730883160599163757 9728202649081185224686409)
          ·
            refine ⟨7296151986810888918514807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9728202649081185224686409 7296151986810888918514807)
            ·
              refine ⟨10944227980216333377772211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296151986810888918514807 10944227980216333377772211)
              ·
                refine ⟨16416341970324500066658317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10944227980216333377772211 16416341970324500066658317)
                ·
                  refine ⟨6156128238871687524996869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16416341970324500066658317 6156128238871687524996869)
                  ·
                    refine ⟨1154274044788441410936913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6156128238871687524996869 1154274044788441410936913)
                    ·
                      rfl

theorem cell22_3371911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3371911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371911 prefixEnd_3371911 := by exact prefixLift 3371911
  have htrace : WordTrace (prefixWord ++ tailWord_3371911) baseStart_3371911 baseEnd_3371911 := by
    simpa [prefixWord, tailWord_3371911, baseEnd_3371911] using wordTrace_append hprefix tailTrace_3371911
  have hstable : (prefixWord ++ tailWord_3371911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371911).length < 2 ^ (prefixWord ++ tailWord_3371911).sum := by decide
  have hdescent : baseEnd_3371911 < baseStart_3371911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372003 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 3, 3]
def baseStart_3372003 : Nat := 118140960795 + 3372003 * 2 ^ 59
def prefixEnd_3372003 : Nat := 4983230072969 + 3 ^ 40 * 3372003 * 2
def baseEnd_3372003 : Nat := 1154305538268583837636631

theorem tailTrace_3372003 : CollatzResearch.WordTrace tailWord_3372003 prefixEnd_3372003 1154305538268583837636631 := by
  unfold tailWord_3372003
  simp only [CollatzResearch.WordTrace]
  refine ⟨122987053202816498108384663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81991368801877665405589775 122987053202816498108384663)
  ·
    refine ⟨184480579804224747162576995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122987053202816498108384663 184480579804224747162576995)
    ·
      refine ⟨276720869706337120743865493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184480579804224747162576995 276720869706337120743865493)
      ·
        refine ⟨12971290767484552534868695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276720869706337120743865493 12971290767484552534868695)
        ·
          refine ⟨19456936151226828802303043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12971290767484552534868695 19456936151226828802303043)
          ·
            refine ⟨29185404226840243203454565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19456936151226828802303043 29185404226840243203454565)
            ·
              refine ⟨5472263292532545600647731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29185404226840243203454565 5472263292532545600647731)
              ·
                refine ⟨8208394938798818400971597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472263292532545600647731 8208394938798818400971597)
                ·
                  refine ⟨3078148102049556900364349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8208394938798818400971597 3078148102049556900364349)
                  ·
                    refine ⟨1154305538268583837636631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3078148102049556900364349 1154305538268583837636631)
                    ·
                      rfl

theorem cell22_3372003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 3].length) (baseStart_3372003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372003 prefixEnd_3372003 := by exact prefixLift 3372003
  have htrace : WordTrace (prefixWord ++ tailWord_3372003) baseStart_3372003 baseEnd_3372003 := by
    simpa [prefixWord, tailWord_3372003, baseEnd_3372003] using wordTrace_append hprefix tailTrace_3372003
  have hstable : (prefixWord ++ tailWord_3372003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372003).length < 2 ^ (prefixWord ++ tailWord_3372003).sum := by decide
  have hdescent : baseEnd_3372003 < baseStart_3372003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372076 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_3372076 : Nat := 118140960795 + 3372076 * 2 ^ 59
def prefixEnd_3372076 : Nat := 4983230072969 + 3 ^ 40 * 3372076 * 2
def baseEnd_3372076 : Nat := 1154330527660435980561407

theorem tailTrace_3372076 : CollatzResearch.WordTrace tailWord_3372076 prefixEnd_3372076 1154330527660435980561407 := by
  unfold tailWord_3372076
  simp only [CollatzResearch.WordTrace]
  refine ⟨61494857865776015787896041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81993143821034687717194721 61494857865776015787896041)
  ·
    refine ⟨46121143399332011840922031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61494857865776015787896041 46121143399332011840922031)
    ·
      refine ⟨69181715098998017761383047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46121143399332011840922031 69181715098998017761383047)
      ·
        refine ⟨103772572648497026642074571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69181715098998017761383047 103772572648497026642074571)
        ·
          refine ⟨155658858972745539963111857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103772572648497026642074571 155658858972745539963111857)
          ·
            refine ⟨116744144229559154972333893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155658858972745539963111857 116744144229559154972333893)
            ·
              refine ⟨21889527043042341557312605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116744144229559154972333893 21889527043042341557312605)
              ·
                refine ⟨8208572641140878083992227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21889527043042341557312605 8208572641140878083992227)
                ·
                  refine ⟨12312858961711317125988341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208572641140878083992227 12312858961711317125988341)
                  ·
                    refine ⟨1154330527660435980561407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12312858961711317125988341 1154330527660435980561407)
                    ·
                      rfl

theorem cell22_3372076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_3372076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372076 prefixEnd_3372076 := by exact prefixLift 3372076
  have htrace : WordTrace (prefixWord ++ tailWord_3372076) baseStart_3372076 baseEnd_3372076 := by
    simpa [prefixWord, tailWord_3372076, baseEnd_3372076] using wordTrace_append hprefix tailTrace_3372076
  have hstable : (prefixWord ++ tailWord_3372076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372076).length < 2 ^ (prefixWord ++ tailWord_3372076).sum := by decide
  have hdescent : baseEnd_3372076 < baseStart_3372076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372093 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_3372093 : Nat := 118140960795 + 3372093 * 2 ^ 59
def prefixEnd_3372093 : Nat := 4983230072969 + 3 ^ 40 * 3372093 * 2
def baseEnd_3372093 : Nat := 1154336347107853602886355

theorem tailTrace_3372093 : CollatzResearch.WordTrace tailWord_3372093 prefixEnd_3372093 1154336347107853602886355 := by
  unfold tailWord_3372093
  simp only [CollatzResearch.WordTrace]
  refine ⟨122990335772490443479160933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81993557181660295652773955 122990335772490443479160933)
  ·
    refine ⟨23060687957341958152342675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122990335772490443479160933 23060687957341958152342675)
    ·
      refine ⟨34591031936012937228514013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23060687957341958152342675 34591031936012937228514013)
      ·
        refine ⟨12971636976004851460692755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34591031936012937228514013 12971636976004851460692755)
        ·
          refine ⟨19457455464007277191039133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12971636976004851460692755 19457455464007277191039133)
          ·
            refine ⟨7296545799002728946639675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19457455464007277191039133 7296545799002728946639675)
            ·
              refine ⟨10944818698504093419959513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296545799002728946639675 10944818698504093419959513)
              ·
                refine ⟨8208614023878070064969635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10944818698504093419959513 8208614023878070064969635)
                ·
                  refine ⟨12312921035817105097454453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208614023878070064969635 12312921035817105097454453)
                  ·
                    refine ⟨1154336347107853602886355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12312921035817105097454453 1154336347107853602886355)
                    ·
                      rfl

theorem cell22_3372093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_3372093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372093 prefixEnd_3372093 := by exact prefixLift 3372093
  have htrace : WordTrace (prefixWord ++ tailWord_3372093) baseStart_3372093 baseEnd_3372093 := by
    simpa [prefixWord, tailWord_3372093, baseEnd_3372093] using wordTrace_append hprefix tailTrace_3372093
  have hstable : (prefixWord ++ tailWord_3372093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372093).length < 2 ^ (prefixWord ++ tailWord_3372093).sum := by decide
  have hdescent : baseEnd_3372093 < baseStart_3372093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372097 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3372097 : Nat := 118140960795 + 3372097 * 2 ^ 59
def prefixEnd_3372097 : Nat := 4983230072969 + 3 ^ 40 * 3372097 * 2
def baseEnd_3372097 : Nat := 1154337716389598925786343

theorem tailTrace_3372097 : CollatzResearch.WordTrace tailWord_3372097 prefixEnd_3372097 1154337716389598925786343 := by
  unfold tailWord_3372097
  simp only [CollatzResearch.WordTrace]
  refine ⟨122990481664475952162306545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81993654442983968108204363 122990481664475952162306545)
  ·
    refine ⟨92242861248356964121729909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122990481664475952162306545 92242861248356964121729909)
    ·
      refine ⟨8647768242033465386412179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92242861248356964121729909 8647768242033465386412179)
      ·
        refine ⟨12971652363050198079618269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8647768242033465386412179 12971652363050198079618269)
        ·
          refine ⟨4864369636143824279856851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12971652363050198079618269 4864369636143824279856851)
          ·
            refine ⟨7296554454215736419785277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864369636143824279856851 7296554454215736419785277)
            ·
              refine ⟨2736207920330901157419479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7296554454215736419785277 2736207920330901157419479)
              ·
                refine ⟨4104311880496351736129219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736207920330901157419479 4104311880496351736129219)
                ·
                  refine ⟨6156467820744527604193829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104311880496351736129219 6156467820744527604193829)
                  ·
                    refine ⟨1154337716389598925786343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6156467820744527604193829 1154337716389598925786343)
                    ·
                      rfl

theorem cell22_3372097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3372097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372097 prefixEnd_3372097 := by exact prefixLift 3372097
  have htrace : WordTrace (prefixWord ++ tailWord_3372097) baseStart_3372097 baseEnd_3372097 := by
    simpa [prefixWord, tailWord_3372097, baseEnd_3372097] using wordTrace_append hprefix tailTrace_3372097
  have hstable : (prefixWord ++ tailWord_3372097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372097).length < 2 ^ (prefixWord ++ tailWord_3372097).sum := by decide
  have hdescent : baseEnd_3372097 < baseStart_3372097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372110 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_3372110 : Nat := 118140960795 + 3372110 * 2 ^ 59
def prefixEnd_3372110 : Nat := 4983230072969 + 3 ^ 40 * 3372110 * 2
def baseEnd_3372110 : Nat := 1154342166555271225211303

theorem tailTrace_3372110 : CollatzResearch.WordTrace tailWord_3372110 prefixEnd_3372110 1154342166555271225211303 := by
  unfold tailWord_3372110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15373869476678606922816223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81993970542285903588353189 15373869476678606922816223)
  ·
    refine ⟨23060804215017910384224335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15373869476678606922816223 23060804215017910384224335)
    ·
      refine ⟨34591206322526865576336503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23060804215017910384224335 34591206322526865576336503)
      ·
        refine ⟨51886809483790298364504755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34591206322526865576336503 51886809483790298364504755)
        ·
          refine ⟨77830214225685447546757133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51886809483790298364504755 77830214225685447546757133)
          ·
            refine ⟨29186330334632042830033925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77830214225685447546757133 29186330334632042830033925)
            ·
              refine ⟨5472436937743508030631361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29186330334632042830033925 5472436937743508030631361)
              ·
                refine ⟨4104327703307631022973521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5472436937743508030631361 4104327703307631022973521)
                ·
                  refine ⟨3078245777480723267230141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4104327703307631022973521 3078245777480723267230141)
                  ·
                    refine ⟨1154342166555271225211303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3078245777480723267230141 1154342166555271225211303)
                    ·
                      rfl

theorem cell22_3372110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_3372110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372110 prefixEnd_3372110 := by exact prefixLift 3372110
  have htrace : WordTrace (prefixWord ++ tailWord_3372110) baseStart_3372110 baseEnd_3372110 := by
    simpa [prefixWord, tailWord_3372110, baseEnd_3372110] using wordTrace_append hprefix tailTrace_3372110
  have hstable : (prefixWord ++ tailWord_3372110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372110).length < 2 ^ (prefixWord ++ tailWord_3372110).sum := by decide
  have hdescent : baseEnd_3372110 < baseStart_3372110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372151 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 7]
def baseStart_3372151 : Nat := 118140960795 + 3372151 * 2 ^ 59
def prefixEnd_3372151 : Nat := 4983230072969 + 3 ^ 40 * 3372151 * 2
def baseEnd_3372151 : Nat := 384785400564386928312059

theorem tailTrace_3372151 : CollatzResearch.WordTrace tailWord_3372151 prefixEnd_3372151 384785400564386928312059 := by
  unfold tailWord_3372151
  simp only [CollatzResearch.WordTrace]
  refine ⟨122992451206280319384772307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81994967470853546256514871 122992451206280319384772307)
  ·
    refine ⟨184488676809420479077158461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122992451206280319384772307 184488676809420479077158461)
    ·
      refine ⟨69183253803532679653934423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184488676809420479077158461 69183253803532679653934423)
      ·
        refine ⟨103774880705299019480901635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69183253803532679653934423 103774880705299019480901635)
        ·
          refine ⟨155662321057948529221352453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103774880705299019480901635 155662321057948529221352453)
          ·
            refine ⟨29186685198365349229003585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155662321057948529221352453 29186685198365349229003585)
            ·
              refine ⟨21890013898774011921752689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29186685198365349229003585 21890013898774011921752689)
              ·
                refine ⟨16417510424080508941314517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21890013898774011921752689 16417510424080508941314517)
                ·
                  refine ⟨384785400564386928312059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16417510424080508941314517 384785400564386928312059)
                  ·
                    rfl

theorem cell22_3372151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_3372151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372151 prefixEnd_3372151 := by exact prefixLift 3372151
  have htrace : WordTrace (prefixWord ++ tailWord_3372151) baseStart_3372151 baseEnd_3372151 := by
    simpa [prefixWord, tailWord_3372151, baseEnd_3372151] using wordTrace_append hprefix tailTrace_3372151
  have hstable : (prefixWord ++ tailWord_3372151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372151).length < 2 ^ (prefixWord ++ tailWord_3372151).sum := by decide
  have hdescent : baseEnd_3372151 < baseStart_3372151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372181 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3372181 : Nat := 118140960795 + 3372181 * 2 ^ 59
def prefixEnd_3372181 : Nat := 4983230072969 + 3 ^ 40 * 3372181 * 2
def baseEnd_3372181 : Nat := 1154366471306250706686085

theorem tailTrace_3372181 : CollatzResearch.WordTrace tailWord_3372181 prefixEnd_3372181 1154366471306250706686085 := by
  unfold tailWord_3372181
  simp only [CollatzResearch.WordTrace]
  refine ⟨122993545396171634508364397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81995696930781089672242931 122993545396171634508364397)
  ·
    refine ⟨46122579523564362940636649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122993545396171634508364397 46122579523564362940636649)
    ·
      refine ⟨34591934642673272205477487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46122579523564362940636649 34591934642673272205477487)
      ·
        refine ⟨51887901964009908308216231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34591934642673272205477487 51887901964009908308216231)
        ·
          refine ⟨77831852946014862462324347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51887901964009908308216231 77831852946014862462324347)
          ·
            refine ⟨116747779419022293693486521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77831852946014862462324347 116747779419022293693486521)
            ·
              refine ⟨87560834564266720270114891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116747779419022293693486521 87560834564266720270114891)
              ·
                refine ⟨131341251846400080405172337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87560834564266720270114891 131341251846400080405172337)
                ·
                  refine ⟨98505938884800060303879253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131341251846400080405172337 98505938884800060303879253)
                  ·
                    refine ⟨1154366471306250706686085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98505938884800060303879253 1154366471306250706686085)
                    ·
                      rfl

theorem cell22_3372181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3372181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372181 prefixEnd_3372181 := by exact prefixLift 3372181
  have htrace : WordTrace (prefixWord ++ tailWord_3372181) baseStart_3372181 baseEnd_3372181 := by
    simpa [prefixWord, tailWord_3372181, baseEnd_3372181] using wordTrace_append hprefix tailTrace_3372181
  have hstable : (prefixWord ++ tailWord_3372181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372181).length < 2 ^ (prefixWord ++ tailWord_3372181).sum := by decide
  have hdescent : baseEnd_3372181 < baseStart_3372181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372183 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3372183 : Nat := 118140960795 + 3372183 * 2 ^ 59
def prefixEnd_3372183 : Nat := 4983230072969 + 3 ^ 40 * 3372183 * 2
def baseEnd_3372183 : Nat := 1154367155947123368136079

theorem tailTrace_3372183 : CollatzResearch.WordTrace tailWord_3372183 prefixEnd_3372183 1154367155947123368136079 := by
  unfold tailWord_3372183
  simp only [CollatzResearch.WordTrace]
  refine ⟨122993618342164388849937203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81995745561442925899958135 122993618342164388849937203)
  ·
    refine ⟨184490427513246583274905805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122993618342164388849937203 184490427513246583274905805)
    ·
      refine ⟨69183910317467468728089677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184490427513246583274905805 69183910317467468728089677)
      ·
        refine ⟨25943966369050300773033629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69183910317467468728089677 25943966369050300773033629)
        ·
          refine ⟨9728987388393862789887611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25943966369050300773033629 9728987388393862789887611)
          ·
            refine ⟨14593481082590794184831417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728987388393862789887611 14593481082590794184831417)
            ·
              refine ⟨10945110811943095638623563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14593481082590794184831417 10945110811943095638623563)
              ·
                refine ⟨16417666217914643457935345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945110811943095638623563 16417666217914643457935345)
                ·
                  refine ⟨12313249663435982593451509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16417666217914643457935345 12313249663435982593451509)
                  ·
                    refine ⟨1154367155947123368136079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12313249663435982593451509 1154367155947123368136079)
                    ·
                      rfl

theorem cell22_3372183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3372183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372183 prefixEnd_3372183 := by exact prefixLift 3372183
  have htrace : WordTrace (prefixWord ++ tailWord_3372183) baseStart_3372183 baseEnd_3372183 := by
    simpa [prefixWord, tailWord_3372183, baseEnd_3372183] using wordTrace_append hprefix tailTrace_3372183
  have hstable : (prefixWord ++ tailWord_3372183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372183).length < 2 ^ (prefixWord ++ tailWord_3372183).sum := by decide
  have hdescent : baseEnd_3372183 < baseStart_3372183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372324 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_3372324 : Nat := 118140960795 + 3372324 * 2 ^ 59
def prefixEnd_3372324 : Nat := 4983230072969 + 3 ^ 40 * 3372324 * 2
def baseEnd_3372324 : Nat := 1154415423128646000360647

theorem tailTrace_3372324 : CollatzResearch.WordTrace tailWord_3372324 prefixEnd_3372324 1154415423128646000360647 := by
  unfold tailWord_3372324
  simp only [CollatzResearch.WordTrace]
  refine ⟨61499380517326784965410013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81999174023102379953880017 61499380517326784965410013)
  ·
    refine ⟨23062267693997544362028755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61499380517326784965410013 23062267693997544362028755)
    ·
      refine ⟨34593401540996316543043133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23062267693997544362028755 34593401540996316543043133)
      ·
        refine ⟨12972525577873618703641175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34593401540996316543043133 12972525577873618703641175)
        ·
          refine ⟨19458788366810428055461763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12972525577873618703641175 19458788366810428055461763)
          ·
            refine ⟨29188182550215642083192645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19458788366810428055461763 29188182550215642083192645)
            ·
              refine ⟨5472784228165432890598621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29188182550215642083192645 5472784228165432890598621)
              ·
                refine ⟨2052294085562037333974483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5472784228165432890598621 2052294085562037333974483)
                ·
                  refine ⟨3078441128343056000961725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052294085562037333974483 3078441128343056000961725)
                  ·
                    refine ⟨1154415423128646000360647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3078441128343056000961725 1154415423128646000360647)
                    ·
                      rfl

theorem cell22_3372324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_3372324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372324 prefixEnd_3372324 := by exact prefixLift 3372324
  have htrace : WordTrace (prefixWord ++ tailWord_3372324) baseStart_3372324 baseEnd_3372324 := by
    simpa [prefixWord, tailWord_3372324, baseEnd_3372324] using wordTrace_append hprefix tailTrace_3372324
  have hstable : (prefixWord ++ tailWord_3372324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372324).length < 2 ^ (prefixWord ++ tailWord_3372324).sum := by decide
  have hdescent : baseEnd_3372324 < baseStart_3372324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372337 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 5]
def baseStart_3372337 : Nat := 118140960795 + 3372337 * 2 ^ 59
def prefixEnd_3372337 : Nat := 4983230072969 + 3 ^ 40 * 3372337 * 2
def baseEnd_3372337 : Nat := 384806624431439433261869

theorem tailTrace_3372337 : CollatzResearch.WordTrace tailWord_3372337 prefixEnd_3372337 384806624431439433261869 := by
  unfold tailWord_3372337
  simp only [CollatzResearch.WordTrace]
  refine ⟨122999235183606473151043265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81999490122404315434028843 122999235183606473151043265)
  ·
    refine ⟨92249426387704854863282449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122999235183606473151043265 92249426387704854863282449)
    ·
      refine ⟨69187069790778641147461837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92249426387704854863282449 69187069790778641147461837)
      ·
        refine ⟨25945151171541990430298189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69187069790778641147461837 25945151171541990430298189)
        ·
          refine ⟨9729431689328246411361821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25945151171541990430298189 9729431689328246411361821)
          ·
            refine ⟨3648536883498092404260683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9729431689328246411361821 3648536883498092404260683)
            ·
              refine ⟨5472805325247138606391025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648536883498092404260683 5472805325247138606391025)
              ·
                refine ⟨4104603993935353954793269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5472805325247138606391025 4104603993935353954793269)
                ·
                  refine ⟨384806624431439433261869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4104603993935353954793269 384806624431439433261869)
                  ·
                    rfl

theorem cell22_3372337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_3372337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372337 prefixEnd_3372337 := by exact prefixLift 3372337
  have htrace : WordTrace (prefixWord ++ tailWord_3372337) baseStart_3372337 baseEnd_3372337 := by
    simpa [prefixWord, tailWord_3372337, baseEnd_3372337] using wordTrace_append hprefix tailTrace_3372337
  have hstable : (prefixWord ++ tailWord_3372337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372337).length < 2 ^ (prefixWord ++ tailWord_3372337).sum := by decide
  have hdescent : baseEnd_3372337 < baseStart_3372337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372397 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_3372397 : Nat := 118140960795 + 3372397 * 2 ^ 59
def prefixEnd_3372397 : Nat := 4983230072969 + 3 ^ 40 * 3372397 * 2
def baseEnd_3372397 : Nat := 1154440412520498143285423

theorem tailTrace_3372397 : CollatzResearch.WordTrace tailWord_3372397 prefixEnd_3372397 1154440412520498143285423 := by
  unfold tailWord_3372397
  simp only [CollatzResearch.WordTrace]
  refine ⟨123001423563389103398227445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82000949042259402265484963 123001423563389103398227445)
  ·
    refine ⟨11531383459067728443583823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123001423563389103398227445 11531383459067728443583823)
    ·
      refine ⟨17297075188601592665375735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11531383459067728443583823 17297075188601592665375735)
      ·
        refine ⟨25945612782902388998063603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17297075188601592665375735 25945612782902388998063603)
        ·
          refine ⟨38918419174353583497095405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25945612782902388998063603 38918419174353583497095405)
          ·
            refine ⟨14594407190382593811410777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38918419174353583497095405 14594407190382593811410777)
            ·
              refine ⟨10945805392786945358558083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14594407190382593811410777 10945805392786945358558083)
              ·
                refine ⟨16418708089180418037837125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945805392786945358558083 16418708089180418037837125)
                ·
                  refine ⟨3078507766721328382094461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16418708089180418037837125 3078507766721328382094461)
                  ·
                    refine ⟨1154440412520498143285423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3078507766721328382094461 1154440412520498143285423)
                    ·
                      rfl

theorem cell22_3372397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_3372397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372397 prefixEnd_3372397 := by exact prefixLift 3372397
  have htrace : WordTrace (prefixWord ++ tailWord_3372397) baseStart_3372397 baseEnd_3372397 := by
    simpa [prefixWord, tailWord_3372397, baseEnd_3372397] using wordTrace_append hprefix tailTrace_3372397
  have hstable : (prefixWord ++ tailWord_3372397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372397).length < 2 ^ (prefixWord ++ tailWord_3372397).sum := by decide
  have hdescent : baseEnd_3372397 < baseStart_3372397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372517 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 6]
def baseStart_3372517 : Nat := 118140960795 + 3372517 * 2 ^ 59
def prefixEnd_3372517 : Nat := 4983230072969 + 3 ^ 40 * 3372517 * 2
def baseEnd_3372517 : Nat := 384827163657619276761685

theorem tailTrace_3372517 : CollatzResearch.WordTrace tailWord_3372517 prefixEnd_3372517 384827163657619276761685 := by
  unfold tailWord_3372517
  simp only [CollatzResearch.WordTrace]
  refine ⟨123005800322954363892595805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82003866881969575928397203 123005800322954363892595805)
  ·
    refine ⟨46127175121107886459723427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123005800322954363892595805 46127175121107886459723427)
    ·
      refine ⟨69190762681661829689585141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46127175121107886459723427 69190762681661829689585141)
      ·
        refine ⟨6486634001405796533398607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69190762681661829689585141 6486634001405796533398607)
        ·
          refine ⟨9729951002108694800097911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486634001405796533398607 9729951002108694800097911)
          ·
            refine ⟨14594926503163042200146867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729951002108694800097911 14594926503163042200146867)
            ·
              refine ⟨21892389754744563300220301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14594926503163042200146867 21892389754744563300220301)
              ·
                refine ⟨8209646158029211237582613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21892389754744563300220301 8209646158029211237582613)
                ·
                  refine ⟨384827163657619276761685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8209646158029211237582613 384827163657619276761685)
                  ·
                    rfl

theorem cell22_3372517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_3372517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372517 prefixEnd_3372517 := by exact prefixLift 3372517
  have htrace : WordTrace (prefixWord ++ tailWord_3372517) baseStart_3372517 baseEnd_3372517 := by
    simpa [prefixWord, tailWord_3372517, baseEnd_3372517] using wordTrace_append hprefix tailTrace_3372517
  have hstable : (prefixWord ++ tailWord_3372517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372517).length < 2 ^ (prefixWord ++ tailWord_3372517).sum := by decide
  have hdescent : baseEnd_3372517 < baseStart_3372517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372551 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 4]
def baseStart_3372551 : Nat := 118140960795 + 3372551 * 2 ^ 59
def prefixEnd_3372551 : Nat := 4983230072969 + 3 ^ 40 * 3372551 * 2
def baseEnd_3372551 : Nat := 384831043289231024978317

theorem tailTrace_3372551 : CollatzResearch.WordTrace tailWord_3372551 prefixEnd_3372551 384831043289231024978317 := by
  unfold tailWord_3372551
  simp only [CollatzResearch.WordTrace]
  refine ⟨123007040404831187699333507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82004693603220791799555671 123007040404831187699333507)
  ·
    refine ⟨184510560607246781549000261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123007040404831187699333507 184510560607246781549000261)
    ·
      refine ⟨34595730113858771540437549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184510560607246781549000261 34595730113858771540437549)
      ·
        refine ⟨12973398792697039327664081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34595730113858771540437549 12973398792697039327664081)
        ·
          refine ⟨9730049094522779495748061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12973398792697039327664081 9730049094522779495748061)
          ·
            refine ⟨3648768410446042310905523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9730049094522779495748061 3648768410446042310905523)
            ·
              refine ⟨5473152615669063466358285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648768410446042310905523 5473152615669063466358285)
              ·
                refine ⟨2052432230875898799884357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5473152615669063466358285 2052432230875898799884357)
                ·
                  refine ⟨384831043289231024978317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2052432230875898799884357 384831043289231024978317)
                  ·
                    rfl

theorem cell22_3372551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 4].length) (baseStart_3372551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372551 prefixEnd_3372551 := by exact prefixLift 3372551
  have htrace : WordTrace (prefixWord ++ tailWord_3372551) baseStart_3372551 baseEnd_3372551 := by
    simpa [prefixWord, tailWord_3372551, baseEnd_3372551] using wordTrace_append hprefix tailTrace_3372551
  have hstable : (prefixWord ++ tailWord_3372551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372551).length < 2 ^ (prefixWord ++ tailWord_3372551).sum := by decide
  have hdescent : baseEnd_3372551 < baseStart_3372551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372622 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3372622 : Nat := 118140960795 + 3372622 * 2 ^ 59
def prefixEnd_3372622 : Nat := 4983230072969 + 3 ^ 40 * 3372622 * 2
def baseEnd_3372622 : Nat := 1154517434618672556409733

theorem tailTrace_3372622 : CollatzResearch.WordTrace tailWord_3372622 prefixEnd_3372622 1154517434618672556409733 := by
  unfold tailWord_3372622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376203748446745853146015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82006419991715977883445413 15376203748446745853146015)
  ·
    refine ⟨23064305622670118779719023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15376203748446745853146015 23064305622670118779719023)
    ·
      refine ⟨34596458434005178169578535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23064305622670118779719023 34596458434005178169578535)
      ·
        refine ⟨51894687651007767254367803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34596458434005178169578535 51894687651007767254367803)
        ·
          refine ⟨77842031476511650881551705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51894687651007767254367803 77842031476511650881551705)
          ·
            refine ⟨58381523607383738161163779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77842031476511650881551705 58381523607383738161163779)
            ·
              refine ⟨87572285411075607241745669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58381523607383738161163779 87572285411075607241745669)
              ·
                refine ⟨16419803514576676357827313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87572285411075607241745669 16419803514576676357827313)
                ·
                  refine ⟨12314852635932507268370485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16419803514576676357827313 12314852635932507268370485)
                  ·
                    refine ⟨1154517434618672556409733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12314852635932507268370485 1154517434618672556409733)
                    ·
                      rfl

theorem cell22_3372622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3372622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372622 prefixEnd_3372622 := by exact prefixLift 3372622
  have htrace : WordTrace (prefixWord ++ tailWord_3372622) baseStart_3372622 baseEnd_3372622 := by
    simpa [prefixWord, tailWord_3372622, baseEnd_3372622] using wordTrace_append hprefix tailTrace_3372622
  have hstable : (prefixWord ++ tailWord_3372622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372622).length < 2 ^ (prefixWord ++ tailWord_3372622).sum := by decide
  have hdescent : baseEnd_3372622 < baseStart_3372622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372630 : List Nat := [5, 2, 2, 2, 2, 1, 1, 7]
def baseStart_3372630 : Nat := 118140960795 + 3372630 * 2 ^ 59
def prefixEnd_3372630 : Nat := 4983230072969 + 3 ^ 40 * 3372630 * 2
def baseEnd_3372630 : Nat := 128280019242462578023301

theorem tailTrace_3372630 : CollatzResearch.WordTrace tailWord_3372630 prefixEnd_3372630 128280019242462578023301 := by
  unfold tailWord_3372630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688120110721561511966209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82006614514363322794306229 7688120110721561511966209)
  ·
    refine ⟨5766090083041171133974657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7688120110721561511966209 5766090083041171133974657)
    ·
      refine ⟨4324567562280878350480993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5766090083041171133974657 4324567562280878350480993)
      ·
        refine ⟨3243425671710658762860745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324567562280878350480993 3243425671710658762860745)
        ·
          refine ⟨2432569253782994072145559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243425671710658762860745 2432569253782994072145559)
          ·
            refine ⟨3648853880674491108218339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432569253782994072145559 3648853880674491108218339)
            ·
              refine ⟨5473280821011736662327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648853880674491108218339 5473280821011736662327509)
              ·
                refine ⟨128280019242462578023301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5473280821011736662327509 128280019242462578023301)
                ·
                  rfl

theorem cell22_3372630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_3372630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372630 prefixEnd_3372630 := by exact prefixLift 3372630
  have htrace : WordTrace (prefixWord ++ tailWord_3372630) baseStart_3372630 baseEnd_3372630 := by
    simpa [prefixWord, tailWord_3372630, baseEnd_3372630] using wordTrace_append hprefix tailTrace_3372630
  have hstable : (prefixWord ++ tailWord_3372630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372630).length < 2 ^ (prefixWord ++ tailWord_3372630).sum := by decide
  have hdescent : baseEnd_3372630 < baseStart_3372630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372667 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 1, 5]
def baseStart_3372667 : Nat := 118140960795 + 3372667 * 2 ^ 59
def prefixEnd_3372667 : Nat := 4983230072969 + 3 ^ 40 * 3372667 * 2
def baseEnd_3372667 : Nat := 1154532839038307439034595

theorem tailTrace_3372667 : CollatzResearch.WordTrace tailWord_3372667 prefixEnd_3372667 1154532839038307439034595 := by
  unfold tailWord_3372667
  simp only [CollatzResearch.WordTrace]
  refine ⟨123011271272410939510556255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82007514181607293007037503 123011271272410939510556255)
  ·
    refine ⟨184516906908616409265834383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123011271272410939510556255 184516906908616409265834383)
    ·
      refine ⟨276775360362924613898751575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184516906908616409265834383 276775360362924613898751575)
      ·
        refine ⟨415163040544386920848127363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276775360362924613898751575 415163040544386920848127363)
        ·
          refine ⟨622744560816580381272191045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415163040544386920848127363 622744560816580381272191045)
          ·
            refine ⟨116764605153108821488535821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 622744560816580381272191045 116764605153108821488535821)
            ·
              refine ⟨43786726932415808058200933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116764605153108821488535821 43786726932415808058200933)
              ·
                refine ⟨8210011299827964010912675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43786726932415808058200933 8210011299827964010912675)
                ·
                  refine ⟨12315016949741946016369013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210011299827964010912675 12315016949741946016369013)
                  ·
                    refine ⟨1154532839038307439034595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12315016949741946016369013 1154532839038307439034595)
                    ·
                      rfl

theorem cell22_3372667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_3372667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372667 prefixEnd_3372667 := by exact prefixLift 3372667
  have htrace : WordTrace (prefixWord ++ tailWord_3372667) baseStart_3372667 baseEnd_3372667 := by
    simpa [prefixWord, tailWord_3372667, baseEnd_3372667] using wordTrace_append hprefix tailTrace_3372667
  have hstable : (prefixWord ++ tailWord_3372667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372667).length < 2 ^ (prefixWord ++ tailWord_3372667).sum := by decide
  have hdescent : baseEnd_3372667 < baseStart_3372667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372684 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_3372684 : Nat := 118140960795 + 3372684 * 2 ^ 59
def prefixEnd_3372684 : Nat := 4983230072969 + 3 ^ 40 * 3372684 * 2
def baseEnd_3372684 : Nat := 1154538658485725061359543

theorem tailTrace_3372684 : CollatzResearch.WordTrace tailWord_3372684 prefixEnd_3372684 1154538658485725061359543 := by
  unfold tailWord_3372684
  simp only [CollatzResearch.WordTrace]
  refine ⟨61505945656674675706962553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82007927542232900942616737 61505945656674675706962553)
  ·
    refine ⟨46129459242506006780221915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61505945656674675706962553 46129459242506006780221915)
    ·
      refine ⟨69194188863759010170332873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46129459242506006780221915 69194188863759010170332873)
      ·
        refine ⟨51895641647819257627749655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69194188863759010170332873 51895641647819257627749655)
        ·
          refine ⟨77843462471728886441624483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51895641647819257627749655 77843462471728886441624483)
          ·
            refine ⟨116765193707593329662436725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77843462471728886441624483 116765193707593329662436725)
            ·
              refine ⟨10946736910086874655853443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116765193707593329662436725 10946736910086874655853443)
              ·
                refine ⟨16420105365130311983780165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10946736910086874655853443 16420105365130311983780165)
                ·
                  refine ⟨3078769755961933496958781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16420105365130311983780165 3078769755961933496958781)
                  ·
                    refine ⟨1154538658485725061359543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3078769755961933496958781 1154538658485725061359543)
                    ·
                      rfl

theorem cell22_3372684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_3372684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372684 prefixEnd_3372684 := by exact prefixLift 3372684
  have htrace : WordTrace (prefixWord ++ tailWord_3372684) baseStart_3372684 baseEnd_3372684 := by
    simpa [prefixWord, tailWord_3372684, baseEnd_3372684] using wordTrace_append hprefix tailTrace_3372684
  have hstable : (prefixWord ++ tailWord_3372684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372684).length < 2 ^ (prefixWord ++ tailWord_3372684).sum := by decide
  have hdescent : baseEnd_3372684 < baseStart_3372684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372686 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_3372686 : Nat := 118140960795 + 3372686 * 2 ^ 59
def prefixEnd_3372686 : Nat := 4983230072969 + 3 ^ 40 * 3372686 * 2
def baseEnd_3372686 : Nat := 384846447708865907603179

theorem tailTrace_3372686 : CollatzResearch.WordTrace tailWord_3372686 prefixEnd_3372686 384846447708865907603179 := by
  unfold tailWord_3372686
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376495532417763219437239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82007976172894737170331941 15376495532417763219437239)
  ·
    refine ⟨23064743298626644829155859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15376495532417763219437239 23064743298626644829155859)
    ·
      refine ⟨34597114947939967243733789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23064743298626644829155859 34597114947939967243733789)
      ·
        refine ⟨12973918105477487716400171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34597114947939967243733789 12973918105477487716400171)
        ·
          refine ⟨19460877158216231574600257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973918105477487716400171 19460877158216231574600257)
          ·
            refine ⟨14595657868662173680950193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19460877158216231574600257 14595657868662173680950193)
            ·
              refine ⟨10946743401496630260712645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14595657868662173680950193 10946743401496630260712645)
              ·
                refine ⟨2052514387780618173883621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10946743401496630260712645 2052514387780618173883621)
                ·
                  refine ⟨384846447708865907603179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2052514387780618173883621 384846447708865907603179)
                  ·
                    rfl

theorem cell22_3372686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_3372686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372686 prefixEnd_3372686 := by exact prefixLift 3372686
  have htrace : WordTrace (prefixWord ++ tailWord_3372686) baseStart_3372686 baseEnd_3372686 := by
    simpa [prefixWord, tailWord_3372686, baseEnd_3372686] using wordTrace_append hprefix tailTrace_3372686
  have hstable : (prefixWord ++ tailWord_3372686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372686).length < 2 ^ (prefixWord ++ tailWord_3372686).sum := by decide
  have hdescent : baseEnd_3372686 < baseStart_3372686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372729 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_3372729 : Nat := 118140960795 + 3372729 * 2 ^ 59
def prefixEnd_3372729 : Nat := 4983230072969 + 3 ^ 40 * 3372729 * 2
def baseEnd_3372729 : Nat := 1154554062905359943984405

theorem tailTrace_3372729 : CollatzResearch.WordTrace tailWord_3372729 prefixEnd_3372729 1154554062905359943984405 := by
  unfold tailWord_3372729
  simp only [CollatzResearch.WordTrace]
  refine ⟨123013532598186324099313241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82009021732124216066208827 123013532598186324099313241)
  ·
    refine ⟨92260149448639743074484931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123013532598186324099313241 92260149448639743074484931)
    ·
      refine ⟨138390224172959614611727397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92260149448639743074484931 138390224172959614611727397)
      ·
        refine ⟨25948167032429927739698887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138390224172959614611727397 25948167032429927739698887)
        ·
          refine ⟨38922250548644891609548331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25948167032429927739698887 38922250548644891609548331)
          ·
            refine ⟨58383375822967337414322497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38922250548644891609548331 58383375822967337414322497)
            ·
              refine ⟨43787531867225503060741873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58383375822967337414322497 43787531867225503060741873)
              ·
                refine ⟨32840648900419127295556405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43787531867225503060741873 32840648900419127295556405)
                ·
                  refine ⟨3078810834414293183958413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32840648900419127295556405 3078810834414293183958413)
                  ·
                    refine ⟨1154554062905359943984405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3078810834414293183958413 1154554062905359943984405)
                    ·
                      rfl

theorem cell22_3372729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_3372729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372729 prefixEnd_3372729 := by exact prefixLift 3372729
  have htrace : WordTrace (prefixWord ++ tailWord_3372729) baseStart_3372729 baseEnd_3372729 := by
    simpa [prefixWord, tailWord_3372729, baseEnd_3372729] using wordTrace_append hprefix tailTrace_3372729
  have hstable : (prefixWord ++ tailWord_3372729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372729).length < 2 ^ (prefixWord ++ tailWord_3372729).sum := by decide
  have hdescent : baseEnd_3372729 < baseStart_3372729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372759 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 5]
def baseStart_3372759 : Nat := 118140960795 + 3372759 * 2 ^ 59
def prefixEnd_3372759 : Nat := 4983230072969 + 3 ^ 40 * 3372759 * 2
def baseEnd_3372759 : Nat := 384854777506149955244771

theorem tailTrace_3372759 : CollatzResearch.WordTrace tailWord_3372759 prefixEnd_3372759 384854777506149955244771 := by
  unfold tailWord_3372759
  simp only [CollatzResearch.WordTrace]
  refine ⟨123014626788077639222905331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82009751192051759481936887 123014626788077639222905331)
  ·
    refine ⟨184521940182116458834357997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123014626788077639222905331 184521940182116458834357997)
    ·
      refine ⟨69195727568293672062884249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184521940182116458834357997 69195727568293672062884249)
      ·
        refine ⟨51896795676220254047163187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69195727568293672062884249 51896795676220254047163187)
        ·
          refine ⟨77845193514330381070744781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51896795676220254047163187 77845193514330381070744781)
          ·
            refine ⟨29191947567873892901529293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77845193514330381070744781 29191947567873892901529293)
            ·
              refine ⟨10946980337952709838073485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29191947567873892901529293 10946980337952709838073485)
              ·
                refine ⟨4105117626732266189277557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10946980337952709838073485 4105117626732266189277557)
                ·
                  refine ⟨384854777506149955244771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105117626732266189277557 384854777506149955244771)
                  ·
                    rfl

theorem cell22_3372759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 5].length) (baseStart_3372759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372759 prefixEnd_3372759 := by exact prefixLift 3372759
  have htrace : WordTrace (prefixWord ++ tailWord_3372759) baseStart_3372759 baseEnd_3372759 := by
    simpa [prefixWord, tailWord_3372759, baseEnd_3372759] using wordTrace_append hprefix tailTrace_3372759
  have hstable : (prefixWord ++ tailWord_3372759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372759).length < 2 ^ (prefixWord ++ tailWord_3372759).sum := by decide
  have hdescent : baseEnd_3372759 < baseStart_3372759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372836 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_3372836 : Nat := 118140960795 + 3372836 * 2 ^ 59
def prefixEnd_3372836 : Nat := 4983230072969 + 3 ^ 40 * 3372836 * 2
def baseEnd_3372836 : Nat := 1154590691192047331559077

theorem tailTrace_3372836 : CollatzResearch.WordTrace tailWord_3372836 prefixEnd_3372836 1154590691192047331559077 := by
  unfold tailWord_3372836
  simp only [CollatzResearch.WordTrace]
  refine ⟨61508717604399340686729181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82011623472532454248972241 61508717604399340686729181)
  ·
    refine ⟨23065769101649752757523443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61508717604399340686729181 23065769101649752757523443)
    ·
      refine ⟨34598653652474629136285165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23065769101649752757523443 34598653652474629136285165)
      ·
        refine ⟨12974495119677985926106937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34598653652474629136285165 12974495119677985926106937)
        ·
          refine ⟨9730871339758489444580203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12974495119677985926106937 9730871339758489444580203)
          ·
            refine ⟨14596307009637734166870305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9730871339758489444580203 14596307009637734166870305)
            ·
              refine ⟨10947230257228300625152729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14596307009637734166870305 10947230257228300625152729)
              ·
                refine ⟨8210422692921225468864547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10947230257228300625152729 8210422692921225468864547)
                ·
                  refine ⟨12315634039381838203296821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210422692921225468864547 12315634039381838203296821)
                  ·
                    refine ⟨1154590691192047331559077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12315634039381838203296821 1154590691192047331559077)
                    ·
                      rfl

theorem cell22_3372836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_3372836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372836 prefixEnd_3372836 := by exact prefixLift 3372836
  have htrace : WordTrace (prefixWord ++ tailWord_3372836) baseStart_3372836 baseEnd_3372836 := by
    simpa [prefixWord, tailWord_3372836, baseEnd_3372836] using wordTrace_append hprefix tailTrace_3372836
  have hstable : (prefixWord ++ tailWord_3372836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372836).length < 2 ^ (prefixWord ++ tailWord_3372836).sum := by decide
  have hdescent : baseEnd_3372836 < baseStart_3372836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372840 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3372840 : Nat := 118140960795 + 3372840 * 2 ^ 59
def prefixEnd_3372840 : Nat := 4983230072969 + 3 ^ 40 * 3372840 * 2
def baseEnd_3372840 : Nat := 1154592060473792654459065

theorem tailTrace_3372840 : CollatzResearch.WordTrace tailWord_3372840 prefixEnd_3372840 1154592060473792654459065 := by
  unfold tailWord_3372840
  simp only [CollatzResearch.WordTrace]
  refine ⟨61508790550392095028301987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82011720733856126704402649 61508790550392095028301987)
  ·
    refine ⟨92263185825588142542452981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61508790550392095028301987 92263185825588142542452981)
    ·
      refine ⟨8649673671148888363354967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92263185825588142542452981 8649673671148888363354967)
      ·
        refine ⟨12974510506723332545032451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8649673671148888363354967 12974510506723332545032451)
        ·
          refine ⟨19461765760084998817548677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12974510506723332545032451 19461765760084998817548677)
          ·
            refine ⟨3649081080015937278290377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19461765760084998817548677 3649081080015937278290377)
            ·
              refine ⟨2736810810011952958717783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3649081080015937278290377 2736810810011952958717783)
              ·
                refine ⟨4105216215017929438076675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736810810011952958717783 4105216215017929438076675)
                ·
                  refine ⟨6157824322526894157115013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105216215017929438076675 6157824322526894157115013)
                  ·
                    refine ⟨1154592060473792654459065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6157824322526894157115013 1154592060473792654459065)
                    ·
                      rfl

theorem cell22_3372840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3372840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372840 prefixEnd_3372840 := by exact prefixLift 3372840
  have htrace : WordTrace (prefixWord ++ tailWord_3372840) baseStart_3372840 baseEnd_3372840 := by
    simpa [prefixWord, tailWord_3372840, baseEnd_3372840] using wordTrace_append hprefix tailTrace_3372840
  have hstable : (prefixWord ++ tailWord_3372840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372840).length < 2 ^ (prefixWord ++ tailWord_3372840).sum := by decide
  have hdescent : baseEnd_3372840 < baseStart_3372840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372849 : List Nat := [1, 2, 2, 3, 2, 3, 9]
def baseStart_3372849 : Nat := 118140960795 + 3372849 * 2 ^ 59
def prefixEnd_3372849 : Nat := 4983230072969 + 3 ^ 40 * 3372849 * 2
def baseEnd_3372849 : Nat := 42762783013248875221631

theorem tailTrace_3372849 : CollatzResearch.WordTrace tailWord_3372849 prefixEnd_3372849 42762783013248875221631 := by
  unfold tailWord_3372849
  simp only [CollatzResearch.WordTrace]
  refine ⟨123017909357751584593681601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82011939571834389729121067 123017909357751584593681601)
  ·
    refine ⟨92263432018313688445261201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123017909357751584593681601 92263432018313688445261201)
    ·
      refine ⟨69197574013735266333945901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92263432018313688445261201 69197574013735266333945901)
      ·
        refine ⟨25949090255150724875229713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69197574013735266333945901 25949090255150724875229713)
        ·
          refine ⟨19461817691363043656422285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25949090255150724875229713 19461817691363043656422285)
          ·
            refine ⟨7298181634261141371158357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19461817691363043656422285 7298181634261141371158357)
            ·
              refine ⟨42762783013248875221631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7298181634261141371158357 42762783013248875221631)
              ·
                rfl

theorem cell22_3372849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 9].length) (baseStart_3372849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372849 prefixEnd_3372849 := by exact prefixLift 3372849
  have htrace : WordTrace (prefixWord ++ tailWord_3372849) baseStart_3372849 baseEnd_3372849 := by
    simpa [prefixWord, tailWord_3372849, baseEnd_3372849] using wordTrace_append hprefix tailTrace_3372849
  have hstable : (prefixWord ++ tailWord_3372849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372849).length < 2 ^ (prefixWord ++ tailWord_3372849).sum := by decide
  have hdescent : baseEnd_3372849 < baseStart_3372849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372853 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3372853 : Nat := 118140960795 + 3372853 * 2 ^ 59
def prefixEnd_3372853 : Nat := 4983230072969 + 3 ^ 40 * 3372853 * 2
def baseEnd_3372853 : Nat := 1154596510639464953884025

theorem tailTrace_3372853 : CollatzResearch.WordTrace tailWord_3372853 prefixEnd_3372853 1154596510639464953884025 := by
  unfold tailWord_3372853
  simp only [CollatzResearch.WordTrace]
  refine ⟨123018055249737093276827213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82012036833158062184551475 123018055249737093276827213)
  ·
    refine ⟨46131770718651409978810205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123018055249737093276827213 46131770718651409978810205)
    ·
      refine ⟨17299414019494278742053827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46131770718651409978810205 17299414019494278742053827)
      ·
        refine ⟨25949121029241418113080741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17299414019494278742053827 25949121029241418113080741)
        ·
          refine ⟨4865460192982765896202639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25949121029241418113080741 4865460192982765896202639)
          ·
            refine ⟨7298190289474148844303959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865460192982765896202639 7298190289474148844303959)
            ·
              refine ⟨10947285434211223266455939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298190289474148844303959 10947285434211223266455939)
              ·
                refine ⟨16420928151316834899683909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10947285434211223266455939 16420928151316834899683909)
                ·
                  refine ⟨3078924028371906543690733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16420928151316834899683909 3078924028371906543690733)
                  ·
                    refine ⟨1154596510639464953884025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3078924028371906543690733 1154596510639464953884025)
                    ·
                      rfl

theorem cell22_3372853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3372853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372853 prefixEnd_3372853 := by exact prefixLift 3372853
  have htrace : WordTrace (prefixWord ++ tailWord_3372853) baseStart_3372853 baseEnd_3372853 := by
    simpa [prefixWord, tailWord_3372853, baseEnd_3372853] using wordTrace_append hprefix tailTrace_3372853
  have hstable : (prefixWord ++ tailWord_3372853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372853).length < 2 ^ (prefixWord ++ tailWord_3372853).sum := by decide
  have hdescent : baseEnd_3372853 < baseStart_3372853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372870 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3372870 : Nat := 118140960795 + 3372870 * 2 ^ 59
def prefixEnd_3372870 : Nat := 4983230072969 + 3 ^ 40 * 3372870 * 2
def baseEnd_3372870 : Nat := 1154602330086882576208973

theorem tailTrace_3372870 : CollatzResearch.WordTrace tailWord_3372870 prefixEnd_3372870 1154602330086882576208973 := by
  unfold tailWord_3372870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3844333602833609536881127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82012450193783670120130709 3844333602833609536881127)
  ·
    refine ⟨5766500404250414305321691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3844333602833609536881127 5766500404250414305321691)
    ·
      refine ⟨8649750606375621457982537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766500404250414305321691 8649750606375621457982537)
      ·
        refine ⟨6487312954781716093486903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8649750606375621457982537 6487312954781716093486903)
        ·
          refine ⟨9730969432172574140230355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6487312954781716093486903 9730969432172574140230355)
          ·
            refine ⟨14596454148258861210345533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9730969432172574140230355 14596454148258861210345533)
            ·
              refine ⟨5473670305597072953879575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14596454148258861210345533 5473670305597072953879575)
              ·
                refine ⟨8210505458395609430819363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473670305597072953879575 8210505458395609430819363)
                ·
                  refine ⟨12315758187593414146229045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210505458395609430819363 12315758187593414146229045)
                  ·
                    refine ⟨1154602330086882576208973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12315758187593414146229045 1154602330086882576208973)
                    ·
                      rfl

theorem cell22_3372870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3372870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372870 prefixEnd_3372870 := by exact prefixLift 3372870
  have htrace : WordTrace (prefixWord ++ tailWord_3372870) baseStart_3372870 baseEnd_3372870 := by
    simpa [prefixWord, tailWord_3372870, baseEnd_3372870] using wordTrace_append hprefix tailTrace_3372870
  have hstable : (prefixWord ++ tailWord_3372870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372870).length < 2 ^ (prefixWord ++ tailWord_3372870).sum := by decide
  have hdescent : baseEnd_3372870 < baseStart_3372870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372924 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3372924 : Nat := 118140960795 + 3372924 * 2 ^ 59
def prefixEnd_3372924 : Nat := 4983230072969 + 3 ^ 40 * 3372924 * 2
def baseEnd_3372924 : Nat := 1154620815390444435358807

theorem tailTrace_3372924 : CollatzResearch.WordTrace tailWord_3372924 prefixEnd_3372924 1154620815390444435358807 := by
  unfold tailWord_3372924
  simp only [CollatzResearch.WordTrace]
  refine ⟨61510322416239936201330913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82013763221653248268441217 61510322416239936201330913)
  ·
    refine ⟨46132741812179952150998185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61510322416239936201330913 46132741812179952150998185)
    ·
      refine ⟨34599556359134964113248639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46132741812179952150998185 34599556359134964113248639)
      ·
        refine ⟨51899334538702446169872959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34599556359134964113248639 51899334538702446169872959)
        ·
          refine ⟨77849001808053669254809439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51899334538702446169872959 77849001808053669254809439)
          ·
            refine ⟨116773502712080503882214159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77849001808053669254809439 116773502712080503882214159)
            ·
              refine ⟨175160254068120755823321239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116773502712080503882214159 175160254068120755823321239)
              ·
                refine ⟨262740381102181133734981859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175160254068120755823321239 262740381102181133734981859)
                ·
                  refine ⟨394110571653271700602472789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262740381102181133734981859 394110571653271700602472789)
                  ·
                    refine ⟨1154620815390444435358807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 394110571653271700602472789 1154620815390444435358807)
                    ·
                      rfl

theorem cell22_3372924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3372924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372924 prefixEnd_3372924 := by exact prefixLift 3372924
  have htrace : WordTrace (prefixWord ++ tailWord_3372924) baseStart_3372924 baseEnd_3372924 := by
    simpa [prefixWord, tailWord_3372924, baseEnd_3372924] using wordTrace_append hprefix tailTrace_3372924
  have hstable : (prefixWord ++ tailWord_3372924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372924).length < 2 ^ (prefixWord ++ tailWord_3372924).sum := by decide
  have hdescent : baseEnd_3372924 < baseStart_3372924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372939 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 8]
def baseStart_3372939 : Nat := 118140960795 + 3372939 * 2 ^ 59
def prefixEnd_3372939 : Nat := 4983230072969 + 3 ^ 40 * 3372939 * 2
def baseEnd_3372939 : Nat := 384875316732329798744587

theorem tailTrace_3372939 : CollatzResearch.WordTrace tailWord_3372939 prefixEnd_3372939 384875316732329798744587 := by
  unfold tailWord_3372939
  simp only [CollatzResearch.WordTrace]
  refine ⟨123021191927425529964457871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82014127951617019976305247 123021191927425529964457871)
  ·
    refine ⟨184531787891138294946686807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123021191927425529964457871 184531787891138294946686807)
    ·
      refine ⟨276797681836707442420030211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184531787891138294946686807 276797681836707442420030211)
      ·
        refine ⟨415196522755061163630045317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276797681836707442420030211 415196522755061163630045317)
        ·
          refine ⟨77849348016573968180633497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415196522755061163630045317 77849348016573968180633497)
          ·
            refine ⟨58387011012430476135475123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77849348016573968180633497 58387011012430476135475123)
            ·
              refine ⟨87580516518645714203212685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58387011012430476135475123 87580516518645714203212685)
              ·
                refine ⟨32842693694492142826204757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87580516518645714203212685 32842693694492142826204757)
                ·
                  refine ⟨384875316732329798744587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32842693694492142826204757 384875316732329798744587)
                  ·
                    rfl

theorem cell22_3372939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_3372939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3372939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3372939 prefixEnd_3372939 := by exact prefixLift 3372939
  have htrace : WordTrace (prefixWord ++ tailWord_3372939) baseStart_3372939 baseEnd_3372939 := by
    simpa [prefixWord, tailWord_3372939, baseEnd_3372939] using wordTrace_append hprefix tailTrace_3372939
  have hstable : (prefixWord ++ tailWord_3372939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372939).length < 2 ^ (prefixWord ++ tailWord_3372939).sum := by decide
  have hdescent : baseEnd_3372939 < baseStart_3372939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373069 : List Nat := [1, 7, 1, 2, 2, 1, 8]
def baseStart_3373069 : Nat := 118140960795 + 3373069 * 2 ^ 59
def prefixEnd_3373069 : Nat := 4983230072969 + 3 ^ 40 * 3373069 * 2
def baseEnd_3373069 : Nat := 42765572290878236684569

theorem tailTrace_3373069 : CollatzResearch.WordTrace tailWord_3373069 prefixEnd_3373069 42765572290878236684569 := by
  unfold tailWord_3373069
  simp only [CollatzResearch.WordTrace]
  refine ⟨123025933416954562166690261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82017288944636374777793507 123025933416954562166690261)
  ·
    refine ⟨2883420314459872550781803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 123025933416954562166690261 2883420314459872550781803)
    ·
      refine ⟨4325130471689808826172705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883420314459872550781803 4325130471689808826172705)
      ·
        refine ⟨3243847853767356619629529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4325130471689808826172705 3243847853767356619629529)
        ·
          refine ⟨2432885890325517464722147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243847853767356619629529 2432885890325517464722147)
          ·
            refine ⟨3649328835488276197083221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432885890325517464722147 3649328835488276197083221)
            ·
              refine ⟨42765572290878236684569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3649328835488276197083221 42765572290878236684569)
              ·
                rfl

theorem cell22_3373069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 8].length) (baseStart_3373069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373069 prefixEnd_3373069 := by exact prefixLift 3373069
  have htrace : WordTrace (prefixWord ++ tailWord_3373069) baseStart_3373069 baseEnd_3373069 := by
    simpa [prefixWord, tailWord_3373069, baseEnd_3373069] using wordTrace_append hprefix tailTrace_3373069
  have hstable : (prefixWord ++ tailWord_3373069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373069).length < 2 ^ (prefixWord ++ tailWord_3373069).sum := by decide
  have hdescent : baseEnd_3373069 < baseStart_3373069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373084 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_3373084 : Nat := 118140960795 + 3373084 * 2 ^ 59
def prefixEnd_3373084 : Nat := 4983230072969 + 3 ^ 40 * 3373084 * 2
def baseEnd_3373084 : Nat := 1154675586660257351358317

theorem tailTrace_3373084 : CollatzResearch.WordTrace tailWord_3373084 prefixEnd_3373084 1154675586660257351358317 := by
  unfold tailWord_3373084
  simp only [CollatzResearch.WordTrace]
  refine ⟨61513240255950109864243153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82017653674600146485657537 61513240255950109864243153)
  ·
    refine ⟨46134930191962582398182365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61513240255950109864243153 46134930191962582398182365)
    ·
      refine ⟨17300598821985968399318387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46134930191962582398182365 17300598821985968399318387)
      ·
        refine ⟨25950898232978952598977581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17300598821985968399318387 25950898232978952598977581)
        ·
          refine ⟨9731586837367107224616593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25950898232978952598977581 9731586837367107224616593)
          ·
            refine ⟨7298690128025330418462445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9731586837367107224616593 7298690128025330418462445)
            ·
              refine ⟨2737008798009498906923417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7298690128025330418462445 2737008798009498906923417)
              ·
                refine ⟨2052756598507124180192563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737008798009498906923417 2052756598507124180192563)
                ·
                  refine ⟨3079134897760686270288845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052756598507124180192563 3079134897760686270288845)
                  ·
                    refine ⟨1154675586660257351358317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079134897760686270288845 1154675586660257351358317)
                    ·
                      rfl

theorem cell22_3373084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_3373084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373084 prefixEnd_3373084 := by exact prefixLift 3373084
  have htrace : WordTrace (prefixWord ++ tailWord_3373084) baseStart_3373084 baseEnd_3373084 := by
    simpa [prefixWord, tailWord_3373084, baseEnd_3373084] using wordTrace_append hprefix tailTrace_3373084
  have hstable : (prefixWord ++ tailWord_3373084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373084).length < 2 ^ (prefixWord ++ tailWord_3373084).sum := by decide
  have hdescent : baseEnd_3373084 < baseStart_3373084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373110 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3373110 : Nat := 118140960795 + 3373110 * 2 ^ 59
def prefixEnd_3373110 : Nat := 4983230072969 + 3 ^ 40 * 3373110 * 2
def baseEnd_3373110 : Nat := 1154684486991601950208237

theorem tailTrace_3373110 : CollatzResearch.WordTrace tailWord_3373110 prefixEnd_3373110 1154684486991601950208237 := by
  unfold tailWord_3373110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689214300612876635558299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82018285873204017445955189 7689214300612876635558299)
  ·
    refine ⟨11533821450919314953337449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7689214300612876635558299 11533821450919314953337449)
    ·
      refine ⟨8650366088189486215003087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11533821450919314953337449 8650366088189486215003087)
      ·
        refine ⟨12975549132284229322504631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8650366088189486215003087 12975549132284229322504631)
        ·
          refine ⟨19463323698426343983756947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12975549132284229322504631 19463323698426343983756947)
          ·
            refine ⟨29194985547639515975635421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19463323698426343983756947 29194985547639515975635421)
            ·
              refine ⟨10948119580364818490863283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29194985547639515975635421 10948119580364818490863283)
              ·
                refine ⟨16422179370547227736294925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10948119580364818490863283 16422179370547227736294925)
                ·
                  refine ⟨6158317263955210401110597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16422179370547227736294925 6158317263955210401110597)
                  ·
                    refine ⟨1154684486991601950208237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6158317263955210401110597 1154684486991601950208237)
                    ·
                      rfl

theorem cell22_3373110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3373110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373110 prefixEnd_3373110 := by exact prefixLift 3373110
  have htrace : WordTrace (prefixWord ++ tailWord_3373110) baseStart_3373110 baseEnd_3373110 := by
    simpa [prefixWord, tailWord_3373110, baseEnd_3373110] using wordTrace_append hprefix tailTrace_3373110
  have hstable : (prefixWord ++ tailWord_3373110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373110).length < 2 ^ (prefixWord ++ tailWord_3373110).sum := by decide
  have hdescent : baseEnd_3373110 < baseStart_3373110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373123 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 4, 3]
def baseStart_3373123 : Nat := 118140960795 + 3373123 * 2 ^ 59
def prefixEnd_3373123 : Nat := 4983230072969 + 3 ^ 40 * 3373123 * 2
def baseEnd_3373123 : Nat := 1154688937157274249633197

theorem tailTrace_3373123 : CollatzResearch.WordTrace tailWord_3373123 prefixEnd_3373123 1154688937157274249633197 := by
  unfold tailWord_3373123
  simp only [CollatzResearch.WordTrace]
  refine ⟨123027902958758929389156023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82018601972505952926104015 123027902958758929389156023)
  ·
    refine ⟨184541854438138394083734035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123027902958758929389156023 184541854438138394083734035)
    ·
      refine ⟨276812781657207591125601053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184541854438138394083734035 276812781657207591125601053)
      ·
        refine ⟨103804793121452846672100395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276812781657207591125601053 103804793121452846672100395)
        ·
          refine ⟨155707189682179270008150593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103804793121452846672100395 155707189682179270008150593)
          ·
            refine ⟨116780392261634452506112945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155707189682179270008150593 116780392261634452506112945)
            ·
              refine ⟨87585294196225839379584709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116780392261634452506112945 87585294196225839379584709)
              ·
                refine ⟨16422242661792344883672133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87585294196225839379584709 16422242661792344883672133)
                ·
                  refine ⟨3079170499086064665688525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16422242661792344883672133 3079170499086064665688525)
                  ·
                    refine ⟨1154688937157274249633197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079170499086064665688525 1154688937157274249633197)
                    ·
                      rfl

theorem cell22_3373123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 3].length) (baseStart_3373123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373123 prefixEnd_3373123 := by exact prefixLift 3373123
  have htrace : WordTrace (prefixWord ++ tailWord_3373123) baseStart_3373123 baseEnd_3373123 := by
    simpa [prefixWord, tailWord_3373123, baseEnd_3373123] using wordTrace_append hprefix tailTrace_3373123
  have hstable : (prefixWord ++ tailWord_3373123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373123).length < 2 ^ (prefixWord ++ tailWord_3373123).sum := by decide
  have hdescent : baseEnd_3373123 < baseStart_3373123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373170 : List Nat := [3, 2, 1, 2, 2, 3, 3, 6]
def baseStart_3373170 : Nat := 118140960795 + 3373170 * 2 ^ 59
def prefixEnd_3373170 : Nat := 4983230072969 + 3 ^ 40 * 3373170 * 2
def baseEnd_3373170 : Nat := 128300558468642421523117

theorem tailTrace_3373170 : CollatzResearch.WordTrace tailWord_3373170 prefixEnd_3373170 128300558468642421523117 := by
  unfold tailWord_3373170
  simp only [CollatzResearch.WordTrace]
  refine ⟨30757404297397164104029241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82019744793059104277411309 30757404297397164104029241)
  ·
    refine ⟨23068053223047873078021931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30757404297397164104029241 23068053223047873078021931)
    ·
      refine ⟨34602079834571809617032897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23068053223047873078021931 34602079834571809617032897)
      ·
        refine ⟨25951559875928857212774673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34602079834571809617032897 25951559875928857212774673)
        ·
          refine ⟨19463669906946642909581005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25951559875928857212774673 19463669906946642909581005)
          ·
            refine ⟨7298876215104991091092877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19463669906946642909581005 7298876215104991091092877)
            ·
              refine ⟨2737078580664371659159829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7298876215104991091092877 2737078580664371659159829)
              ·
                refine ⟨128300558468642421523117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2737078580664371659159829 128300558468642421523117)
                ·
                  rfl

theorem cell22_3373170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_3373170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373170 prefixEnd_3373170 := by exact prefixLift 3373170
  have htrace : WordTrace (prefixWord ++ tailWord_3373170) baseStart_3373170 baseEnd_3373170 := by
    simpa [prefixWord, tailWord_3373170, baseEnd_3373170] using wordTrace_append hprefix tailTrace_3373170
  have hstable : (prefixWord ++ tailWord_3373170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373170).length < 2 ^ (prefixWord ++ tailWord_3373170).sum := by decide
  have hdescent : baseEnd_3373170 < baseStart_3373170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373202 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3373202 : Nat := 118140960795 + 3373202 * 2 ^ 59
def prefixEnd_3373202 : Nat := 4983230072969 + 3 ^ 40 * 3373202 * 2
def baseEnd_3373202 : Nat := 1154715980471744376907955

theorem tailTrace_3373202 : CollatzResearch.WordTrace tailWord_3373202 prefixEnd_3373202 1154715980471744376907955 := by
  unfold tailWord_3373202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30757696081368181470320465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82020522883648483920854573 30757696081368181470320465)
  ·
    refine ⟨23068272061026136102740349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30757696081368181470320465 23068272061026136102740349)
    ·
      refine ⟨8650602022884801038527631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23068272061026136102740349 8650602022884801038527631)
      ·
        refine ⟨12975903034327201557791447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8650602022884801038527631 12975903034327201557791447)
        ·
          refine ⟨19463854551490802336687171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12975903034327201557791447 19463854551490802336687171)
          ·
            refine ⟨29195781827236203505030757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19463854551490802336687171 29195781827236203505030757)
            ·
              refine ⟨5474209092606788157193267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29195781827236203505030757 5474209092606788157193267)
              ·
                refine ⟨8211313638910182235789901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474209092606788157193267 8211313638910182235789901)
                ·
                  refine ⟨3079242614591318338421213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8211313638910182235789901 3079242614591318338421213)
                  ·
                    refine ⟨1154715980471744376907955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079242614591318338421213 1154715980471744376907955)
                    ·
                      rfl

theorem cell22_3373202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3373202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373202 prefixEnd_3373202 := by exact prefixLift 3373202
  have htrace : WordTrace (prefixWord ++ tailWord_3373202) baseStart_3373202 baseEnd_3373202 := by
    simpa [prefixWord, tailWord_3373202, baseEnd_3373202] using wordTrace_append hprefix tailTrace_3373202
  have hstable : (prefixWord ++ tailWord_3373202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373202).length < 2 ^ (prefixWord ++ tailWord_3373202).sum := by decide
  have hdescent : baseEnd_3373202 < baseStart_3373202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373228 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_3373228 : Nat := 118140960795 + 3373228 * 2 ^ 59
def prefixEnd_3373228 : Nat := 4983230072969 + 3 ^ 40 * 3373228 * 2
def baseEnd_3373228 : Nat := 1154724880803088975757875

theorem tailTrace_3373228 : CollatzResearch.WordTrace tailWord_3373228 prefixEnd_3373228 1154724880803088975757875 := by
  unfold tailWord_3373228
  simp only [CollatzResearch.WordTrace]
  refine ⟨61515866311689266160864169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82021155082252354881152225 61515866311689266160864169)
  ·
    refine ⟨46136899733766949620648127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61515866311689266160864169 46136899733766949620648127)
    ·
      refine ⟨69205349600650424430972191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46136899733766949620648127 69205349600650424430972191)
      ·
        refine ⟨103808024400975636646458287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69205349600650424430972191 103808024400975636646458287)
        ·
          refine ⟨155712036601463454969687431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103808024400975636646458287 155712036601463454969687431)
          ·
            refine ⟨233568054902195182454531147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155712036601463454969687431 233568054902195182454531147)
            ·
              refine ⟨350352082353292773681796721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233568054902195182454531147 350352082353292773681796721)
              ·
                refine ⟨262764061764969580261347541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350352082353292773681796721 262764061764969580261347541)
                ·
                  refine ⟨6158532697616474537375333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 262764061764969580261347541 6158532697616474537375333)
                  ·
                    refine ⟨1154724880803088975757875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6158532697616474537375333 1154724880803088975757875)
                    ·
                      rfl

theorem cell22_3373228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_3373228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373228 prefixEnd_3373228 := by exact prefixLift 3373228
  have htrace : WordTrace (prefixWord ++ tailWord_3373228) baseStart_3373228 baseEnd_3373228 := by
    simpa [prefixWord, tailWord_3373228, baseEnd_3373228] using wordTrace_append hprefix tailTrace_3373228
  have hstable : (prefixWord ++ tailWord_3373228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373228).length < 2 ^ (prefixWord ++ tailWord_3373228).sum := by decide
  have hdescent : baseEnd_3373228 < baseStart_3373228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373273 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_3373273 : Nat := 118140960795 + 3373273 * 2 ^ 59
def prefixEnd_3373273 : Nat := 4983230072969 + 3 ^ 40 * 3373273 * 2
def baseEnd_3373273 : Nat := 1154740285222723858382737

theorem tailTrace_3373273 : CollatzResearch.WordTrace tailWord_3373273 prefixEnd_3373273 1154740285222723858382737 := by
  unfold tailWord_3373273
  simp only [CollatzResearch.WordTrace]
  refine ⟨123033373908215505007116473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82022249272143670004744315 123033373908215505007116473)
  ·
    refine ⟨92275030431161628755337355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123033373908215505007116473 92275030431161628755337355)
    ·
      refine ⟨138412545646742443133006033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92275030431161628755337355 138412545646742443133006033)
      ·
        refine ⟨103809409235056832349754525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138412545646742443133006033 103809409235056832349754525)
        ·
          refine ⟨38928528463146312131157947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103809409235056832349754525 38928528463146312131157947)
          ·
            refine ⟨58392792694719468196736921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38928528463146312131157947 58392792694719468196736921)
            ·
              refine ⟨43794594521039601147552691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58392792694719468196736921 43794594521039601147552691)
              ·
                refine ⟨65691891781559401721329037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43794594521039601147552691 65691891781559401721329037)
                ·
                  refine ⟨24634459418084775645498389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65691891781559401721329037 24634459418084775645498389)
                  ·
                    refine ⟨1154740285222723858382737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24634459418084775645498389 1154740285222723858382737)
                    ·
                      rfl

theorem cell22_3373273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_3373273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373273 prefixEnd_3373273 := by exact prefixLift 3373273
  have htrace : WordTrace (prefixWord ++ tailWord_3373273) baseStart_3373273 baseEnd_3373273 := by
    simpa [prefixWord, tailWord_3373273, baseEnd_3373273] using wordTrace_append hprefix tailTrace_3373273
  have hstable : (prefixWord ++ tailWord_3373273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373273).length < 2 ^ (prefixWord ++ tailWord_3373273).sum := by decide
  have hdescent : baseEnd_3373273 < baseStart_3373273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373341 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3373341 : Nat := 118140960795 + 3373341 * 2 ^ 59
def prefixEnd_3373341 : Nat := 4983230072969 + 3 ^ 40 * 3373341 * 2
def baseEnd_3373341 : Nat := 1154763563012394347682529

theorem tailTrace_3373341 : CollatzResearch.WordTrace tailWord_3373341 prefixEnd_3373341 1154763563012394347682529 := by
  unfold tailWord_3373341
  simp only [CollatzResearch.WordTrace]
  refine ⟨123035854071969152620591877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82023902714646101747061251 123035854071969152620591877)
  ·
    refine ⟨23069222638494216116360977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123035854071969152620591877 23069222638494216116360977)
    ·
      refine ⟨17301916978870662087270733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23069222638494216116360977 17301916978870662087270733)
      ·
        refine ⟨6488218867076498282726525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17301916978870662087270733 6488218867076498282726525)
        ·
          refine ⟨2433082075153686856022447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6488218867076498282726525 2433082075153686856022447)
          ·
            refine ⟨3649623112730530284033671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433082075153686856022447 3649623112730530284033671)
            ·
              refine ⟨5474434669095795426050507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649623112730530284033671 5474434669095795426050507)
              ·
                refine ⟨8211652003643693139075761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474434669095795426050507 8211652003643693139075761)
                ·
                  refine ⟨6158739002732769854306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8211652003643693139075761 6158739002732769854306821)
                  ·
                    refine ⟨1154763563012394347682529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6158739002732769854306821 1154763563012394347682529)
                    ·
                      rfl

theorem cell22_3373341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3373341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373341 prefixEnd_3373341 := by exact prefixLift 3373341
  have htrace : WordTrace (prefixWord ++ tailWord_3373341) baseStart_3373341 baseEnd_3373341 := by
    simpa [prefixWord, tailWord_3373341, baseEnd_3373341] using wordTrace_append hprefix tailTrace_3373341
  have hstable : (prefixWord ++ tailWord_3373341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373341).length < 2 ^ (prefixWord ++ tailWord_3373341).sum := by decide
  have hdescent : baseEnd_3373341 < baseStart_3373341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373365 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3373365 : Nat := 118140960795 + 3373365 * 2 ^ 59
def prefixEnd_3373365 : Nat := 4983230072969 + 3 ^ 40 * 3373365 * 2
def baseEnd_3373365 : Nat := 1154771778702866285082455

theorem tailTrace_3373365 : CollatzResearch.WordTrace tailWord_3373365 prefixEnd_3373365 1154771778702866285082455 := by
  unfold tailWord_3373365
  simp only [CollatzResearch.WordTrace]
  refine ⟨123036729423882204719465549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82024486282588136479643699 123036729423882204719465549)
  ·
    refine ⟨46138773533955826769799581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123036729423882204719465549 46138773533955826769799581)
    ·
      refine ⟨17302040075233435038674843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46138773533955826769799581 17302040075233435038674843)
      ·
        refine ⟨25953060112850152558012265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17302040075233435038674843 25953060112850152558012265)
        ·
          refine ⟨19464795084637614418509199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25953060112850152558012265 19464795084637614418509199)
          ·
            refine ⟨29197192626956421627763799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19464795084637614418509199 29197192626956421627763799)
            ·
              refine ⟨43795788940434632441645699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29197192626956421627763799 43795788940434632441645699)
              ·
                refine ⟨65693683410651948662468549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43795788940434632441645699 65693683410651948662468549)
                ·
                  refine ⟨12317565639497240374212853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65693683410651948662468549 12317565639497240374212853)
                  ·
                    refine ⟨1154771778702866285082455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12317565639497240374212853 1154771778702866285082455)
                    ·
                      rfl

theorem cell22_3373365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3373365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373365 prefixEnd_3373365 := by exact prefixLift 3373365
  have htrace : WordTrace (prefixWord ++ tailWord_3373365) baseStart_3373365 baseEnd_3373365 := by
    simpa [prefixWord, tailWord_3373365, baseEnd_3373365] using wordTrace_append hprefix tailTrace_3373365
  have hstable : (prefixWord ++ tailWord_3373365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373365).length < 2 ^ (prefixWord ++ tailWord_3373365).sum := by decide
  have hdescent : baseEnd_3373365 < baseStart_3373365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373429 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 6]
def baseStart_3373429 : Nat := 118140960795 + 3373429 * 2 ^ 59
def prefixEnd_3373429 : Nat := 4983230072969 + 3 ^ 40 * 3373429 * 2
def baseEnd_3373429 : Nat := 384931229070263817160753

theorem tailTrace_3373429 : CollatzResearch.WordTrace tailWord_3373429 prefixEnd_3373429 384931229070263817160753 := by
  unfold tailWord_3373429
  simp only [CollatzResearch.WordTrace]
  refine ⟨123039063695650343649795341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82026042463766895766530227 123039063695650343649795341)
  ·
    refine ⟨46139648885868878868673253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123039063695650343649795341 46139648885868878868673253)
    ·
      refine ⟨8651184166100414787876235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46139648885868878868673253 8651184166100414787876235)
      ·
        refine ⟨12976776249150622181814353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8651184166100414787876235 12976776249150622181814353)
        ·
          refine ⟨9732582186862966636360765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12976776249150622181814353 9732582186862966636360765)
          ·
            refine ⟨3649718320073612488635287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9732582186862966636360765 3649718320073612488635287)
            ·
              refine ⟨5474577480110418732952931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649718320073612488635287 5474577480110418732952931)
              ·
                refine ⟨8211866220165628099429397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474577480110418732952931 8211866220165628099429397)
                ·
                  refine ⟨384931229070263817160753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8211866220165628099429397 384931229070263817160753)
                  ·
                    rfl

theorem cell22_3373429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_3373429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373429 prefixEnd_3373429 := by exact prefixLift 3373429
  have htrace : WordTrace (prefixWord ++ tailWord_3373429) baseStart_3373429 baseEnd_3373429 := by
    simpa [prefixWord, tailWord_3373429, baseEnd_3373429] using wordTrace_append hprefix tailTrace_3373429
  have hstable : (prefixWord ++ tailWord_3373429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373429).length < 2 ^ (prefixWord ++ tailWord_3373429).sum := by decide
  have hdescent : baseEnd_3373429 < baseStart_3373429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373444 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3373444 : Nat := 118140960795 + 3373444 * 2 ^ 59
def prefixEnd_3373444 : Nat := 4983230072969 + 3 ^ 40 * 3373444 * 2
def baseEnd_3373444 : Nat := 1154798822017336412357213

theorem tailTrace_3373444 : CollatzResearch.WordTrace tailWord_3373444 prefixEnd_3373444 1154798822017336412357213 := by
  unfold tailWord_3373444
  simp only [CollatzResearch.WordTrace]
  refine ⟨61519805395298000605795693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82026407193730667474394257 61519805395298000605795693)
  ·
    refine ⟨23069927023236750227173385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61519805395298000605795693 23069927023236750227173385)
    ·
      refine ⟨17302445267427562670380039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23069927023236750227173385 17302445267427562670380039)
      ·
        refine ⟨25953667901141344005570059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17302445267427562670380039 25953667901141344005570059)
        ·
          refine ⟨38930501851712016008355089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25953667901141344005570059 38930501851712016008355089)
          ·
            refine ⟨29197876388784012006266317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38930501851712016008355089 29197876388784012006266317)
            ·
              refine ⟨10949203645794004502349869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29197876388784012006266317 10949203645794004502349869)
              ·
                refine ⟨4105951367172751688381201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10949203645794004502349869 4105951367172751688381201)
                ·
                  refine ⟨3079463525379563766285901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4105951367172751688381201 3079463525379563766285901)
                  ·
                    refine ⟨1154798822017336412357213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079463525379563766285901 1154798822017336412357213)
                    ·
                      rfl

theorem cell22_3373444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3373444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373444 prefixEnd_3373444 := by exact prefixLift 3373444
  have htrace : WordTrace (prefixWord ++ tailWord_3373444) baseStart_3373444 baseEnd_3373444 := by
    simpa [prefixWord, tailWord_3373444, baseEnd_3373444] using wordTrace_append hprefix tailTrace_3373444
  have hstable : (prefixWord ++ tailWord_3373444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373444).length < 2 ^ (prefixWord ++ tailWord_3373444).sum := by decide
  have hdescent : baseEnd_3373444 < baseStart_3373444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373547 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 6]
def baseStart_3373547 : Nat := 118140960795 + 3373547 * 2 ^ 59
def prefixEnd_3373547 : Nat := 4983230072969 + 3 ^ 40 * 3373547 * 2
def baseEnd_3373547 : Nat := 384944693674092825677299

theorem tailTrace_3373547 : CollatzResearch.WordTrace tailWord_3373547 prefixEnd_3373547 384944693674092825677299 := by
  unfold tailWord_3373547
  simp only [CollatzResearch.WordTrace]
  refine ⟨123043367509222849802590895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82028911672815233201727263 123043367509222849802590895)
  ·
    refine ⟨184565051263834274703886343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123043367509222849802590895 184565051263834274703886343)
    ·
      refine ⟨276847576895751412055829515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184565051263834274703886343 276847576895751412055829515)
      ·
        refine ⟨415271365343627118083744273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276847576895751412055829515 415271365343627118083744273)
        ·
          refine ⟨311453524007720338562808205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415271365343627118083744273 311453524007720338562808205)
          ·
            refine ⟨116795071502895126961053077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311453524007720338562808205 116795071502895126961053077)
            ·
              refine ⟨5474768976698209076299363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116795071502895126961053077 5474768976698209076299363)
              ·
                refine ⟨8212153465047313614449045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474768976698209076299363 8212153465047313614449045)
                ·
                  refine ⟨384944693674092825677299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8212153465047313614449045 384944693674092825677299)
                  ·
                    rfl

theorem cell22_3373547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 6].length) (baseStart_3373547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373547 prefixEnd_3373547 := by exact prefixLift 3373547
  have htrace : WordTrace (prefixWord ++ tailWord_3373547) baseStart_3373547 baseEnd_3373547 := by
    simpa [prefixWord, tailWord_3373547, baseEnd_3373547] using wordTrace_append hprefix tailTrace_3373547
  have hstable : (prefixWord ++ tailWord_3373547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373547).length < 2 ^ (prefixWord ++ tailWord_3373547).sum := by decide
  have hdescent : baseEnd_3373547 < baseStart_3373547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373562 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_3373562 : Nat := 118140960795 + 3373562 * 2 ^ 59
def prefixEnd_3373562 : Nat := 4983230072969 + 3 ^ 40 * 3373562 * 2
def baseEnd_3373562 : Nat := 1154839215828823437906851

theorem tailTrace_3373562 : CollatzResearch.WordTrace tailWord_3373562 prefixEnd_3373562 1154839215828823437906851 := by
  unfold tailWord_3373562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30760978651042126841096735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82029276402779004909591293 30760978651042126841096735)
  ·
    refine ⟨46141467976563190261645103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30760978651042126841096735 46141467976563190261645103)
    ·
      refine ⟨69212201964844785392467655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46141467976563190261645103 69212201964844785392467655)
      ·
        refine ⟨103818302947267178088701483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69212201964844785392467655 103818302947267178088701483)
        ·
          refine ⟨155727454420900767133052225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103818302947267178088701483 155727454420900767133052225)
          ·
            refine ⟨116795590815675575349789169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155727454420900767133052225 116795590815675575349789169)
            ·
              refine ⟨87596693111756681512341877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116795590815675575349789169 87596693111756681512341877)
              ·
                refine ⟨8212189979227188891782051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87596693111756681512341877 8212189979227188891782051)
                ·
                  refine ⟨12318284968840783337673077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212189979227188891782051 12318284968840783337673077)
                  ·
                    refine ⟨1154839215828823437906851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12318284968840783337673077 1154839215828823437906851)
                    ·
                      rfl

theorem cell22_3373562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_3373562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373562 prefixEnd_3373562 := by exact prefixLift 3373562
  have htrace : WordTrace (prefixWord ++ tailWord_3373562) baseStart_3373562 baseEnd_3373562 := by
    simpa [prefixWord, tailWord_3373562, baseEnd_3373562] using wordTrace_append hprefix tailTrace_3373562
  have hstable : (prefixWord ++ tailWord_3373562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373562).length < 2 ^ (prefixWord ++ tailWord_3373562).sum := by decide
  have hdescent : baseEnd_3373562 < baseStart_3373562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373574 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3373574 : Nat := 118140960795 + 3373574 * 2 ^ 59
def prefixEnd_3373574 : Nat := 4983230072969 + 3 ^ 40 * 3373574 * 2
def baseEnd_3373574 : Nat := 1154843323674059406606815

theorem tailTrace_3373574 : CollatzResearch.WordTrace tailWord_3373574 prefixEnd_3373574 1154843323674059406606815 := by
  unfold tailWord_3373574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845136008753907294181993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82029568186750022275882517 3845136008753907294181993)
  ·
    refine ⟨2883852006565430470636495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3845136008753907294181993 2883852006565430470636495)
    ·
      refine ⟨4325778009848145705954743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883852006565430470636495 4325778009848145705954743)
      ·
        refine ⟨6488667014772218558932115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325778009848145705954743 6488667014772218558932115)
        ·
          refine ⟨9733000522158327838398173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488667014772218558932115 9733000522158327838398173)
          ·
            refine ⟨3649875195809372939399315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9733000522158327838398173 3649875195809372939399315)
            ·
              refine ⟨5474812793714059409098973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649875195809372939399315 5474812793714059409098973)
              ·
                refine ⟨2053054797642772278412115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5474812793714059409098973 2053054797642772278412115)
                ·
                  refine ⟨3079582196464158417618173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053054797642772278412115 3079582196464158417618173)
                  ·
                    refine ⟨1154843323674059406606815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079582196464158417618173 1154843323674059406606815)
                    ·
                      rfl

theorem cell22_3373574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3373574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373574 prefixEnd_3373574 := by exact prefixLift 3373574
  have htrace : WordTrace (prefixWord ++ tailWord_3373574) baseStart_3373574 baseEnd_3373574 := by
    simpa [prefixWord, tailWord_3373574, baseEnd_3373574] using wordTrace_append hprefix tailTrace_3373574
  have hstable : (prefixWord ++ tailWord_3373574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373574).length < 2 ^ (prefixWord ++ tailWord_3373574).sum := by decide
  have hdescent : baseEnd_3373574 < baseStart_3373574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373579 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 4, 3]
def baseStart_3373579 : Nat := 118140960795 + 3373579 * 2 ^ 59
def prefixEnd_3373579 : Nat := 4983230072969 + 3 ^ 40 * 3373579 * 2
def baseEnd_3373579 : Nat := 1154845035276241060231799

theorem tailTrace_3373579 : CollatzResearch.WordTrace tailWord_3373579 prefixEnd_3373579 1154845035276241060231799 := by
  unfold tailWord_3373579
  simp only [CollatzResearch.WordTrace]
  refine ⟨123044534645106919267755791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82029689763404612845170527 123044534645106919267755791)
  ·
    refine ⟨184566801967660378901633687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123044534645106919267755791 184566801967660378901633687)
    ·
      refine ⟨276850202951490568352450531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184566801967660378901633687 276850202951490568352450531)
      ·
        refine ⟨415275304427235852528675797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276850202951490568352450531 415275304427235852528675797)
        ·
          refine ⟨9733014947513340293640839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 415275304427235852528675797 9733014947513340293640839)
          ·
            refine ⟨14599522421270010440461259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733014947513340293640839 14599522421270010440461259)
            ·
              refine ⟨21899283631905015660691889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14599522421270010440461259 21899283631905015660691889)
              ·
                refine ⟨16424462723928761745518917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21899283631905015660691889 16424462723928761745518917)
                ·
                  refine ⟨3079586760736642827284797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16424462723928761745518917 3079586760736642827284797)
                  ·
                    refine ⟨1154845035276241060231799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079586760736642827284797 1154845035276241060231799)
                    ·
                      rfl

theorem cell22_3373579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 3].length) (baseStart_3373579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373579 prefixEnd_3373579 := by exact prefixLift 3373579
  have htrace : WordTrace (prefixWord ++ tailWord_3373579) baseStart_3373579 baseEnd_3373579 := by
    simpa [prefixWord, tailWord_3373579, baseEnd_3373579] using wordTrace_append hprefix tailTrace_3373579
  have hstable : (prefixWord ++ tailWord_3373579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373579).length < 2 ^ (prefixWord ++ tailWord_3373579).sum := by decide
  have hdescent : baseEnd_3373579 < baseStart_3373579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373592 : List Nat := [2, 1, 2, 3, 3, 1, 10]
def baseStart_3373592 : Nat := 118140960795 + 3373592 * 2 ^ 59
def prefixEnd_3373592 : Nat := 4983230072969 + 3 ^ 40 * 3373592 * 2
def baseEnd_3373592 : Nat := 42772203164515309616917

theorem tailTrace_3373592 : CollatzResearch.WordTrace tailWord_3373592 prefixEnd_3373592 42772203164515309616917 := by
  unfold tailWord_3373592
  simp only [CollatzResearch.WordTrace]
  refine ⟨61522504397029911243989515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82030005862706548325319353 61522504397029911243989515)
  ·
    refine ⟨92283756595544866865984273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61522504397029911243989515 92283756595544866865984273)
    ·
      refine ⟨69212817446658650149488205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92283756595544866865984273 69212817446658650149488205)
      ·
        refine ⟨25954806542496993806058077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69212817446658650149488205 25954806542496993806058077)
        ·
          refine ⟨9733052453436372677271779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25954806542496993806058077 9733052453436372677271779)
          ·
            refine ⟨14599578680154559015907669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733052453436372677271779 14599578680154559015907669)
            ·
              refine ⟨42772203164515309616917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14599578680154559015907669 42772203164515309616917)
              ·
                rfl

theorem cell22_3373592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 10].length) (baseStart_3373592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373592 prefixEnd_3373592 := by exact prefixLift 3373592
  have htrace : WordTrace (prefixWord ++ tailWord_3373592) baseStart_3373592 baseEnd_3373592 := by
    simpa [prefixWord, tailWord_3373592, baseEnd_3373592] using wordTrace_append hprefix tailTrace_3373592
  have hstable : (prefixWord ++ tailWord_3373592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373592).length < 2 ^ (prefixWord ++ tailWord_3373592).sum := by decide
  have hdescent : baseEnd_3373592 < baseStart_3373592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373624 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_3373624 : Nat := 118140960795 + 3373624 * 2 ^ 59
def prefixEnd_3373624 : Nat := 4983230072969 + 3 ^ 40 * 3373624 * 2
def baseEnd_3373624 : Nat := 1154860439695875942856661

theorem tailTrace_3373624 : CollatzResearch.WordTrace tailWord_3373624 prefixEnd_3373624 1154860439695875942856661 := by
  unfold tailWord_3373624
  simp only [CollatzResearch.WordTrace]
  refine ⟨61523087964971945976571963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82030783953295927968762617 61523087964971945976571963)
  ·
    refine ⟨92284631947457918964857945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61523087964971945976571963 92284631947457918964857945)
    ·
      refine ⟨69213473960593439223643459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92284631947457918964857945 69213473960593439223643459)
      ·
        refine ⟨103820210940890158835465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69213473960593439223643459 103820210940890158835465189)
        ·
          refine ⟨19466289551416904781649723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103820210940890158835465189 19466289551416904781649723)
          ·
            refine ⟨29199434327125357172474585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19466289551416904781649723 29199434327125357172474585)
            ·
              refine ⟨21899575745344017879355939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29199434327125357172474585 21899575745344017879355939)
              ·
                refine ⟨32849363618016026819033909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21899575745344017879355939 32849363618016026819033909)
                ·
                  refine ⟨3079627839189002514284429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32849363618016026819033909 3079627839189002514284429)
                  ·
                    refine ⟨1154860439695875942856661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079627839189002514284429 1154860439695875942856661)
                    ·
                      rfl

theorem cell22_3373624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_3373624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373624 prefixEnd_3373624 := by exact prefixLift 3373624
  have htrace : WordTrace (prefixWord ++ tailWord_3373624) baseStart_3373624 baseEnd_3373624 := by
    simpa [prefixWord, tailWord_3373624, baseEnd_3373624] using wordTrace_append hprefix tailTrace_3373624
  have hstable : (prefixWord ++ tailWord_3373624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373624).length < 2 ^ (prefixWord ++ tailWord_3373624).sum := by decide
  have hdescent : baseEnd_3373624 < baseStart_3373624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373701 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3373701 : Nat := 118140960795 + 3373701 * 2 ^ 59
def prefixEnd_3373701 : Nat := 4983230072969 + 3 ^ 40 * 3373701 * 2
def baseEnd_3373701 : Nat := 1154886798369473408681425

theorem tailTrace_3373701 : CollatzResearch.WordTrace tailWord_3373701 prefixEnd_3373701 1154886798369473408681425 := by
  unfold tailWord_3373701
  simp only [CollatzResearch.WordTrace]
  refine ⟨123048984350664934103696957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82032656233776622735797971 123048984350664934103696957)
  ·
    refine ⟨46143369131499350288886359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123048984350664934103696957 46143369131499350288886359)
    ·
      refine ⟨69215053697249025433329539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46143369131499350288886359 69215053697249025433329539)
      ·
        refine ⟨103822580545873538149994309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69215053697249025433329539 103822580545873538149994309)
        ·
          refine ⟨19466733852351288403123933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103822580545873538149994309 19466733852351288403123933)
          ·
            refine ⟨7300025194631733151171475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19466733852351288403123933 7300025194631733151171475)
            ·
              refine ⟨10950037791947599726757213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300025194631733151171475 10950037791947599726757213)
              ·
                refine ⟨4106264171980349897533955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10950037791947599726757213 4106264171980349897533955)
                ·
                  refine ⟨6159396257970524846300933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106264171980349897533955 6159396257970524846300933)
                  ·
                    refine ⟨1154886798369473408681425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159396257970524846300933 1154886798369473408681425)
                    ·
                      rfl

theorem cell22_3373701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3373701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373701 prefixEnd_3373701 := by exact prefixLift 3373701
  have htrace : WordTrace (prefixWord ++ tailWord_3373701) baseStart_3373701 baseEnd_3373701 := by
    simpa [prefixWord, tailWord_3373701, baseEnd_3373701] using wordTrace_append hprefix tailTrace_3373701
  have hstable : (prefixWord ++ tailWord_3373701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373701).length < 2 ^ (prefixWord ++ tailWord_3373701).sum := by decide
  have hdescent : baseEnd_3373701 < baseStart_3373701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373716 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3373716 : Nat := 118140960795 + 3373716 * 2 ^ 59
def prefixEnd_3373716 : Nat := 4983230072969 + 3 ^ 40 * 3373716 * 2
def baseEnd_3373716 : Nat := 384963977725339456518793

theorem tailTrace_3373716 : CollatzResearch.WordTrace tailWord_3373716 prefixEnd_3373716 384963977725339456518793 := by
  unfold tailWord_3373716
  simp only [CollatzResearch.WordTrace]
  refine ⟨61524765722805295832746501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82033020963740394443662001 61524765722805295832746501)
  ·
    refine ⟨11535893573025992968639969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61524765722805295832746501 11535893573025992968639969)
    ·
      refine ⟨8651920179769494726479977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11535893573025992968639969 8651920179769494726479977)
      ·
        refine ⟨6488940134827121044859983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8651920179769494726479977 6488940134827121044859983)
        ·
          refine ⟨9733410202240681567289975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488940134827121044859983 9733410202240681567289975)
          ·
            refine ⟨14600115303361022350934963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733410202240681567289975 14600115303361022350934963)
            ·
              refine ⟨21900172955041533526402445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14600115303361022350934963 21900172955041533526402445)
              ·
                refine ⟨8212564858140575072400917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21900172955041533526402445 8212564858140575072400917)
                ·
                  refine ⟨384963977725339456518793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8212564858140575072400917 384963977725339456518793)
                  ·
                    rfl

theorem cell22_3373716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3373716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373716 prefixEnd_3373716 := by exact prefixLift 3373716
  have htrace : WordTrace (prefixWord ++ tailWord_3373716) baseStart_3373716 baseEnd_3373716 := by
    simpa [prefixWord, tailWord_3373716, baseEnd_3373716] using wordTrace_append hprefix tailTrace_3373716
  have hstable : (prefixWord ++ tailWord_3373716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373716).length < 2 ^ (prefixWord ++ tailWord_3373716).sum := by decide
  have hdescent : baseEnd_3373716 < baseStart_3373716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373735 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3373735 : Nat := 118140960795 + 3373735 * 2 ^ 59
def prefixEnd_3373735 : Nat := 4983230072969 + 3 ^ 40 * 3373735 * 2
def baseEnd_3373735 : Nat := 1154898437264308653331321

theorem tailTrace_3373735 : CollatzResearch.WordTrace tailWord_3373735 prefixEnd_3373735 1154898437264308653331321 := by
  unfold tailWord_3373735
  simp only [CollatzResearch.WordTrace]
  refine ⟨123050224432541757910434659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82033482955027838606956439 123050224432541757910434659)
  ·
    refine ⟨184575336648812636865651989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123050224432541757910434659 184575336648812636865651989)
    ·
      refine ⟨8651968905413092353077437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184575336648812636865651989 8651968905413092353077437)
      ·
        refine ⟨3244488339529909632404039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8651968905413092353077437 3244488339529909632404039)
        ·
          refine ⟨4866732509294864448606059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244488339529909632404039 4866732509294864448606059)
          ·
            refine ⟨7300098763942296672909089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866732509294864448606059 7300098763942296672909089)
            ·
              refine ⟨5475074072956722504681817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300098763942296672909089 5475074072956722504681817)
              ·
                refine ⟨4106305554717541878511363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475074072956722504681817 4106305554717541878511363)
                ·
                  refine ⟨6159458332076312817767045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106305554717541878511363 6159458332076312817767045)
                  ·
                    refine ⟨1154898437264308653331321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159458332076312817767045 1154898437264308653331321)
                    ·
                      rfl

theorem cell22_3373735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3373735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373735 prefixEnd_3373735 := by exact prefixLift 3373735
  have htrace : WordTrace (prefixWord ++ tailWord_3373735) baseStart_3373735 baseEnd_3373735 := by
    simpa [prefixWord, tailWord_3373735, baseEnd_3373735] using wordTrace_append hprefix tailTrace_3373735
  have hstable : (prefixWord ++ tailWord_3373735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373735).length < 2 ^ (prefixWord ++ tailWord_3373735).sum := by decide
  have hdescent : baseEnd_3373735 < baseStart_3373735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373804 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_3373804 : Nat := 118140960795 + 3373804 * 2 ^ 59
def prefixEnd_3373804 : Nat := 4983230072969 + 3 ^ 40 * 3373804 * 2
def baseEnd_3373804 : Nat := 1154922057374415473356109

theorem tailTrace_3373804 : CollatzResearch.WordTrace tailWord_3373804 prefixEnd_3373804 1154922057374415473356109 := by
  unfold tailWord_3373804
  simp only [CollatzResearch.WordTrace]
  refine ⟨61526370534645891347348233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82035160712861188463130977 61526370534645891347348233)
  ·
    refine ⟨46144777900984418510511175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61526370534645891347348233 46144777900984418510511175)
    ·
      refine ⟨69217166851476627765766763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46144777900984418510511175 69217166851476627765766763)
      ·
        refine ⟨103825750277214941648650145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69217166851476627765766763 103825750277214941648650145)
        ·
          refine ⟨77869312707911206236487609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103825750277214941648650145 77869312707911206236487609)
          ·
            refine ⟨58401984530933404677365707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77869312707911206236487609 58401984530933404677365707)
            ·
              refine ⟨87602976796400107016048561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58401984530933404677365707 87602976796400107016048561)
              ·
                refine ⟨65702232597300080262036421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87602976796400107016048561 65702232597300080262036421)
                ·
                  refine ⟨12319168611993765049131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65702232597300080262036421 12319168611993765049131829)
                  ·
                    refine ⟨1154922057374415473356109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12319168611993765049131829 1154922057374415473356109)
                    ·
                      rfl

theorem cell22_3373804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_3373804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373804 prefixEnd_3373804 := by exact prefixLift 3373804
  have htrace : WordTrace (prefixWord ++ tailWord_3373804) baseStart_3373804 baseEnd_3373804 := by
    simpa [prefixWord, tailWord_3373804, baseEnd_3373804] using wordTrace_append hprefix tailTrace_3373804
  have hstable : (prefixWord ++ tailWord_3373804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373804).length < 2 ^ (prefixWord ++ tailWord_3373804).sum := by decide
  have hdescent : baseEnd_3373804 < baseStart_3373804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373868 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 4]
def baseStart_3373868 : Nat := 118140960795 + 3373868 * 2 ^ 59
def prefixEnd_3373868 : Nat := 4983230072969 + 3 ^ 40 * 3373868 * 2
def baseEnd_3373868 : Nat := 384981321960780213251971

theorem tailTrace_3373868 : CollatzResearch.WordTrace tailWord_3373868 prefixEnd_3373868 384981321960780213251971 := by
  unfold tailWord_3373868
  simp only [CollatzResearch.WordTrace]
  refine ⟨61527537670529960812513129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82036716894039947750017505 61527537670529960812513129)
  ·
    refine ⟨46145653252897470609384847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61527537670529960812513129 46145653252897470609384847)
    ·
      refine ⟨69218479879346205914077271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46145653252897470609384847 69218479879346205914077271)
      ·
        refine ⟨103827719819019308871115907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69218479879346205914077271 103827719819019308871115907)
        ·
          refine ⟨155741579728528963306673861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103827719819019308871115907 155741579728528963306673861)
          ·
            refine ⟨29201546199099180620001349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155741579728528963306673861 29201546199099180620001349)
            ·
              refine ⟨5475289912331096366250253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29201546199099180620001349 5475289912331096366250253)
              ·
                refine ⟨2053233717124161137343845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5475289912331096366250253 2053233717124161137343845)
                ·
                  refine ⟨384981321960780213251971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053233717124161137343845 384981321960780213251971)
                  ·
                    rfl

theorem cell22_3373868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_3373868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373868 prefixEnd_3373868 := by exact prefixLift 3373868
  have htrace : WordTrace (prefixWord ++ tailWord_3373868) baseStart_3373868 baseEnd_3373868 := by
    simpa [prefixWord, tailWord_3373868, baseEnd_3373868] using wordTrace_append hprefix tailTrace_3373868
  have hstable : (prefixWord ++ tailWord_3373868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373868).length < 2 ^ (prefixWord ++ tailWord_3373868).sum := by decide
  have hdescent : baseEnd_3373868 < baseStart_3373868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373870 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3373870 : Nat := 118140960795 + 3373870 * 2 ^ 59
def prefixEnd_3373870 : Nat := 4983230072969 + 3 ^ 40 * 3373870 * 2
def baseEnd_3373870 : Nat := 1154944650523213301205907

theorem tailTrace_3373870 : CollatzResearch.WordTrace tailWord_3373870 prefixEnd_3373870 1154944650523213301205907 := by
  unfold tailWord_3373870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381893535881584495824883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82036765524701783977732709 15381893535881584495824883)
  ·
    refine ⟨23072840303822376743737325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15381893535881584495824883 23072840303822376743737325)
    ·
      refine ⟨8652315113933391278901497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23072840303822376743737325 8652315113933391278901497)
      ·
        refine ⟨6489236335450043459176123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8652315113933391278901497 6489236335450043459176123)
        ·
          refine ⟨9733854503175065188764185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489236335450043459176123 9733854503175065188764185)
          ·
            refine ⟨7300390877381298891573139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9733854503175065188764185 7300390877381298891573139)
            ·
              refine ⟨10950586316071948337359709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300390877381298891573139 10950586316071948337359709)
              ·
                refine ⟨4106469868526980626509891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10950586316071948337359709 4106469868526980626509891)
                ·
                  refine ⟨6159704802790470939764837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106469868526980626509891 6159704802790470939764837)
                  ·
                    refine ⟨1154944650523213301205907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159704802790470939764837 1154944650523213301205907)
                    ·
                      rfl

theorem cell22_3373870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3373870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373870 prefixEnd_3373870 := by exact prefixLift 3373870
  have htrace : WordTrace (prefixWord ++ tailWord_3373870) baseStart_3373870 baseEnd_3373870 := by
    simpa [prefixWord, tailWord_3373870, baseEnd_3373870] using wordTrace_append hprefix tailTrace_3373870
  have hstable : (prefixWord ++ tailWord_3373870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373870).length < 2 ^ (prefixWord ++ tailWord_3373870).sum := by decide
  have hdescent : baseEnd_3373870 < baseStart_3373870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373879 : List Nat := [1, 1, 3, 1, 2, 1, 13]
def baseStart_3373879 : Nat := 118140960795 + 3373879 * 2 ^ 59
def prefixEnd_3373879 : Nat := 4983230072969 + 3 ^ 40 * 3373879 * 2
def baseEnd_3373879 : Nat := 42775841903968158434477

theorem tailTrace_3373879 : CollatzResearch.WordTrace tailWord_3373879 prefixEnd_3373879 42775841903968158434477 := by
  unfold tailWord_3373879
  simp only [CollatzResearch.WordTrace]
  refine ⟨123055476544020070503676691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82036984362680047002451127 123055476544020070503676691)
  ·
    refine ⟨184583214816030105755515037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123055476544020070503676691 184583214816030105755515037)
    ·
      refine ⟨69218705556011289658318139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184583214816030105755515037 69218705556011289658318139)
      ·
        refine ⟨103828058334016934487477209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69218705556011289658318139 103828058334016934487477209)
        ·
          refine ⟨77871043750512700865607907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103828058334016934487477209 77871043750512700865607907)
          ·
            refine ⟨116806565625769051298411861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77871043750512700865607907 116806565625769051298411861)
            ·
              refine ⟨42775841903968158434477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 116806565625769051298411861 42775841903968158434477)
              ·
                rfl

theorem cell22_3373879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 13].length) (baseStart_3373879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373879 prefixEnd_3373879 := by exact prefixLift 3373879
  have htrace : WordTrace (prefixWord ++ tailWord_3373879) baseStart_3373879 baseEnd_3373879 := by
    simpa [prefixWord, tailWord_3373879, baseEnd_3373879] using wordTrace_append hprefix tailTrace_3373879
  have hstable : (prefixWord ++ tailWord_3373879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373879).length < 2 ^ (prefixWord ++ tailWord_3373879).sum := by decide
  have hdescent : baseEnd_3373879 < baseStart_3373879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373913 : List Nat := [1, 2, 1, 2, 2, 6, 2, 6]
def baseStart_3373913 : Nat := 118140960795 + 3373913 * 2 ^ 59
def prefixEnd_3373913 : Nat := 4983230072969 + 3 ^ 40 * 3373913 * 2
def baseEnd_3373913 : Nat := 128328818922441724708975

theorem tailTrace_3373913 : CollatzResearch.WordTrace tailWord_3373913 prefixEnd_3373913 128328818922441724708975 := by
  unfold tailWord_3373913
  simp only [CollatzResearch.WordTrace]
  refine ⟨123056716625896894310414393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82037811083931262873609595 123056716625896894310414393)
  ·
    refine ⟨92292537469422670732810795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123056716625896894310414393 92292537469422670732810795)
    ·
      refine ⟨138438806204134006099216193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92292537469422670732810795 138438806204134006099216193)
      ·
        refine ⟨103829104653100504574412145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138438806204134006099216193 103829104653100504574412145)
        ·
          refine ⟨77871828489825378430809109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103829104653100504574412145 77871828489825378430809109)
          ·
            refine ⟨3650241960460564613944177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77871828489825378430809109 3650241960460564613944177)
            ·
              refine ⟨2737681470345423460458133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3650241960460564613944177 2737681470345423460458133)
              ·
                refine ⟨128328818922441724708975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2737681470345423460458133 128328818922441724708975)
                ·
                  rfl

theorem cell22_3373913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 6].length) (baseStart_3373913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373913 prefixEnd_3373913 := by exact prefixLift 3373913
  have htrace : WordTrace (prefixWord ++ tailWord_3373913) baseStart_3373913 baseEnd_3373913 := by
    simpa [prefixWord, tailWord_3373913, baseEnd_3373913] using wordTrace_append hprefix tailTrace_3373913
  have hstable : (prefixWord ++ tailWord_3373913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373913).length < 2 ^ (prefixWord ++ tailWord_3373913).sum := by decide
  have hdescent : baseEnd_3373913 < baseStart_3373913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373945 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_3373945 : Nat := 118140960795 + 3373945 * 2 ^ 59
def prefixEnd_3373945 : Nat := 4983230072969 + 3 ^ 40 * 3373945 * 2
def baseEnd_3373945 : Nat := 1154970324555938105580677

theorem tailTrace_3373945 : CollatzResearch.WordTrace tailWord_3373945 prefixEnd_3373945 1154970324555938105580677 := by
  unfold tailWord_3373945
  simp only [CollatzResearch.WordTrace]
  refine ⟨123057883761780963775579289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82038589174520642517052859 123057883761780963775579289)
  ·
    refine ⟨92293412821335722831684467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123057883761780963775579289 92293412821335722831684467)
    ·
      refine ⟨138440119232003584247526701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92293412821335722831684467 138440119232003584247526701)
      ·
        refine ⟨51915044712001344092822513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138440119232003584247526701 51915044712001344092822513)
        ·
          refine ⟨38936283534001008069616885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51915044712001344092822513 38936283534001008069616885)
          ·
            refine ⟨3650276581312594506526583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38936283534001008069616885 3650276581312594506526583)
            ·
              refine ⟨5475414871968891759789875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650276581312594506526583 5475414871968891759789875)
              ·
                refine ⟨8213122307953337639684813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475414871968891759789875 8213122307953337639684813)
                ·
                  refine ⟨3079920865482501614881805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8213122307953337639684813 3079920865482501614881805)
                  ·
                    refine ⟨1154970324555938105580677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079920865482501614881805 1154970324555938105580677)
                    ·
                      rfl

theorem cell22_3373945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_3373945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373945 prefixEnd_3373945 := by exact prefixLift 3373945
  have htrace : WordTrace (prefixWord ++ tailWord_3373945) baseStart_3373945 baseEnd_3373945 := by
    simpa [prefixWord, tailWord_3373945, baseEnd_3373945] using wordTrace_append hprefix tailTrace_3373945
  have hstable : (prefixWord ++ tailWord_3373945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373945).length < 2 ^ (prefixWord ++ tailWord_3373945).sum := by decide
  have hdescent : baseEnd_3373945 < baseStart_3373945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373956 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3373956 : Nat := 118140960795 + 3373956 * 2 ^ 59
def prefixEnd_3373956 : Nat := 4983230072969 + 3 ^ 40 * 3373956 * 2
def baseEnd_3373956 : Nat := 1154974090080737743555643

theorem tailTrace_3373956 : CollatzResearch.WordTrace tailWord_3373956 prefixEnd_3373956 1154974090080737743555643 := by
  unfold tailWord_3373956
  simp only [CollatzResearch.WordTrace]
  refine ⟨61529142482370556327114861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82038856643160741769486481 61529142482370556327114861)
  ·
    refine ⟨23073428430888958622668073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61529142482370556327114861 23073428430888958622668073)
    ·
      refine ⟨17305071323166718967001055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23073428430888958622668073 17305071323166718967001055)
      ·
        refine ⟨25957606984750078450501583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17305071323166718967001055 25957606984750078450501583)
        ·
          refine ⟨38936410477125117675752375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25957606984750078450501583 38936410477125117675752375)
          ·
            refine ⟨58404615715687676513628563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38936410477125117675752375 58404615715687676513628563)
            ·
              refine ⟨87606923573531514770442845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58404615715687676513628563 87606923573531514770442845)
              ·
                refine ⟨32852596340074318038916067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87606923573531514770442845 32852596340074318038916067)
                ·
                  refine ⟨49278894510111477058374101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32852596340074318038916067 49278894510111477058374101)
                  ·
                    refine ⟨1154974090080737743555643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49278894510111477058374101 1154974090080737743555643)
                    ·
                      rfl

theorem cell22_3373956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3373956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3373956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3373956 prefixEnd_3373956 := by exact prefixLift 3373956
  have htrace : WordTrace (prefixWord ++ tailWord_3373956) baseStart_3373956 baseEnd_3373956 := by
    simpa [prefixWord, tailWord_3373956, baseEnd_3373956] using wordTrace_append hprefix tailTrace_3373956
  have hstable : (prefixWord ++ tailWord_3373956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373956).length < 2 ^ (prefixWord ++ tailWord_3373956).sum := by decide
  have hdescent : baseEnd_3373956 < baseStart_3373956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374037 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 4]
def baseStart_3374037 : Nat := 118140960795 + 3374037 * 2 ^ 59
def prefixEnd_3374037 : Nat := 4983230072969 + 3 ^ 40 * 3374037 * 2
def baseEnd_3374037 : Nat := 385000606012026844093465

theorem tailTrace_3374037 : CollatzResearch.WordTrace tailWord_3374037 prefixEnd_3374037 385000606012026844093465 := by
  unfold tailWord_3374037
  simp only [CollatzResearch.WordTrace]
  refine ⟨123061239277447663487928365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82040826184965108991952243 123061239277447663487928365)
  ·
    refine ⟨46147964729042873807973137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123061239277447663487928365 46147964729042873807973137)
    ·
      refine ⟨34610973546782155355979853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46147964729042873807973137 34610973546782155355979853)
      ·
        refine ⟨12979115080043308258492445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34610973546782155355979853 12979115080043308258492445)
        ·
          refine ⟨4867168155016240596934667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12979115080043308258492445 4867168155016240596934667)
          ·
            refine ⟨7300752232524360895402001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4867168155016240596934667 7300752232524360895402001)
            ·
              refine ⟨5475564174393270671551501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300752232524360895402001 5475564174393270671551501)
              ·
                refine ⟨2053336565397476501831813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5475564174393270671551501 2053336565397476501831813)
                ·
                  refine ⟨385000606012026844093465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053336565397476501831813 385000606012026844093465)
                  ·
                    rfl

theorem cell22_3374037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_3374037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374037 prefixEnd_3374037 := by exact prefixLift 3374037
  have htrace : WordTrace (prefixWord ++ tailWord_3374037) baseStart_3374037 baseEnd_3374037 := by
    simpa [prefixWord, tailWord_3374037, baseEnd_3374037] using wordTrace_append hprefix tailTrace_3374037
  have hstable : (prefixWord ++ tailWord_3374037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374037).length < 2 ^ (prefixWord ++ tailWord_3374037).sum := by decide
  have hdescent : baseEnd_3374037 < baseStart_3374037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374069 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3374069 : Nat := 118140960795 + 3374069 * 2 ^ 59
def prefixEnd_3374069 : Nat := 4983230072969 + 3 ^ 40 * 3374069 * 2
def baseEnd_3374069 : Nat := 1155012772290043115480297

theorem tailTrace_3374069 : CollatzResearch.WordTrace tailWord_3374069 prefixEnd_3374069 1155012772290043115480297 := by
  unfold tailWord_3374069
  simp only [CollatzResearch.WordTrace]
  refine ⟨123062406413331732953093261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82041604275554488635395507 123062406413331732953093261)
  ·
    refine ⟨46148402404999399857409973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123062406413331732953093261 46148402404999399857409973)
    ·
      refine ⟨4326412725468693736632185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46148402404999399857409973 4326412725468693736632185)
      ·
        refine ⟨3244809544101520302474139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4326412725468693736632185 3244809544101520302474139)
        ·
          refine ⟨4867214316152280453711209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244809544101520302474139 4867214316152280453711209)
          ·
            refine ⟨3650410737114210340283407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4867214316152280453711209 3650410737114210340283407)
            ·
              refine ⟨5475616105671315510425111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650410737114210340283407 5475616105671315510425111)
              ·
                refine ⟨8213424158506973265637667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475616105671315510425111 8213424158506973265637667)
                ·
                  refine ⟨12320136237760459898456501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8213424158506973265637667 12320136237760459898456501)
                  ·
                    refine ⟨1155012772290043115480297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12320136237760459898456501 1155012772290043115480297)
                    ·
                      rfl

theorem cell22_3374069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3374069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374069 prefixEnd_3374069 := by exact prefixLift 3374069
  have htrace : WordTrace (prefixWord ++ tailWord_3374069) baseStart_3374069 baseEnd_3374069 := by
    simpa [prefixWord, tailWord_3374069, baseEnd_3374069] using wordTrace_append hprefix tailTrace_3374069
  have hstable : (prefixWord ++ tailWord_3374069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374069).length < 2 ^ (prefixWord ++ tailWord_3374069).sum := by decide
  have hdescent : baseEnd_3374069 < baseStart_3374069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374082 : List Nat := [3, 4, 1, 3, 1, 1, 1, 8]
def baseStart_3374082 : Nat := 118140960795 + 3374082 * 2 ^ 59
def prefixEnd_3374082 : Nat := 4983230072969 + 3 ^ 40 * 3374082 * 2
def baseEnd_3374082 : Nat := 128335246939523934989473

theorem tailTrace_3374082 : CollatzResearch.WordTrace tailWord_3374082 prefixEnd_3374082 128335246939523934989473 := by
  unfold tailWord_3374082
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765720140571159043329125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82041920374856424115544333 30765720140571159043329125)
  ·
    refine ⟨5768572526357092320624211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30765720140571159043329125 5768572526357092320624211)
    ·
      refine ⟨8652858789535638480936317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5768572526357092320624211 8652858789535638480936317)
      ·
        refine ⟨3244822046075864430351119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8652858789535638480936317 3244822046075864430351119)
        ·
          refine ⟨4867233069113796645526679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244822046075864430351119 4867233069113796645526679)
          ·
            refine ⟨7300849603670694968290019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4867233069113796645526679 7300849603670694968290019)
            ·
              refine ⟨10951274405506042452435029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300849603670694968290019 10951274405506042452435029)
              ·
                refine ⟨128335246939523934989473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10951274405506042452435029 128335246939523934989473)
                ·
                  rfl

theorem cell22_3374082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_3374082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374082 prefixEnd_3374082 := by exact prefixLift 3374082
  have htrace : WordTrace (prefixWord ++ tailWord_3374082) baseStart_3374082 baseEnd_3374082 := by
    simpa [prefixWord, tailWord_3374082, baseEnd_3374082] using wordTrace_append hprefix tailTrace_3374082
  have hstable : (prefixWord ++ tailWord_3374082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374082).length < 2 ^ (prefixWord ++ tailWord_3374082).sum := by decide
  have hdescent : baseEnd_3374082 < baseStart_3374082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374123 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 3, 4]
def baseStart_3374123 : Nat := 118140960795 + 3374123 * 2 ^ 59
def prefixEnd_3374123 : Nat := 4983230072969 + 3 ^ 40 * 3374123 * 2
def baseEnd_3374123 : Nat := 1155031257593604974630131

theorem tailTrace_3374123 : CollatzResearch.WordTrace tailWord_3374123 prefixEnd_3374123 1155031257593604974630131 := by
  unfold tailWord_3374123
  simp only [CollatzResearch.WordTrace]
  refine ⟨123064375955136100175559023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82042917303424066783706015 123064375955136100175559023)
  ·
    refine ⟨184596563932704150263338535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123064375955136100175559023 184596563932704150263338535)
    ·
      refine ⟨276894845899056225395007803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184596563932704150263338535 276894845899056225395007803)
      ·
        refine ⟨415342268848584338092511705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276894845899056225395007803 415342268848584338092511705)
        ·
          refine ⟨311506701636438253569383779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415342268848584338092511705 311506701636438253569383779)
          ·
            refine ⟨467260052454657380354075669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311506701636438253569383779 467260052454657380354075669)
            ·
              refine ⟨21902814958812064704097297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467260052454657380354075669 21902814958812064704097297)
              ·
                refine ⟨16427111219109048528072973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21902814958812064704097297 16427111219109048528072973)
                ·
                  refine ⟨6160166707165893198027365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16427111219109048528072973 6160166707165893198027365)
                  ·
                    refine ⟨1155031257593604974630131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160166707165893198027365 1155031257593604974630131)
                    ·
                      rfl

theorem cell22_3374123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_3374123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374123 prefixEnd_3374123 := by exact prefixLift 3374123
  have htrace : WordTrace (prefixWord ++ tailWord_3374123) baseStart_3374123 baseEnd_3374123 := by
    simpa [prefixWord, tailWord_3374123, baseEnd_3374123] using wordTrace_append hprefix tailTrace_3374123
  have hstable : (prefixWord ++ tailWord_3374123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374123).length < 2 ^ (prefixWord ++ tailWord_3374123).sum := by decide
  have hdescent : baseEnd_3374123 < baseStart_3374123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374138 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_3374138 : Nat := 118140960795 + 3374138 * 2 ^ 59
def prefixEnd_3374138 : Nat := 4983230072969 + 3 ^ 40 * 3374138 * 2
def baseEnd_3374138 : Nat := 385012130800049978501695

theorem tailTrace_3374138 : CollatzResearch.WordTrace tailWord_3374138 prefixEnd_3374138 385012130800049978501695 := by
  unfold tailWord_3374138
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766230762520439434338767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82043282033387838491570045 30766230762520439434338767)
  ·
    refine ⟨46149346143780659151508151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30766230762520439434338767 46149346143780659151508151)
    ·
      refine ⟨69224019215670988727262227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46149346143780659151508151 69224019215670988727262227)
      ·
        refine ⟨103836028823506483090893341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69224019215670988727262227 103836028823506483090893341)
        ·
          refine ⟨38938510808814931159085003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103836028823506483090893341 38938510808814931159085003)
          ·
            refine ⟨58407766213222396738627505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38938510808814931159085003 58407766213222396738627505)
            ·
              refine ⟨43805824659916797553970629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58407766213222396738627505 43805824659916797553970629)
              ·
                refine ⟨8213592123734399541369493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43805824659916797553970629 8213592123734399541369493)
                ·
                  refine ⟨385012130800049978501695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8213592123734399541369493 385012130800049978501695)
                  ·
                    rfl

theorem cell22_3374138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_3374138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374138 prefixEnd_3374138 := by exact prefixLift 3374138
  have htrace : WordTrace (prefixWord ++ tailWord_3374138) baseStart_3374138 baseEnd_3374138 := by
    simpa [prefixWord, tailWord_3374138, baseEnd_3374138] using wordTrace_append hprefix tailTrace_3374138
  have hstable : (prefixWord ++ tailWord_3374138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374138).length < 2 ^ (prefixWord ++ tailWord_3374138).sum := by decide
  have hdescent : baseEnd_3374138 < baseStart_3374138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374140 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3374140 : Nat := 118140960795 + 3374140 * 2 ^ 59
def prefixEnd_3374140 : Nat := 4983230072969 + 3 ^ 40 * 3374140 * 2
def baseEnd_3374140 : Nat := 1155037077041022596955079

theorem tailTrace_3374140 : CollatzResearch.WordTrace tailWord_3374140 prefixEnd_3374140 1155037077041022596955079 := by
  unfold tailWord_3374140
  simp only [CollatzResearch.WordTrace]
  refine ⟨61532497998037256039463937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82043330664049674719285249 61532497998037256039463937)
  ·
    refine ⟨46149373498527942029597953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61532497998037256039463937 46149373498527942029597953)
    ·
      refine ⟨34612030123895956522198465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46149373498527942029597953 34612030123895956522198465)
      ·
        refine ⟨25959022592921967391648849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34612030123895956522198465 25959022592921967391648849)
        ·
          refine ⟨19469266944691475543736637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25959022592921967391648849 19469266944691475543736637)
          ·
            refine ⟨7300975104259303328901239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19469266944691475543736637 7300975104259303328901239)
            ·
              refine ⟨10951462656388954993351859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300975104259303328901239 10951462656388954993351859)
              ·
                refine ⟨16427193984583432490027789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10951462656388954993351859 16427193984583432490027789)
                ·
                  refine ⟨6160197744218787183760421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16427193984583432490027789 6160197744218787183760421)
                  ·
                    refine ⟨1155037077041022596955079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160197744218787183760421 1155037077041022596955079)
                    ·
                      rfl

theorem cell22_3374140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3374140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374140 prefixEnd_3374140 := by exact prefixLift 3374140
  have htrace : WordTrace (prefixWord ++ tailWord_3374140) baseStart_3374140 baseEnd_3374140 := by
    simpa [prefixWord, tailWord_3374140, baseEnd_3374140] using wordTrace_append hprefix tailTrace_3374140
  have hstable : (prefixWord ++ tailWord_3374140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374140).length < 2 ^ (prefixWord ++ tailWord_3374140).sum := by decide
  have hdescent : baseEnd_3374140 < baseStart_3374140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374172 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 4]
def baseStart_3374172 : Nat := 118140960795 + 3374172 * 2 ^ 59
def prefixEnd_3374172 : Nat := 4983230072969 + 3 ^ 40 * 3374172 * 2
def baseEnd_3374172 : Nat := 385016010431661726718327

theorem tailTrace_3374172 : CollatzResearch.WordTrace tailWord_3374172 prefixEnd_3374172 385016010431661726718327 := by
  unfold tailWord_3374172
  simp only [CollatzResearch.WordTrace]
  refine ⟨61533081565979290772046385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82044108754639054362728513 61533081565979290772046385)
  ·
    refine ⟨46149811174484468079034789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61533081565979290772046385 46149811174484468079034789)
    ·
      refine ⟨8653089595215837764819023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46149811174484468079034789 8653089595215837764819023)
      ·
        refine ⟨12979634392823756647228535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8653089595215837764819023 12979634392823756647228535)
        ·
          refine ⟨19469451589235634970842803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12979634392823756647228535 19469451589235634970842803)
          ·
            refine ⟨29204177383853452456264205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19469451589235634970842803 29204177383853452456264205)
            ·
              refine ⟨10951566518945044671099077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29204177383853452456264205 10951566518945044671099077)
              ·
                refine ⟨2053418722302195875831077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10951566518945044671099077 2053418722302195875831077)
                ·
                  refine ⟨385016010431661726718327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053418722302195875831077 385016010431661726718327)
                  ·
                    rfl

theorem cell22_3374172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_3374172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374172 prefixEnd_3374172 := by exact prefixLift 3374172
  have htrace : WordTrace (prefixWord ++ tailWord_3374172) baseStart_3374172 baseEnd_3374172 := by
    simpa [prefixWord, tailWord_3374172, baseEnd_3374172] using wordTrace_append hprefix tailTrace_3374172
  have hstable : (prefixWord ++ tailWord_3374172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374172).length < 2 ^ (prefixWord ++ tailWord_3374172).sum := by decide
  have hdescent : baseEnd_3374172 < baseStart_3374172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374174 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3374174 : Nat := 118140960795 + 3374174 * 2 ^ 59
def prefixEnd_3374174 : Nat := 4983230072969 + 3 ^ 40 * 3374174 * 2
def baseEnd_3374174 : Nat := 1155048715935857841604975

theorem tailTrace_3374174 : CollatzResearch.WordTrace tailWord_3374174 prefixEnd_3374174 1155048715935857841604975 := by
  unfold tailWord_3374174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383279509743916985708197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82044157385300890590443717 15383279509743916985708197)
  ·
    refine ⟨2884364908076984434820287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15383279509743916985708197 2884364908076984434820287)
    ·
      refine ⟨4326547362115476652230431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884364908076984434820287 4326547362115476652230431)
      ·
        refine ⟨6489821043173214978345647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326547362115476652230431 6489821043173214978345647)
        ·
          refine ⟨9734731564759822467518471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489821043173214978345647 9734731564759822467518471)
          ·
            refine ⟨14602097347139733701277707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734731564759822467518471 14602097347139733701277707)
            ·
              refine ⟨21903146020709600551916561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14602097347139733701277707 21903146020709600551916561)
              ·
                refine ⟨16427359515532200413937421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21903146020709600551916561 16427359515532200413937421)
                ·
                  refine ⟨6160259818324575155226533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16427359515532200413937421 6160259818324575155226533)
                  ·
                    refine ⟨1155048715935857841604975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160259818324575155226533 1155048715935857841604975)
                    ·
                      rfl

theorem cell22_3374174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3374174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374174 prefixEnd_3374174 := by exact prefixLift 3374174
  have htrace : WordTrace (prefixWord ++ tailWord_3374174) baseStart_3374174 baseEnd_3374174 := by
    simpa [prefixWord, tailWord_3374174, baseEnd_3374174] using wordTrace_append hprefix tailTrace_3374174
  have hstable : (prefixWord ++ tailWord_3374174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374174).length < 2 ^ (prefixWord ++ tailWord_3374174).sum := by decide
  have hdescent : baseEnd_3374174 < baseStart_3374174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374215 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3374215 : Nat := 118140960795 + 3374215 * 2 ^ 59
def prefixEnd_3374215 : Nat := 4983230072969 + 3 ^ 40 * 3374215 * 2
def baseEnd_3374215 : Nat := 1155062751073747401329849

theorem tailTrace_3374215 : CollatzResearch.WordTrace tailWord_3374215 prefixEnd_3374215 1155062751073747401329849 := by
  unfold tailWord_3374215
  simp only [CollatzResearch.WordTrace]
  refine ⟨123067731470802799887908099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82045154313868533258605399 123067731470802799887908099)
  ·
    refine ⟨184601597206204199831862149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123067731470802799887908099 184601597206204199831862149)
    ·
      refine ⟨34612799476163287468474153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184601597206204199831862149 34612799476163287468474153)
      ·
        refine ⟨25959599607122465601355615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34612799476163287468474153 25959599607122465601355615)
        ·
          refine ⟨38939399410683698402033423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25959599607122465601355615 38939399410683698402033423)
          ·
            refine ⟨58409099116025547603050135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38939399410683698402033423 58409099116025547603050135)
            ·
              refine ⟨87613648674038321404575203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58409099116025547603050135 87613648674038321404575203)
              ·
                refine ⟨131420473011057482106862805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87613648674038321404575203 131420473011057482106862805)
                ·
                  refine ⟨3080167336196659736879597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 131420473011057482106862805 3080167336196659736879597)
                  ·
                    refine ⟨1155062751073747401329849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080167336196659736879597 1155062751073747401329849)
                    ·
                      rfl

theorem cell22_3374215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3374215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374215 prefixEnd_3374215 := by exact prefixLift 3374215
  have htrace : WordTrace (prefixWord ++ tailWord_3374215) baseStart_3374215 baseEnd_3374215 := by
    simpa [prefixWord, tailWord_3374215, baseEnd_3374215] using wordTrace_append hprefix tailTrace_3374215
  have hstable : (prefixWord ++ tailWord_3374215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374215).length < 2 ^ (prefixWord ++ tailWord_3374215).sum := by decide
  have hdescent : baseEnd_3374215 < baseStart_3374215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374232 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_3374232 : Nat := 118140960795 + 3374232 * 2 ^ 59
def prefixEnd_3374232 : Nat := 4983230072969 + 3 ^ 40 * 3374232 * 2
def baseEnd_3374232 : Nat := 1155068570521165023654797

theorem tailTrace_3374232 : CollatzResearch.WordTrace tailWord_3374232 prefixEnd_3374232 1155068570521165023654797 := by
  unfold tailWord_3374232
  simp only [CollatzResearch.WordTrace]
  refine ⟨61534175755870605895638475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82045567674494141194184633 61534175755870605895638475)
  ·
    refine ⟨92301263633805908843457713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61534175755870605895638475 92301263633805908843457713)
    ·
      refine ⟨69225947725354431632593285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92301263633805908843457713 69225947725354431632593285)
      ·
        refine ⟨12979865198503955931111241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69225947725354431632593285 12979865198503955931111241)
        ·
          refine ⟨9734898898877966948333431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12979865198503955931111241 9734898898877966948333431)
          ·
            refine ⟨14602348348316950422500147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734898898877966948333431 14602348348316950422500147)
            ·
              refine ⟨21903522522475425633750221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14602348348316950422500147 21903522522475425633750221)
              ·
                refine ⟨8213820945928284612656333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21903522522475425633750221 8213820945928284612656333)
                ·
                  refine ⟨3080182854723106729746125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8213820945928284612656333 3080182854723106729746125)
                  ·
                    refine ⟨1155068570521165023654797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080182854723106729746125 1155068570521165023654797)
                    ·
                      rfl

theorem cell22_3374232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_3374232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374232 prefixEnd_3374232 := by exact prefixLift 3374232
  have htrace : WordTrace (prefixWord ++ tailWord_3374232) baseStart_3374232 baseEnd_3374232 := by
    simpa [prefixWord, tailWord_3374232, baseEnd_3374232] using wordTrace_append hprefix tailTrace_3374232
  have hstable : (prefixWord ++ tailWord_3374232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374232).length < 2 ^ (prefixWord ++ tailWord_3374232).sum := by decide
  have hdescent : baseEnd_3374232 < baseStart_3374232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374296 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 5]
def baseStart_3374296 : Nat := 118140960795 + 3374296 * 2 ^ 59
def prefixEnd_3374296 : Nat := 4983230072969 + 3 ^ 40 * 3374296 * 2
def baseEnd_3374296 : Nat := 385030159676363396684867

theorem tailTrace_3374296 : CollatzResearch.WordTrace tailWord_3374296 prefixEnd_3374296 385030159676363396684867 := by
  unfold tailWord_3374296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61535342891754675360803371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82047123855672900481071161 61535342891754675360803371)
  ·
    refine ⟨92303014337632013041205057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61535342891754675360803371 92303014337632013041205057)
    ·
      refine ⟨69227260753224009780903793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92303014337632013041205057 69227260753224009780903793)
      ·
        refine ⟨51920445564918007335677845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69227260753224009780903793 51920445564918007335677845)
        ·
          refine ⟨2433770885855531593859899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51920445564918007335677845 2433770885855531593859899)
          ·
            refine ⟨3650656328783297390789849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433770885855531593859899 3650656328783297390789849)
            ·
              refine ⟨2737992246587473043092387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3650656328783297390789849 2737992246587473043092387)
              ·
                refine ⟨4106988369881209564638581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737992246587473043092387 4106988369881209564638581)
                ·
                  refine ⟨385030159676363396684867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4106988369881209564638581 385030159676363396684867)
                  ·
                    rfl

theorem cell22_3374296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_3374296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374296 prefixEnd_3374296 := by exact prefixLift 3374296
  have htrace : WordTrace (prefixWord ++ tailWord_3374296) baseStart_3374296 baseEnd_3374296 := by
    simpa [prefixWord, tailWord_3374296, baseEnd_3374296] using wordTrace_append hprefix tailTrace_3374296
  have hstable : (prefixWord ++ tailWord_3374296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374296).length < 2 ^ (prefixWord ++ tailWord_3374296).sum := by decide
  have hdescent : baseEnd_3374296 < baseStart_3374296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374337 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3374337 : Nat := 118140960795 + 3374337 * 2 ^ 59
def prefixEnd_3374337 : Nat := 4983230072969 + 3 ^ 40 * 3374337 * 2
def baseEnd_3374337 : Nat := 1155104514166979749779475

theorem tailTrace_3374337 : CollatzResearch.WordTrace tailWord_3374337 prefixEnd_3374337 1155104514166979749779475 := by
  unfold tailWord_3374337
  simp only [CollatzResearch.WordTrace]
  refine ⟨123072181176360814723849265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82048120784240543149232843 123072181176360814723849265)
  ·
    refine ⟨92304135882270611042886949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123072181176360814723849265 92304135882270611042886949)
    ·
      refine ⟨17307025477925739570541303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92304135882270611042886949 17307025477925739570541303)
      ·
        refine ⟨25960538216888609355811955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17307025477925739570541303 25960538216888609355811955)
        ·
          refine ⟨38940807325332914033717933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25960538216888609355811955 38940807325332914033717933)
          ·
            refine ⟨14602802746999842762644225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38940807325332914033717933 14602802746999842762644225)
            ·
              refine ⟨10952102060249882071983169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14602802746999842762644225 10952102060249882071983169)
              ·
                refine ⟨8214076545187411553987377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10952102060249882071983169 8214076545187411553987377)
                ·
                  refine ⟨6160557408890558665490533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8214076545187411553987377 6160557408890558665490533)
                  ·
                    refine ⟨1155104514166979749779475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160557408890558665490533 1155104514166979749779475)
                    ·
                      rfl

theorem cell22_3374337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3374337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374337 prefixEnd_3374337 := by exact prefixLift 3374337
  have htrace : WordTrace (prefixWord ++ tailWord_3374337) baseStart_3374337 baseEnd_3374337 := by
    simpa [prefixWord, tailWord_3374337, baseEnd_3374337] using wordTrace_append hprefix tailTrace_3374337
  have hstable : (prefixWord ++ tailWord_3374337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374337).length < 2 ^ (prefixWord ++ tailWord_3374337).sum := by decide
  have hdescent : baseEnd_3374337 < baseStart_3374337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374339 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 2, 3]
def baseStart_3374339 : Nat := 118140960795 + 3374339 * 2 ^ 59
def prefixEnd_3374339 : Nat := 4983230072969 + 3 ^ 40 * 3374339 * 2
def baseEnd_3374339 : Nat := 1155105198807852411229469

theorem tailTrace_3374339 : CollatzResearch.WordTrace tailWord_3374339 prefixEnd_3374339 1155105198807852411229469 := by
  unfold tailWord_3374339
  simp only [CollatzResearch.WordTrace]
  refine ⟨123072254122353569065422071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82048169414902379376948047 123072254122353569065422071)
  ·
    refine ⟨184608381183530353598133107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123072254122353569065422071 184608381183530353598133107)
    ·
      refine ⟨276912571775295530397199661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184608381183530353598133107 276912571775295530397199661)
      ·
        refine ⟨103842214415735823898949873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276912571775295530397199661 103842214415735823898949873)
        ·
          refine ⟨77881660811801867924212405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103842214415735823898949873 77881660811801867924212405)
          ·
            refine ⟨7301405701106425117894913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77881660811801867924212405 7301405701106425117894913)
            ·
              refine ⟨5476054275829818838421185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7301405701106425117894913 5476054275829818838421185)
              ·
                refine ⟨4107040706872364128815889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476054275829818838421185 4107040706872364128815889)
                ·
                  refine ⟨3080280530154273096611917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107040706872364128815889 3080280530154273096611917)
                  ·
                    refine ⟨1155105198807852411229469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080280530154273096611917 1155105198807852411229469)
                    ·
                      rfl

theorem cell22_3374339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 3].length) (baseStart_3374339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374339 prefixEnd_3374339 := by exact prefixLift 3374339
  have htrace : WordTrace (prefixWord ++ tailWord_3374339) baseStart_3374339 baseEnd_3374339 := by
    simpa [prefixWord, tailWord_3374339, baseEnd_3374339] using wordTrace_append hprefix tailTrace_3374339
  have hstable : (prefixWord ++ tailWord_3374339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374339).length < 2 ^ (prefixWord ++ tailWord_3374339).sum := by decide
  have hdescent : baseEnd_3374339 < baseStart_3374339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374380 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_3374380 : Nat := 118140960795 + 3374380 * 2 ^ 59
def prefixEnd_3374380 : Nat := 4983230072969 + 3 ^ 40 * 3374380 * 2
def baseEnd_3374380 : Nat := 385039744648580656984781

theorem tailTrace_3374380 : CollatzResearch.WordTrace tailWord_3374380 prefixEnd_3374380 385039744648580656984781 := by
  unfold tailWord_3374380
  simp only [CollatzResearch.WordTrace]
  refine ⟨61536874757602516533832297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82049166343470022045109729 61536874757602516533832297)
  ·
    refine ⟨46152656068201887400374223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61536874757602516533832297 46152656068201887400374223)
    ·
      refine ⟨69228984102302831100561335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46152656068201887400374223 69228984102302831100561335)
      ·
        refine ⟨103843476153454246650842003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69228984102302831100561335 103843476153454246650842003)
        ·
          refine ⟨155765214230181369976263005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103843476153454246650842003 155765214230181369976263005)
          ·
            refine ⟨58411955336318013741098627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155765214230181369976263005 58411955336318013741098627)
            ·
              refine ⟨87617933004477020611647941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58411955336318013741098627 87617933004477020611647941)
              ·
                refine ⟨16428362438339441364683989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87617933004477020611647941 16428362438339441364683989)
                ·
                  refine ⟨385039744648580656984781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16428362438339441364683989 385039744648580656984781)
                  ·
                    rfl

theorem cell22_3374380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_3374380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374380 prefixEnd_3374380 := by exact prefixLift 3374380
  have htrace : WordTrace (prefixWord ++ tailWord_3374380) baseStart_3374380 baseEnd_3374380 := by
    simpa [prefixWord, tailWord_3374380, baseEnd_3374380] using wordTrace_append hprefix tailTrace_3374380
  have hstable : (prefixWord ++ tailWord_3374380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374380).length < 2 ^ (prefixWord ++ tailWord_3374380).sum := by decide
  have hdescent : baseEnd_3374380 < baseStart_3374380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374390 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3374390 : Nat := 118140960795 + 3374390 * 2 ^ 59
def prefixEnd_3374390 : Nat := 4983230072969 + 3 ^ 40 * 3374390 * 2
def baseEnd_3374390 : Nat := 1155122657150105278204313

theorem tailTrace_3374390 : CollatzResearch.WordTrace tailWord_3374390 prefixEnd_3374390 1155122657150105278204313 := by
  unfold tailWord_3374390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692132140323050298470539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82049409496779203183685749 7692132140323050298470539)
  ·
    refine ⟨11538198210484575447705809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7692132140323050298470539 11538198210484575447705809)
    ·
      refine ⟨8653648657863431585779357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11538198210484575447705809 8653648657863431585779357)
      ·
        refine ⟨3245118246698786844667259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8653648657863431585779357 3245118246698786844667259)
        ·
          refine ⟨4867677370048180267000889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245118246698786844667259 4867677370048180267000889)
          ·
            refine ⟨3650758027536135200250667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4867677370048180267000889 3650758027536135200250667)
            ·
              refine ⟨5476137041304202800376001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650758027536135200250667 5476137041304202800376001)
              ·
                refine ⟨4107102780978152100282001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476137041304202800376001 4107102780978152100282001)
                ·
                  refine ⟨3080327085733614075211501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107102780978152100282001 3080327085733614075211501)
                  ·
                    refine ⟨1155122657150105278204313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080327085733614075211501 1155122657150105278204313)
                    ·
                      rfl

theorem cell22_3374390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3374390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374390 prefixEnd_3374390 := by exact prefixLift 3374390
  have htrace : WordTrace (prefixWord ++ tailWord_3374390) baseStart_3374390 baseEnd_3374390 := by
    simpa [prefixWord, tailWord_3374390, baseEnd_3374390] using wordTrace_append hprefix tailTrace_3374390
  have hstable : (prefixWord ++ tailWord_3374390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374390).length < 2 ^ (prefixWord ++ tailWord_3374390).sum := by decide
  have hdescent : baseEnd_3374390 < baseStart_3374390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374401 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3374401 : Nat := 118140960795 + 3374401 * 2 ^ 59
def prefixEnd_3374401 : Nat := 4983230072969 + 3 ^ 40 * 3374401 * 2
def baseEnd_3374401 : Nat := 1155126422674904916179279

theorem tailTrace_3374401 : CollatzResearch.WordTrace tailWord_3374401 prefixEnd_3374401 1155126422674904916179279 := by
  unfold tailWord_3374401
  simp only [CollatzResearch.WordTrace]
  refine ⟨123074515448128953654179057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82049676965419302436119371 123074515448128953654179057)
  ·
    refine ⟨92305886586096715240634293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123074515448128953654179057 92305886586096715240634293)
    ·
      refine ⟨8653676867446567053809465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92305886586096715240634293 8653676867446567053809465)
      ·
        refine ⟨6490257650584925290357099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8653676867446567053809465 6490257650584925290357099)
        ·
          refine ⟨9735386475877387935535649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490257650584925290357099 9735386475877387935535649)
          ·
            refine ⟨7301539856908040951651737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9735386475877387935535649 7301539856908040951651737)
            ·
              refine ⟨5476154892681030713738803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7301539856908040951651737 5476154892681030713738803)
              ·
                refine ⟨8214232339021546070608205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476154892681030713738803 8214232339021546070608205)
                ·
                  refine ⟨3080337127133079776478077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8214232339021546070608205 3080337127133079776478077)
                  ·
                    refine ⟨1155126422674904916179279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080337127133079776478077 1155126422674904916179279)
                    ·
                      rfl

theorem cell22_3374401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3374401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374401 prefixEnd_3374401 := by exact prefixLift 3374401
  have htrace : WordTrace (prefixWord ++ tailWord_3374401) baseStart_3374401 baseEnd_3374401 := by
    simpa [prefixWord, tailWord_3374401, baseEnd_3374401] using wordTrace_append hprefix tailTrace_3374401
  have hstable : (prefixWord ++ tailWord_3374401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374401).length < 2 ^ (prefixWord ++ tailWord_3374401).sum := by decide
  have hdescent : baseEnd_3374401 < baseStart_3374401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374412 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3374412 : Nat := 118140960795 + 3374412 * 2 ^ 59
def prefixEnd_3374412 : Nat := 4983230072969 + 3 ^ 40 * 3374412 * 2
def baseEnd_3374412 : Nat := 1155130188199704554154245

theorem tailTrace_3374412 : CollatzResearch.WordTrace tailWord_3374412 prefixEnd_3374412 1155130188199704554154245 := by
  unfold tailWord_3374412
  simp only [CollatzResearch.WordTrace]
  refine ⟨61537458325544551266414745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82049944434059401688552993 61537458325544551266414745)
  ·
    refine ⟨46153093744158413449811059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61537458325544551266414745 46153093744158413449811059)
    ·
      refine ⟨69229640616237620174716589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46153093744158413449811059 69229640616237620174716589)
      ·
        refine ⟨25961115231089107565518721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69229640616237620174716589 25961115231089107565518721)
        ·
          refine ⟨19470836423316830674139041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25961115231089107565518721 19470836423316830674139041)
          ·
            refine ⟨14603127317487623005604281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19470836423316830674139041 14603127317487623005604281)
            ·
              refine ⟨10952345488115717254203211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603127317487623005604281 10952345488115717254203211)
              ·
                refine ⟨16428518232173575881304817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10952345488115717254203211 16428518232173575881304817)
                ·
                  refine ⟨12321388674130181910978613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16428518232173575881304817 12321388674130181910978613)
                  ·
                    refine ⟨1155130188199704554154245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12321388674130181910978613 1155130188199704554154245)
                    ·
                      rfl

theorem cell22_3374412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3374412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374412 prefixEnd_3374412 := by exact prefixLift 3374412
  have htrace : WordTrace (prefixWord ++ tailWord_3374412) baseStart_3374412 baseEnd_3374412 := by
    simpa [prefixWord, tailWord_3374412, baseEnd_3374412] using wordTrace_append hprefix tailTrace_3374412
  have hstable : (prefixWord ++ tailWord_3374412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374412).length < 2 ^ (prefixWord ++ tailWord_3374412).sum := by decide
  have hdescent : baseEnd_3374412 < baseStart_3374412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374414 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_3374414 : Nat := 118140960795 + 3374414 * 2 ^ 59
def prefixEnd_3374414 : Nat := 4983230072969 + 3 ^ 40 * 3374414 * 2
def baseEnd_3374414 : Nat := 385043624280192405201413

theorem tailTrace_3374414 : CollatzResearch.WordTrace tailWord_3374414 prefixEnd_3374414 385043624280192405201413 := by
  unfold tailWord_3374414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384373699635232109300287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82049993064721237916268197 15384373699635232109300287)
  ·
    refine ⟨23076560549452848163950431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15384373699635232109300287 23076560549452848163950431)
    ·
      refine ⟨34614840824179272245925647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23076560549452848163950431 34614840824179272245925647)
      ·
        refine ⟨51922261236268908368888471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34614840824179272245925647 51922261236268908368888471)
        ·
          refine ⟨77883391854403362553332707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51922261236268908368888471 77883391854403362553332707)
          ·
            refine ⟨116825087781605043829999061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77883391854403362553332707 116825087781605043829999061)
            ·
              refine ⟨2738087994881368214765603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 116825087781605043829999061 2738087994881368214765603)
              ·
                refine ⟨4107131992322052322148405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738087994881368214765603 4107131992322052322148405)
                ·
                  refine ⟨385043624280192405201413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4107131992322052322148405 385043624280192405201413)
                  ·
                    rfl

theorem cell22_3374414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_3374414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374414 prefixEnd_3374414 := by exact prefixLift 3374414
  have htrace : WordTrace (prefixWord ++ tailWord_3374414) baseStart_3374414 baseEnd_3374414 := by
    simpa [prefixWord, tailWord_3374414, baseEnd_3374414] using wordTrace_append hprefix tailTrace_3374414
  have hstable : (prefixWord ++ tailWord_3374414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374414).length < 2 ^ (prefixWord ++ tailWord_3374414).sum := by decide
  have hdescent : baseEnd_3374414 < baseStart_3374414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374444 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_3374444 : Nat := 118140960795 + 3374444 * 2 ^ 59
def prefixEnd_3374444 : Nat := 4983230072969 + 3 ^ 40 * 3374444 * 2
def baseEnd_3374444 : Nat := 1155141142453667137354147

theorem tailTrace_3374444 : CollatzResearch.WordTrace tailWord_3374444 prefixEnd_3374444 1155141142453667137354147 := by
  unfold tailWord_3374444
  simp only [CollatzResearch.WordTrace]
  refine ⟨61538041893486585998997193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82050722524648781331996257 61538041893486585998997193)
  ·
    refine ⟨46153531420114939499247895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61538041893486585998997193 46153531420114939499247895)
    ·
      refine ⟨69230297130172409248871843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46153531420114939499247895 69230297130172409248871843)
      ·
        refine ⟨103845445695258613873307765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69230297130172409248871843 103845445695258613873307765)
        ·
          refine ⟨9735510533930495050622603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103845445695258613873307765 9735510533930495050622603)
          ·
            refine ⟨14603265800895742575933905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735510533930495050622603 14603265800895742575933905)
            ·
              refine ⟨10952449350671806931950429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603265800895742575933905 10952449350671806931950429)
              ·
                refine ⟨4107168506501927599481411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10952449350671806931950429 4107168506501927599481411)
                ·
                  refine ⟨6160752759752891399222117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107168506501927599481411 6160752759752891399222117)
                  ·
                    refine ⟨1155141142453667137354147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160752759752891399222117 1155141142453667137354147)
                    ·
                      rfl

theorem cell22_3374444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_3374444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374444 prefixEnd_3374444 := by exact prefixLift 3374444
  have htrace : WordTrace (prefixWord ++ tailWord_3374444) baseStart_3374444 baseEnd_3374444 := by
    simpa [prefixWord, tailWord_3374444, baseEnd_3374444] using wordTrace_append hprefix tailTrace_3374444
  have hstable : (prefixWord ++ tailWord_3374444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374444).length < 2 ^ (prefixWord ++ tailWord_3374444).sum := by decide
  have hdescent : baseEnd_3374444 < baseStart_3374444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374478 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_3374478 : Nat := 118140960795 + 3374478 * 2 ^ 59
def prefixEnd_3374478 : Nat := 4983230072969 + 3 ^ 40 * 3374478 * 2
def baseEnd_3374478 : Nat := 1155152781348502382004043

theorem tailTrace_3374478 : CollatzResearch.WordTrace tailWord_3374478 prefixEnd_3374478 1155152781348502382004043 := by
  unfold tailWord_3374478
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384665483606249475591511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82051549245899997203154725 15384665483606249475591511)
  ·
    refine ⟨23076998225409374213387267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15384665483606249475591511 23076998225409374213387267)
    ·
      refine ⟨34615497338114061320080901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23076998225409374213387267 34615497338114061320080901)
      ·
        refine ⟨6490405750896386497515169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34615497338114061320080901 6490405750896386497515169)
        ·
          refine ⟨4867804313172289873136377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6490405750896386497515169 4867804313172289873136377)
          ·
            refine ⟨3650853234879217404852283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4867804313172289873136377 3650853234879217404852283)
            ·
              refine ⟨5476279852318826107278425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650853234879217404852283 5476279852318826107278425)
              ·
                refine ⟨4107209889239119580458819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476279852318826107278425 4107209889239119580458819)
                ·
                  refine ⟨6160814833858679370688229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107209889239119580458819 6160814833858679370688229)
                  ·
                    refine ⟨1155152781348502382004043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160814833858679370688229 1155152781348502382004043)
                    ·
                      rfl

theorem cell22_3374478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_3374478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374478 prefixEnd_3374478 := by exact prefixLift 3374478
  have htrace : WordTrace (prefixWord ++ tailWord_3374478) baseStart_3374478 baseEnd_3374478 := by
    simpa [prefixWord, tailWord_3374478, baseEnd_3374478] using wordTrace_append hprefix tailTrace_3374478
  have hstable : (prefixWord ++ tailWord_3374478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374478).length < 2 ^ (prefixWord ++ tailWord_3374478).sum := by decide
  have hdescent : baseEnd_3374478 < baseStart_3374478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374489 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_3374489 : Nat := 118140960795 + 3374489 * 2 ^ 59
def prefixEnd_3374489 : Nat := 4983230072969 + 3 ^ 40 * 3374489 * 2
def baseEnd_3374489 : Nat := 1155156546873302019979009

theorem tailTrace_3374489 : CollatzResearch.WordTrace tailWord_3374489 prefixEnd_3374489 1155156546873302019979009 := by
  unfold tailWord_3374489
  simp only [CollatzResearch.WordTrace]
  refine ⟨123077725071810144683382521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82051816714540096455588347 123077725071810144683382521)
  ·
    refine ⟨92308293803857608512536891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123077725071810144683382521 92308293803857608512536891)
    ·
      refine ⟨138462440705786412768805337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92308293803857608512536891 138462440705786412768805337)
      ·
        refine ⟨103846830529339809576604003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138462440705786412768805337 103846830529339809576604003)
        ·
          refine ⟨155770245794009714364906005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103846830529339809576604003 155770245794009714364906005)
          ·
            refine ⟨7301730271594205360854969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155770245794009714364906005 7301730271594205360854969)
            ·
              refine ⟨5476297703695654020641227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7301730271594205360854969 5476297703695654020641227)
              ·
                refine ⟨8214446555543481030961841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476297703695654020641227 8214446555543481030961841)
                ·
                  refine ⟨6160834916657610773221381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8214446555543481030961841 6160834916657610773221381)
                  ·
                    refine ⟨1155156546873302019979009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160834916657610773221381 1155156546873302019979009)
                    ·
                      rfl

theorem cell22_3374489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_3374489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374489 prefixEnd_3374489 := by exact prefixLift 3374489
  have htrace : WordTrace (prefixWord ++ tailWord_3374489) baseStart_3374489 baseEnd_3374489 := by
    simpa [prefixWord, tailWord_3374489, baseEnd_3374489] using wordTrace_append hprefix tailTrace_3374489
  have hstable : (prefixWord ++ tailWord_3374489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374489).length < 2 ^ (prefixWord ++ tailWord_3374489).sum := by decide
  have hdescent : baseEnd_3374489 < baseStart_3374489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374504 : List Nat := [2, 1, 6, 1, 2, 10]
def baseStart_3374504 : Nat := 118140960795 + 3374504 * 2 ^ 59
def prefixEnd_3374504 : Nat := 4983230072969 + 3 ^ 40 * 3374504 * 2
def baseEnd_3374504 : Nat := 14261255329380826924123

theorem tailTrace_3374504 : CollatzResearch.WordTrace tailWord_3374504 prefixEnd_3374504 14261255329380826924123 := by
  unfold tailWord_3374504
  simp only [CollatzResearch.WordTrace]
  refine ⟨61539136083377901122589283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82052181444503868163452377 61539136083377901122589283)
  ·
    refine ⟨92308704125066851683883925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61539136083377901122589283 92308704125066851683883925)
    ·
      refine ⟨4326970505862508672682059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92308704125066851683883925 4326970505862508672682059)
      ·
        refine ⟨6490455758793763009023089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326970505862508672682059 6490455758793763009023089)
        ·
          refine ⟨4867841819095322256767317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6490455758793763009023089 4867841819095322256767317)
          ·
            refine ⟨14261255329380826924123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4867841819095322256767317 14261255329380826924123)
            ·
              rfl

theorem cell22_3374504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 10].length) (baseStart_3374504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374504 prefixEnd_3374504 := by exact prefixLift 3374504
  have htrace : WordTrace (prefixWord ++ tailWord_3374504) baseStart_3374504 baseEnd_3374504 := by
    simpa [prefixWord, tailWord_3374504, baseEnd_3374504] using wordTrace_append hprefix tailTrace_3374504
  have hstable : (prefixWord ++ tailWord_3374504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374504).length < 2 ^ (prefixWord ++ tailWord_3374504).sum := by decide
  have hdescent : baseEnd_3374504 < baseStart_3374504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374519 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 3, 3]
def baseStart_3374519 : Nat := 118140960795 + 3374519 * 2 ^ 59
def prefixEnd_3374519 : Nat := 4983230072969 + 3 ^ 40 * 3374519 * 2
def baseEnd_3374519 : Nat := 1155166816486391941728917

theorem tailTrace_3374519 : CollatzResearch.WordTrace tailWord_3374519 prefixEnd_3374519 1155166816486391941728917 := by
  unfold tailWord_3374519
  simp only [CollatzResearch.WordTrace]
  refine ⟨123078819261701459806974611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82052546174467639871316407 123078819261701459806974611)
  ·
    refine ⟨184618228892552189710461917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123078819261701459806974611 184618228892552189710461917)
    ·
      refine ⟨69231835834707071141423219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184618228892552189710461917 69231835834707071141423219)
      ·
        refine ⟨103847753752060606712134829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69231835834707071141423219 103847753752060606712134829)
        ·
          refine ⟨38942907657022727517050561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103847753752060606712134829 38942907657022727517050561)
          ·
            refine ⟨29207180742767045637787921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38942907657022727517050561 29207180742767045637787921)
            ·
              refine ⟨21905385557075284228340941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29207180742767045637787921 21905385557075284228340941)
              ·
                refine ⟨8214519583903231585627853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21905385557075284228340941 8214519583903231585627853)
                ·
                  refine ⟨3080444843963711844610445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8214519583903231585627853 3080444843963711844610445)
                  ·
                    refine ⟨1155166816486391941728917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080444843963711844610445 1155166816486391941728917)
                    ·
                      rfl

theorem cell22_3374519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_3374519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374519 prefixEnd_3374519 := by exact prefixLift 3374519
  have htrace : WordTrace (prefixWord ++ tailWord_3374519) baseStart_3374519 baseEnd_3374519 := by
    simpa [prefixWord, tailWord_3374519, baseEnd_3374519] using wordTrace_append hprefix tailTrace_3374519
  have hstable : (prefixWord ++ tailWord_3374519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374519).length < 2 ^ (prefixWord ++ tailWord_3374519).sum := by decide
  have hdescent : baseEnd_3374519 < baseStart_3374519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374521 : List Nat := [1, 2, 1, 4, 5, 1, 1, 7]
def baseStart_3374521 : Nat := 118140960795 + 3374521 * 2 ^ 59
def prefixEnd_3374521 : Nat := 4983230072969 + 3 ^ 40 * 3374521 * 2
def baseEnd_3374521 : Nat := 128351944569696067019879

theorem tailTrace_3374521 : CollatzResearch.WordTrace tailWord_3374521 prefixEnd_3374521 128351944569696067019879 := by
  unfold tailWord_3374521
  simp only [CollatzResearch.WordTrace]
  refine ⟨123078892207694214148547417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82052594805129476099031611 123078892207694214148547417)
  ·
    refine ⟨92309169155770660611410563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123078892207694214148547417 92309169155770660611410563)
    ·
      refine ⟨138463753733655990917115845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92309169155770660611410563 138463753733655990917115845)
      ·
        refine ⟨25961953825060498296959221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138463753733655990917115845 25961953825060498296959221)
        ·
          refine ⟨2433933171099421715339927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25961953825060498296959221 2433933171099421715339927)
          ·
            refine ⟨3650899756649132573009891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433933171099421715339927 3650899756649132573009891)
            ·
              refine ⟨5476349634973698859514837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650899756649132573009891 5476349634973698859514837)
              ·
                refine ⟨128351944569696067019879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5476349634973698859514837 128351944569696067019879)
                ·
                  rfl

theorem cell22_3374521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 7].length) (baseStart_3374521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374521 prefixEnd_3374521 := by exact prefixLift 3374521
  have htrace : WordTrace (prefixWord ++ tailWord_3374521) baseStart_3374521 baseEnd_3374521 := by
    simpa [prefixWord, tailWord_3374521, baseEnd_3374521] using wordTrace_append hprefix tailTrace_3374521
  have hstable : (prefixWord ++ tailWord_3374521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374521).length < 2 ^ (prefixWord ++ tailWord_3374521).sum := by decide
  have hdescent : baseEnd_3374521 < baseStart_3374521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374553 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 1, 3]
def baseStart_3374553 : Nat := 118140960795 + 3374553 * 2 ^ 59
def prefixEnd_3374553 : Nat := 4983230072969 + 3 ^ 40 * 3374553 * 2
def baseEnd_3374553 : Nat := 1155178455381227186378813

theorem tailTrace_3374553 : CollatzResearch.WordTrace tailWord_3374553 prefixEnd_3374553 1155178455381227186378813 := by
  unfold tailWord_3374553
  simp only [CollatzResearch.WordTrace]
  refine ⟨123080059343578283613712313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82053372895718855742474875 123080059343578283613712313)
  ·
    refine ⟨92310044507683712710284235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123080059343578283613712313 92310044507683712710284235)
    ·
      refine ⟨138465066761525569065426353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92310044507683712710284235 138465066761525569065426353)
      ·
        refine ⟨103848800071144176799069765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138465066761525569065426353 103848800071144176799069765)
        ·
          refine ⟨19471650013339533149825581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103848800071144176799069765 19471650013339533149825581)
          ·
            refine ⟨7301868755002324931184593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19471650013339533149825581 7301868755002324931184593)
            ·
              refine ⟨5476401566251743698388445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7301868755002324931184593 5476401566251743698388445)
              ·
                refine ⟨2053650587344403886895667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5476401566251743698388445 2053650587344403886895667)
                ·
                  refine ⟨3080475881016605830343501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053650587344403886895667 3080475881016605830343501)
                  ·
                    refine ⟨1155178455381227186378813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080475881016605830343501 1155178455381227186378813)
                    ·
                      rfl

theorem cell22_3374553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_3374553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374553 prefixEnd_3374553 := by exact prefixLift 3374553
  have htrace : WordTrace (prefixWord ++ tailWord_3374553) baseStart_3374553 baseEnd_3374553 := by
    simpa [prefixWord, tailWord_3374553, baseEnd_3374553] using wordTrace_append hprefix tailTrace_3374553
  have hstable : (prefixWord ++ tailWord_3374553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374553).length < 2 ^ (prefixWord ++ tailWord_3374553).sum := by decide
  have hdescent : baseEnd_3374553 < baseStart_3374553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374581 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3374581 : Nat := 118140960795 + 3374581 * 2 ^ 59
def prefixEnd_3374581 : Nat := 4983230072969 + 3 ^ 40 * 3374581 * 2
def baseEnd_3374581 : Nat := 1155188040353444446678727

theorem tailTrace_3374581 : CollatzResearch.WordTrace tailWord_3374581 prefixEnd_3374581 1155188040353444446678727 := by
  unfold tailWord_3374581
  simp only [CollatzResearch.WordTrace]
  refine ⟨123081080587476844395731597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82054053724984562930487731 123081080587476844395731597)
  ·
    refine ⟨46155405220303816648399349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123081080587476844395731597 46155405220303816648399349)
    ·
      refine ⟨4327069239403482810787439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46155405220303816648399349 4327069239403482810787439)
      ·
        refine ⟨6490603859105224216181159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327069239403482810787439 6490603859105224216181159)
        ·
          refine ⟨9735905788657836324271739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490603859105224216181159 9735905788657836324271739)
          ·
            refine ⟨14603858682986754486407609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735905788657836324271739 14603858682986754486407609)
            ·
              refine ⟨10952894012240065864805707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603858682986754486407609 10952894012240065864805707)
              ·
                refine ⟨16429341018360098797208561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10952894012240065864805707 16429341018360098797208561)
                ·
                  refine ⟨12322005763770074097906421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16429341018360098797208561 12322005763770074097906421)
                  ·
                    refine ⟨1155188040353444446678727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12322005763770074097906421 1155188040353444446678727)
                    ·
                      rfl

theorem cell22_3374581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3374581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374581 prefixEnd_3374581 := by exact prefixLift 3374581
  have htrace : WordTrace (prefixWord ++ tailWord_3374581) baseStart_3374581 baseEnd_3374581 := by
    simpa [prefixWord, tailWord_3374581, baseEnd_3374581] using wordTrace_append hprefix tailTrace_3374581
  have hstable : (prefixWord ++ tailWord_3374581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374581).length < 2 ^ (prefixWord ++ tailWord_3374581).sum := by decide
  have hdescent : baseEnd_3374581 < baseStart_3374581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374607 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_3374607 : Nat := 118140960795 + 3374607 * 2 ^ 59
def prefixEnd_3374607 : Nat := 4983230072969 + 3 ^ 40 * 3374607 * 2
def baseEnd_3374607 : Nat := 1155196940684789045528647

theorem tailTrace_3374607 : CollatzResearch.WordTrace tailWord_3374607 prefixEnd_3374607 1155196940684789045528647 := by
  unfold tailWord_3374607
  simp only [CollatzResearch.WordTrace]
  refine ⟨123082028885382650836178075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82054685923588433890785383 123082028885382650836178075)
  ·
    refine ⟨184623043328073976254267113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123082028885382650836178075 184623043328073976254267113)
    ·
      refine ⟨138467282496055482190700335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184623043328073976254267113 138467282496055482190700335)
      ·
        refine ⟨207700923744083223286050503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138467282496055482190700335 207700923744083223286050503)
        ·
          refine ⟨311551385616124834929075755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207700923744083223286050503 311551385616124834929075755)
          ·
            refine ⟨467327078424187252393613633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311551385616124834929075755 467327078424187252393613633)
            ·
              refine ⟨350495308818140439295210225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467327078424187252393613633 350495308818140439295210225)
              ·
                refine ⟨262871481613605329471407669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350495308818140439295210225 262871481613605329471407669)
                ·
                  refine ⟨24644201401275499637944469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262871481613605329471407669 24644201401275499637944469)
                  ·
                    refine ⟨1155196940684789045528647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24644201401275499637944469 1155196940684789045528647)
                    ·
                      rfl

theorem cell22_3374607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_3374607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374607 prefixEnd_3374607 := by exact prefixLift 3374607
  have htrace : WordTrace (prefixWord ++ tailWord_3374607) baseStart_3374607 baseEnd_3374607 := by
    simpa [prefixWord, tailWord_3374607, baseEnd_3374607] using wordTrace_append hprefix tailTrace_3374607
  have hstable : (prefixWord ++ tailWord_3374607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374607).length < 2 ^ (prefixWord ++ tailWord_3374607).sum := by decide
  have hdescent : baseEnd_3374607 < baseStart_3374607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374609 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_3374609 : Nat := 118140960795 + 3374609 * 2 ^ 59
def prefixEnd_3374609 : Nat := 4983230072969 + 3 ^ 40 * 3374609 * 2
def baseEnd_3374609 : Nat := 1155197625325661706978641

theorem tailTrace_3374609 : CollatzResearch.WordTrace tailWord_3374609 prefixEnd_3374609 1155197625325661706978641 := by
  unfold tailWord_3374609
  simp only [CollatzResearch.WordTrace]
  refine ⟨123082101831375405177750881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82054734554250270118500587 123082101831375405177750881)
  ·
    refine ⟨92311576373531553883313161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123082101831375405177750881 92311576373531553883313161)
    ·
      refine ⟨69233682280148665412484871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92311576373531553883313161 69233682280148665412484871)
      ·
        refine ⟨103850523420222998118727307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69233682280148665412484871 103850523420222998118727307)
        ·
          refine ⟨155775785130334497178090961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103850523420222998118727307 155775785130334497178090961)
          ·
            refine ⟨116831838847750872883568221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155775785130334497178090961 116831838847750872883568221)
            ·
              refine ⟨43811939567906577331338083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116831838847750872883568221 43811939567906577331338083)
              ·
                refine ⟨65717909351859865997007125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43811939567906577331338083 65717909351859865997007125)
                ·
                  refine ⟨3080527000868431218609709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65717909351859865997007125 3080527000868431218609709)
                  ·
                    refine ⟨1155197625325661706978641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080527000868431218609709 1155197625325661706978641)
                    ·
                      rfl

theorem cell22_3374609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_3374609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374609 prefixEnd_3374609 := by exact prefixLift 3374609
  have htrace : WordTrace (prefixWord ++ tailWord_3374609) baseStart_3374609 baseEnd_3374609 := by
    simpa [prefixWord, tailWord_3374609, baseEnd_3374609] using wordTrace_append hprefix tailTrace_3374609
  have hstable : (prefixWord ++ tailWord_3374609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374609).length < 2 ^ (prefixWord ++ tailWord_3374609).sum := by decide
  have hdescent : baseEnd_3374609 < baseStart_3374609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374611 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 4]
def baseStart_3374611 : Nat := 118140960795 + 3374611 * 2 ^ 59
def prefixEnd_3374611 : Nat := 4983230072969 + 3 ^ 40 * 3374611 * 2
def baseEnd_3374611 : Nat := 385066103322178122809545

theorem tailTrace_3374611 : CollatzResearch.WordTrace tailWord_3374611 prefixEnd_3374611 385066103322178122809545 := by
  unfold tailWord_3374611
  simp only [CollatzResearch.WordTrace]
  refine ⟨123082174777368159519323687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82054783184912106346215791 123082174777368159519323687)
  ·
    refine ⟨184623262166052239278985531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123082174777368159519323687 184623262166052239278985531)
    ·
      refine ⟨276934893249078358918478297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184623262166052239278985531 276934893249078358918478297)
      ·
        refine ⟨207701169936808769188858723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276934893249078358918478297 207701169936808769188858723)
        ·
          refine ⟨311551754905213153783288085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207701169936808769188858723 311551754905213153783288085)
          ·
            refine ⟨14603988511181866583591629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 311551754905213153783288085 14603988511181866583591629)
            ·
              refine ⟨5476495691693199968846861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14603988511181866583591629 5476495691693199968846861)
              ·
                refine ⟨2053685884384949988317573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5476495691693199968846861 2053685884384949988317573)
                ·
                  refine ⟨385066103322178122809545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053685884384949988317573 385066103322178122809545)
                  ·
                    rfl

theorem cell22_3374611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 4].length) (baseStart_3374611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374611 prefixEnd_3374611 := by exact prefixLift 3374611
  have htrace : WordTrace (prefixWord ++ tailWord_3374611) baseStart_3374611 baseEnd_3374611 := by
    simpa [prefixWord, tailWord_3374611, baseEnd_3374611] using wordTrace_append hprefix tailTrace_3374611
  have hstable : (prefixWord ++ tailWord_3374611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374611).length < 2 ^ (prefixWord ++ tailWord_3374611).sum := by decide
  have hdescent : baseEnd_3374611 < baseStart_3374611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374626 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3374626 : Nat := 118140960795 + 3374626 * 2 ^ 59
def prefixEnd_3374626 : Nat := 4983230072969 + 3 ^ 40 * 3374626 * 2
def baseEnd_3374626 : Nat := 1155203444773079329303589

theorem tailTrace_3374626 : CollatzResearch.WordTrace tailWord_3374626 prefixEnd_3374626 1155203444773079329303589 := by
  unfold tailWord_3374626
  simp only [CollatzResearch.WordTrace]
  refine ⟨30770680468078454270279933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82055147914875878054079821 30770680468078454270279933)
  ·
    refine ⟨11539005175529420351354975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30770680468078454270279933 11539005175529420351354975)
    ·
      refine ⟨17308507763294130527032463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11539005175529420351354975 17308507763294130527032463)
      ·
        refine ⟨25962761644941195790548695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17308507763294130527032463 25962761644941195790548695)
        ·
          refine ⟨38944142467411793685823043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25962761644941195790548695 38944142467411793685823043)
          ·
            refine ⟨58416213701117690528734565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38944142467411793685823043 58416213701117690528734565)
            ·
              refine ⟨10953040068959566974137731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58416213701117690528734565 10953040068959566974137731)
              ·
                refine ⟨16429560103439350461206597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953040068959566974137731 16429560103439350461206597)
                ·
                  refine ⟨3080542519394878211476237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16429560103439350461206597 3080542519394878211476237)
                  ·
                    refine ⟨1155203444773079329303589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080542519394878211476237 1155203444773079329303589)
                    ·
                      rfl

theorem cell22_3374626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3374626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374626 prefixEnd_3374626 := by exact prefixLift 3374626
  have htrace : WordTrace (prefixWord ++ tailWord_3374626) baseStart_3374626 baseEnd_3374626 := by
    simpa [prefixWord, tailWord_3374626, baseEnd_3374626] using wordTrace_append hprefix tailTrace_3374626
  have hstable : (prefixWord ++ tailWord_3374626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374626).length < 2 ^ (prefixWord ++ tailWord_3374626).sum := by decide
  have hdescent : baseEnd_3374626 < baseStart_3374626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374643 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 2, 3]
def baseStart_3374643 : Nat := 118140960795 + 3374643 * 2 ^ 59
def prefixEnd_3374643 : Nat := 4983230072969 + 3 ^ 40 * 3374643 * 2
def baseEnd_3374643 : Nat := 1155209264220496951628537

theorem tailTrace_3374643 : CollatzResearch.WordTrace tailWord_3374643 prefixEnd_3374643 1155209264220496951628537 := by
  unfold tailWord_3374643
  simp only [CollatzResearch.WordTrace]
  refine ⟨123083341913252228984488583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82055561275501485989659055 123083341913252228984488583)
  ·
    refine ⟨184625012869878343476732875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123083341913252228984488583 184625012869878343476732875)
    ·
      refine ⟨276937519304817515215099313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184625012869878343476732875 276937519304817515215099313)
      ·
        refine ⟨207703139478613136411324485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276937519304817515215099313 207703139478613136411324485)
        ·
          refine ⟨38944338652239963077123341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207703139478613136411324485 38944338652239963077123341)
          ·
            refine ⟨14604126994589986153921253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38944338652239963077123341 14604126994589986153921253)
            ·
              refine ⟨2738273811485622403860235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14604126994589986153921253 2738273811485622403860235)
              ·
                refine ⟨4107410717228433605790353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738273811485622403860235 4107410717228433605790353)
                ·
                  refine ⟨3080558037921325204342765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107410717228433605790353 3080558037921325204342765)
                  ·
                    refine ⟨1155209264220496951628537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080558037921325204342765 1155209264220496951628537)
                    ·
                      rfl

theorem cell22_3374643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 3].length) (baseStart_3374643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374643 prefixEnd_3374643 := by exact prefixLift 3374643
  have htrace : WordTrace (prefixWord ++ tailWord_3374643) baseStart_3374643 baseEnd_3374643 := by
    simpa [prefixWord, tailWord_3374643, baseEnd_3374643] using wordTrace_append hprefix tailTrace_3374643
  have hstable : (prefixWord ++ tailWord_3374643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374643).length < 2 ^ (prefixWord ++ tailWord_3374643).sum := by decide
  have hdescent : baseEnd_3374643 < baseStart_3374643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374731 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 1, 4]
def baseStart_3374731 : Nat := 118140960795 + 3374731 * 2 ^ 59
def prefixEnd_3374731 : Nat := 4983230072969 + 3 ^ 40 * 3374731 * 2
def baseEnd_3374731 : Nat := 1155239388418894055428267

theorem tailTrace_3374731 : CollatzResearch.WordTrace tailWord_3374731 prefixEnd_3374731 1155239388418894055428267 := by
  unfold tailWord_3374731
  simp only [CollatzResearch.WordTrace]
  refine ⟨123086551536933420013692047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82057701024622280009128031 123086551536933420013692047)
  ·
    refine ⟨184629827305400130020538071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123086551536933420013692047 184629827305400130020538071)
    ·
      refine ⟨276944740958100195030807107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184629827305400130020538071 276944740958100195030807107)
      ·
        refine ⟨415417111437150292546210661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276944740958100195030807107 415417111437150292546210661)
        ·
          refine ⟨77890708394465679852414499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415417111437150292546210661 77890708394465679852414499)
          ·
            refine ⟨116836062591698519778621749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77890708394465679852414499 116836062591698519778621749)
            ·
              refine ⟨10953380867971736229245789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116836062591698519778621749 10953380867971736229245789)
              ·
                refine ⟨4107517825489401085967171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10953380867971736229245789 4107517825489401085967171)
                ·
                  refine ⟨6161276738234101628950757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107517825489401085967171 6161276738234101628950757)
                  ·
                    refine ⟨1155239388418894055428267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6161276738234101628950757 1155239388418894055428267)
                    ·
                      rfl

theorem cell22_3374731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 4].length) (baseStart_3374731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374731 prefixEnd_3374731 := by exact prefixLift 3374731
  have htrace : WordTrace (prefixWord ++ tailWord_3374731) baseStart_3374731 baseEnd_3374731 := by
    simpa [prefixWord, tailWord_3374731, baseEnd_3374731] using wordTrace_append hprefix tailTrace_3374731
  have hstable : (prefixWord ++ tailWord_3374731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374731).length < 2 ^ (prefixWord ++ tailWord_3374731).sum := by decide
  have hdescent : baseEnd_3374731 < baseStart_3374731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374780 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 4]
def baseStart_3374780 : Nat := 118140960795 + 3374780 * 2 ^ 59
def prefixEnd_3374780 : Nat := 4983230072969 + 3 ^ 40 * 3374780 * 2
def baseEnd_3374780 : Nat := 385085387373424753651039

theorem tailTrace_3374780 : CollatzResearch.WordTrace tailWord_3374780 prefixEnd_3374780 385085387373424753651039 := by
  unfold tailWord_3374780
  simp only [CollatzResearch.WordTrace]
  refine ⟨61544169356877950691112897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82058892475837267588150529 61544169356877950691112897)
  ·
    refine ⟨46158127017658463018334673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61544169356877950691112897 46158127017658463018334673)
    ·
      refine ⟨34618595263243847263751005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46158127017658463018334673 34618595263243847263751005)
      ·
        refine ⟨12981973223716442723906627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34618595263243847263751005 12981973223716442723906627)
        ·
          refine ⟨19472959835574664085859941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12981973223716442723906627 19472959835574664085859941)
          ·
            refine ⟨3651179969170249516098739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19472959835574664085859941 3651179969170249516098739)
            ·
              refine ⟨5476769953755374274148109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3651179969170249516098739 5476769953755374274148109)
              ·
                refine ⟨2053788732658265352805541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5476769953755374274148109 2053788732658265352805541)
                ·
                  refine ⟨385085387373424753651039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053788732658265352805541 385085387373424753651039)
                  ·
                    rfl

theorem cell22_3374780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_3374780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374780 prefixEnd_3374780 := by exact prefixLift 3374780
  have htrace : WordTrace (prefixWord ++ tailWord_3374780) baseStart_3374780 baseEnd_3374780 := by
    simpa [prefixWord, tailWord_3374780, baseEnd_3374780] using wordTrace_append hprefix tailTrace_3374780
  have hstable : (prefixWord ++ tailWord_3374780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374780).length < 2 ^ (prefixWord ++ tailWord_3374780).sum := by decide
  have hdescent : baseEnd_3374780 < baseStart_3374780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374789 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3374789 : Nat := 118140960795 + 3374789 * 2 ^ 59
def prefixEnd_3374789 : Nat := 4983230072969 + 3 ^ 40 * 3374789 * 2
def baseEnd_3374789 : Nat := 1155259243004201237478089

theorem tailTrace_3374789 : CollatzResearch.WordTrace tailWord_3374789 prefixEnd_3374789 1155259243004201237478089 := by
  unfold tailWord_3374789
  simp only [CollatzResearch.WordTrace]
  refine ⟨123088666970723295919303421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82059111313815530612868947 123088666970723295919303421)
  ·
    refine ⟨46158250114021235969738783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123088666970723295919303421 46158250114021235969738783)
    ·
      refine ⟨69237375171031853954608175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46158250114021235969738783 69237375171031853954608175)
      ·
        refine ⟨103856062756547780931912263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69237375171031853954608175 103856062756547780931912263)
        ·
          refine ⟨155784094134821671397868395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103856062756547780931912263 155784094134821671397868395)
          ·
            refine ⟨233676141202232507096802593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155784094134821671397868395 233676141202232507096802593)
            ·
              refine ⟨175257105901674380322601945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233676141202232507096802593 175257105901674380322601945)
              ·
                refine ⟨131442829426255785241951459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175257105901674380322601945 131442829426255785241951459)
                ·
                  refine ⟨197164244139383677862927189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131442829426255785241951459 197164244139383677862927189)
                  ·
                    refine ⟨1155259243004201237478089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 197164244139383677862927189 1155259243004201237478089)
                    ·
                      rfl

theorem cell22_3374789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3374789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374789 prefixEnd_3374789 := by exact prefixLift 3374789
  have htrace : WordTrace (prefixWord ++ tailWord_3374789) baseStart_3374789 baseEnd_3374789 := by
    simpa [prefixWord, tailWord_3374789, baseEnd_3374789] using wordTrace_append hprefix tailTrace_3374789
  have hstable : (prefixWord ++ tailWord_3374789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374789).length < 2 ^ (prefixWord ++ tailWord_3374789).sum := by decide
  have hdescent : baseEnd_3374789 < baseStart_3374789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374812 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3374812 : Nat := 118140960795 + 3374812 * 2 ^ 59
def prefixEnd_3374812 : Nat := 4983230072969 + 3 ^ 40 * 3374812 * 2
def baseEnd_3374812 : Nat := 1155267116374236844153019

theorem tailTrace_3374812 : CollatzResearch.WordTrace tailWord_3374812 prefixEnd_3374812 1155267116374236844153019 := by
  unfold tailWord_3374812
  simp only [CollatzResearch.WordTrace]
  refine ⟨61544752924819985423695345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82059670566426647231593793 61544752924819985423695345)
  ·
    refine ⟨46158564693614989067771509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61544752924819985423695345 46158564693614989067771509)
    ·
      refine ⟨4327365440026405225103579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46158564693614989067771509 4327365440026405225103579)
      ·
        refine ⟨6491048160039607837655369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327365440026405225103579 6491048160039607837655369)
        ·
          refine ⟨4868286120029705878241527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6491048160039607837655369 4868286120029705878241527)
          ·
            refine ⟨7302429180044558817362291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868286120029705878241527 7302429180044558817362291)
            ·
              refine ⟨10953643770066838226043437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302429180044558817362291 10953643770066838226043437)
              ·
                refine ⟨4107616413775064334766289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10953643770066838226043437 4107616413775064334766289)
                ·
                  refine ⟨3080712310331298251074717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107616413775064334766289 3080712310331298251074717)
                  ·
                    refine ⟨1155267116374236844153019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080712310331298251074717 1155267116374236844153019)
                    ·
                      rfl

theorem cell22_3374812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3374812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374812 prefixEnd_3374812 := by exact prefixLift 3374812
  have htrace : WordTrace (prefixWord ++ tailWord_3374812) baseStart_3374812 baseEnd_3374812 := by
    simpa [prefixWord, tailWord_3374812, baseEnd_3374812] using wordTrace_append hprefix tailTrace_3374812
  have hstable : (prefixWord ++ tailWord_3374812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374812).length < 2 ^ (prefixWord ++ tailWord_3374812).sum := by decide
  have hdescent : baseEnd_3374812 < baseStart_3374812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374881 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 8]
def baseStart_3374881 : Nat := 118140960795 + 3374881 * 2 ^ 59
def prefixEnd_3374881 : Nat := 4983230072969 + 3 ^ 40 * 3374881 * 2
def baseEnd_3374881 : Nat := 385096912161447888059269

theorem tailTrace_3374881 : CollatzResearch.WordTrace tailWord_3374881 prefixEnd_3374881 385096912161447888059269 := by
  unfold tailWord_3374881
  simp only [CollatzResearch.WordTrace]
  refine ⟨123092022486389995631652497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82061348324259997087768331 123092022486389995631652497)
  ·
    refine ⟨92319016864792496723739373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123092022486389995631652497 92319016864792496723739373)
    ·
      refine ⟨34619631324297186271402265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92319016864792496723739373 34619631324297186271402265)
      ·
        refine ⟨25964723493222889703551699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34619631324297186271402265 25964723493222889703551699)
        ·
          refine ⟨38947085239834334555327549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25964723493222889703551699 38947085239834334555327549)
          ·
            refine ⟨14605156964937875458247831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38947085239834334555327549 14605156964937875458247831)
            ·
              refine ⟨21907735447406813187371747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14605156964937875458247831 21907735447406813187371747)
              ·
                refine ⟨32861603171110219781057621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21907735447406813187371747 32861603171110219781057621)
                ·
                  refine ⟨385096912161447888059269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32861603171110219781057621 385096912161447888059269)
                  ·
                    rfl

theorem cell22_3374881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_3374881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374881 prefixEnd_3374881 := by exact prefixLift 3374881
  have htrace : WordTrace (prefixWord ++ tailWord_3374881) baseStart_3374881 baseEnd_3374881 := by
    simpa [prefixWord, tailWord_3374881, baseEnd_3374881] using wordTrace_append hprefix tailTrace_3374881
  have hstable : (prefixWord ++ tailWord_3374881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374881).length < 2 ^ (prefixWord ++ tailWord_3374881).sum := by decide
  have hdescent : baseEnd_3374881 < baseStart_3374881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374930 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_3374930 : Nat := 118140960795 + 3374930 * 2 ^ 59
def prefixEnd_3374930 : Nat := 4983230072969 + 3 ^ 40 * 3374930 * 2
def baseEnd_3374930 : Nat := 1155307510185723869702657

theorem tailTrace_3374930 : CollatzResearch.WordTrace tailWord_3374930 prefixEnd_3374930 1155307510185723869702657 := by
  unfold tailWord_3374930
  simp only [CollatzResearch.WordTrace]
  refine ⟨30773452415803119250046561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82062539775474984666790829 30773452415803119250046561)
  ·
    refine ⟨23080089311852339437534921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30773452415803119250046561 23080089311852339437534921)
    ·
      refine ⟨17310066983889254578151191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23080089311852339437534921 17310066983889254578151191)
      ·
        refine ⟨25965100475833881867226787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17310066983889254578151191 25965100475833881867226787)
        ·
          refine ⟨38947650713750822800840181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25965100475833881867226787 38947650713750822800840181)
          ·
            refine ⟨3651342254414139637578767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38947650713750822800840181 3651342254414139637578767)
            ·
              refine ⟨5477013381621209456368151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3651342254414139637578767 5477013381621209456368151)
              ·
                refine ⟨8215520072431814184552227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477013381621209456368151 8215520072431814184552227)
                ·
                  refine ⟨12323280108647721276828341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215520072431814184552227 12323280108647721276828341)
                  ·
                    refine ⟨1155307510185723869702657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12323280108647721276828341 1155307510185723869702657)
                    ·
                      rfl

theorem cell22_3374930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_3374930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374930 prefixEnd_3374930 := by exact prefixLift 3374930
  have htrace : WordTrace (prefixWord ++ tailWord_3374930) baseStart_3374930 baseEnd_3374930 := by
    simpa [prefixWord, tailWord_3374930, baseEnd_3374930] using wordTrace_append hprefix tailTrace_3374930
  have hstable : (prefixWord ++ tailWord_3374930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374930).length < 2 ^ (prefixWord ++ tailWord_3374930).sum := by decide
  have hdescent : baseEnd_3374930 < baseStart_3374930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374943 : List Nat := [1, 1, 2, 3, 1, 4, 4, 6]
def baseStart_3374943 : Nat := 118140960795 + 3374943 * 2 ^ 59
def prefixEnd_3374943 : Nat := 4983230072969 + 3 ^ 40 * 3374943 * 2
def baseEnd_3374943 : Nat := 128367995594599574347513

theorem tailTrace_3374943 : CollatzResearch.WordTrace tailWord_3374943 prefixEnd_3374943 128367995594599574347513 := by
  unfold tailWord_3374943
  simp only [CollatzResearch.WordTrace]
  refine ⟨123094283812165380220409483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82062855874776920146939655 123094283812165380220409483)
  ·
    refine ⟨184641425718248070330614225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123094283812165380220409483 184641425718248070330614225)
    ·
      refine ⟨138481069288686052747960669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184641425718248070330614225 138481069288686052747960669)
      ·
        refine ⟨51930400983257269780485251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138481069288686052747960669 51930400983257269780485251)
        ·
          refine ⟨77895601474885904670727877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51930400983257269780485251 77895601474885904670727877)
          ·
            refine ⟨14605425276541107125761477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77895601474885904670727877 14605425276541107125761477)
            ·
              refine ⟨2738517239351457586080277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14605425276541107125761477 2738517239351457586080277)
              ·
                refine ⟨128367995594599574347513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2738517239351457586080277 128367995594599574347513)
                ·
                  rfl

theorem cell22_3374943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 6].length) (baseStart_3374943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3374943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3374943 prefixEnd_3374943 := by exact prefixLift 3374943
  have htrace : WordTrace (prefixWord ++ tailWord_3374943) baseStart_3374943 baseEnd_3374943 := by
    simpa [prefixWord, tailWord_3374943, baseEnd_3374943] using wordTrace_append hprefix tailTrace_3374943
  have hstable : (prefixWord ++ tailWord_3374943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374943).length < 2 ^ (prefixWord ++ tailWord_3374943).sum := by decide
  have hdescent : baseEnd_3374943 < baseStart_3374943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375033 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 6]
def baseStart_3375033 : Nat := 118140960795 + 3375033 * 2 ^ 59
def prefixEnd_3375033 : Nat := 4983230072969 + 3 ^ 40 * 3375033 * 2
def baseEnd_3375033 : Nat := 385114256396888644792447

theorem tailTrace_3375033 : CollatzResearch.WordTrace tailWord_3375033 prefixEnd_3375033 385114256396888644792447 := by
  unfold tailWord_3375033
  simp only [CollatzResearch.WordTrace]
  refine ⟨123097566381839325591185753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82065044254559550394123835 123097566381839325591185753)
  ·
    refine ⟨92323174786379494193389315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123097566381839325591185753 92323174786379494193389315)
    ·
      refine ⟨138484762179569241290083973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92323174786379494193389315 138484762179569241290083973)
      ·
        refine ⟨25965892908669232741890745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138484762179569241290083973 25965892908669232741890745)
        ·
          refine ⟨19474419681501924556418059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25965892908669232741890745 19474419681501924556418059)
          ·
            refine ⟨29211629522252886834627089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19474419681501924556418059 29211629522252886834627089)
            ·
              refine ⟨21908722141689665125970317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29211629522252886834627089 21908722141689665125970317)
              ·
                refine ⟨8215770803133624422238869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21908722141689665125970317 8215770803133624422238869)
                ·
                  refine ⟨385114256396888644792447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8215770803133624422238869 385114256396888644792447)
                  ·
                    rfl

theorem cell22_3375033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_3375033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375033 prefixEnd_3375033 := by exact prefixLift 3375033
  have htrace : WordTrace (prefixWord ++ tailWord_3375033) baseStart_3375033 baseEnd_3375033 := by
    simpa [prefixWord, tailWord_3375033, baseEnd_3375033] using wordTrace_append hprefix tailTrace_3375033
  have hstable : (prefixWord ++ tailWord_3375033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375033).length < 2 ^ (prefixWord ++ tailWord_3375033).sum := by decide
  have hdescent : baseEnd_3375033 < baseStart_3375033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375063 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3375063 : Nat := 118140960795 + 3375063 * 2 ^ 59
def prefixEnd_3375063 : Nat := 4983230072969 + 3 ^ 40 * 3375063 * 2
def baseEnd_3375063 : Nat := 1155353038803755856127249

theorem tailTrace_3375063 : CollatzResearch.WordTrace tailWord_3375063 prefixEnd_3375063 1155353038803755856127249 := by
  unfold tailWord_3375063
  simp only [CollatzResearch.WordTrace]
  refine ⟨123098660571730640714777843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82065773714487093809851895 123098660571730640714777843)
  ·
    refine ⟨184647990857595961072166765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123098660571730640714777843 184647990857595961072166765)
    ·
      refine ⟨69242996571598485402062537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184647990857595961072166765 69242996571598485402062537)
      ·
        refine ⟨51932247428698864051546903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69242996571598485402062537 51932247428698864051546903)
        ·
          refine ⟨77898371143048296077320355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51932247428698864051546903 77898371143048296077320355)
          ·
            refine ⟨116847556714572444115980533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77898371143048296077320355 116847556714572444115980533)
            ·
              refine ⟨10954458441991166635873175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116847556714572444115980533 10954458441991166635873175)
              ·
                refine ⟨16431687662986749953809763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10954458441991166635873175 16431687662986749953809763)
                ·
                  refine ⟨24647531494480124930714645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16431687662986749953809763 24647531494480124930714645)
                  ·
                    refine ⟨1155353038803755856127249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24647531494480124930714645 1155353038803755856127249)
                    ·
                      rfl

theorem cell22_3375063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3375063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375063 prefixEnd_3375063 := by exact prefixLift 3375063
  have htrace : WordTrace (prefixWord ++ tailWord_3375063) baseStart_3375063 baseEnd_3375063 := by
    simpa [prefixWord, tailWord_3375063, baseEnd_3375063] using wordTrace_append hprefix tailTrace_3375063
  have hstable : (prefixWord ++ tailWord_3375063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375063).length < 2 ^ (prefixWord ++ tailWord_3375063).sum := by decide
  have hdescent : baseEnd_3375063 < baseStart_3375063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375123 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 7]
def baseStart_3375123 : Nat := 118140960795 + 3375123 * 2 ^ 59
def prefixEnd_3375123 : Nat := 4983230072969 + 3 ^ 40 * 3375123 * 2
def baseEnd_3375123 : Nat := 385124526009978566542355

theorem tailTrace_3375123 : CollatzResearch.WordTrace tailWord_3375123 prefixEnd_3375123 385124526009978566542355 := by
  unfold tailWord_3375123
  simp only [CollatzResearch.WordTrace]
  refine ⟨123100848951513270961962023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82067232634342180641308015 123100848951513270961962023)
  ·
    refine ⟨184651273427269906442943035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123100848951513270961962023 184651273427269906442943035)
    ·
      refine ⟨276976910140904859664414553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184651273427269906442943035 276976910140904859664414553)
      ·
        refine ⟨207732682605678644748310915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276976910140904859664414553 207732682605678644748310915)
        ·
          refine ⟨311599023908517967122466373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207732682605678644748310915 311599023908517967122466373)
          ·
            refine ⟨58424816982847118835462445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311599023908517967122466373 58424816982847118835462445)
            ·
              refine ⟨21909306368567669563298417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58424816982847118835462445 21909306368567669563298417)
              ·
                refine ⟨16431979776425752172473813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21909306368567669563298417 16431979776425752172473813)
                ·
                  refine ⟨385124526009978566542355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16431979776425752172473813 385124526009978566542355)
                  ·
                    rfl

theorem cell22_3375123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_3375123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375123 prefixEnd_3375123 := by exact prefixLift 3375123
  have htrace : WordTrace (prefixWord ++ tailWord_3375123) baseStart_3375123 baseEnd_3375123 := by
    simpa [prefixWord, tailWord_3375123, baseEnd_3375123] using wordTrace_append hprefix tailTrace_3375123
  have hstable : (prefixWord ++ tailWord_3375123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375123).length < 2 ^ (prefixWord ++ tailWord_3375123).sum := by decide
  have hdescent : baseEnd_3375123 < baseStart_3375123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375157 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 5]
def baseStart_3375157 : Nat := 118140960795 + 3375157 * 2 ^ 59
def prefixEnd_3375157 : Nat := 4983230072969 + 3 ^ 40 * 3375157 * 2
def baseEnd_3375157 : Nat := 385128405641590314758987

theorem tailTrace_3375157 : CollatzResearch.WordTrace tailWord_3375157 prefixEnd_3375157 385128405641590314758987 := by
  unfold tailWord_3375157
  simp only [CollatzResearch.WordTrace]
  refine ⟨123102089033390094768699725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82068059355593396512466483 123102089033390094768699725)
  ·
    refine ⟨46163283387521285538262397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123102089033390094768699725 46163283387521285538262397)
    ·
      refine ⟨17311231270320482076848399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46163283387521285538262397 17311231270320482076848399)
      ·
        refine ⟨25966846905480723115272599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17311231270320482076848399 25966846905480723115272599)
        ·
          refine ⟨38950270358221084672908899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25966846905480723115272599 38950270358221084672908899)
          ·
            refine ⟨58425405537331627009363349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38950270358221084672908899 58425405537331627009363349)
            ·
              refine ⟨2738690884562420016063907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58425405537331627009363349 2738690884562420016063907)
              ·
                refine ⟨4108036326843630024095861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738690884562420016063907 4108036326843630024095861)
                ·
                  refine ⟨385128405641590314758987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4108036326843630024095861 385128405641590314758987)
                  ·
                    rfl

theorem cell22_3375157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_3375157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375157 prefixEnd_3375157 := by exact prefixLift 3375157
  have htrace : WordTrace (prefixWord ++ tailWord_3375157) baseStart_3375157 baseEnd_3375157 := by
    simpa [prefixWord, tailWord_3375157, baseEnd_3375157] using wordTrace_append hprefix tailTrace_3375157
  have hstable : (prefixWord ++ tailWord_3375157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375157).length < 2 ^ (prefixWord ++ tailWord_3375157).sum := by decide
  have hdescent : baseEnd_3375157 < baseStart_3375157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375217 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_3375217 : Nat := 118140960795 + 3375217 * 2 ^ 59
def prefixEnd_3375217 : Nat := 4983230072969 + 3 ^ 40 * 3375217 * 2
def baseEnd_3375217 : Nat := 1155405756150950787776777

theorem tailTrace_3375217 : CollatzResearch.WordTrace tailWord_3375217 prefixEnd_3375217 1155405756150950787776777 := by
  unfold tailWord_3375217
  simp only [CollatzResearch.WordTrace]
  refine ⟨123104277413172725015883905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82069518275448483343922603 123104277413172725015883905)
  ·
    refine ⟨92328208059879543761912929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123104277413172725015883905 92328208059879543761912929)
    ·
      refine ⟨69246156044909657821434697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92328208059879543761912929 69246156044909657821434697)
      ·
        refine ⟨51934617033682243366076023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69246156044909657821434697 51934617033682243366076023)
        ·
          refine ⟨77901925550523365049114035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51934617033682243366076023 77901925550523365049114035)
          ·
            refine ⟨116852888325785047573671053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77901925550523365049114035 116852888325785047573671053)
            ·
              refine ⟨43819833122169392840126645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116852888325785047573671053 43819833122169392840126645)
              ·
                refine ⟨4108109355203380578761873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43819833122169392840126645 4108109355203380578761873)
                ·
                  refine ⟨3081082016402535434071405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4108109355203380578761873 3081082016402535434071405)
                  ·
                    refine ⟨1155405756150950787776777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081082016402535434071405 1155405756150950787776777)
                    ·
                      rfl

theorem cell22_3375217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_3375217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375217 prefixEnd_3375217 := by exact prefixLift 3375217
  have htrace : WordTrace (prefixWord ++ tailWord_3375217) baseStart_3375217 baseEnd_3375217 := by
    simpa [prefixWord, tailWord_3375217, baseEnd_3375217] using wordTrace_append hprefix tailTrace_3375217
  have hstable : (prefixWord ++ tailWord_3375217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375217).length < 2 ^ (prefixWord ++ tailWord_3375217).sum := by decide
  have hdescent : baseEnd_3375217 < baseStart_3375217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375281 : List Nat := [1, 2, 2, 5, 3, 1, 2, 6]
def baseStart_3375281 : Nat := 118140960795 + 3375281 * 2 ^ 59
def prefixEnd_3375281 : Nat := 4983230072969 + 3 ^ 40 * 3375281 * 2
def baseEnd_3375281 : Nat := 128380851628763994908509

theorem tailTrace_3375281 : CollatzResearch.WordTrace tailWord_3375281 prefixEnd_3375281 128380851628763994908509 := by
  unfold tailWord_3375281
  simp only [CollatzResearch.WordTrace]
  refine ⟨123106611684940863946213697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82071074456627242630809131 123106611684940863946213697)
  ·
    refine ⟨92329958763705647959660273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123106611684940863946213697 92329958763705647959660273)
    ·
      refine ⟨69247469072779235969745205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92329958763705647959660273 69247469072779235969745205)
      ·
        refine ⟨6491950225573053372163613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69247469072779235969745205 6491950225573053372163613)
        ·
          refine ⟨2434481334589895014561355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6491950225573053372163613 2434481334589895014561355)
          ·
            refine ⟨3651722001884842521842033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434481334589895014561355 3651722001884842521842033)
            ·
              refine ⟨2738791501413631891381525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3651722001884842521842033 2738791501413631891381525)
              ·
                refine ⟨128380851628763994908509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2738791501413631891381525 128380851628763994908509)
                ·
                  rfl

theorem cell22_3375281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 6].length) (baseStart_3375281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375281 prefixEnd_3375281 := by exact prefixLift 3375281
  have htrace : WordTrace (prefixWord ++ tailWord_3375281) baseStart_3375281 baseEnd_3375281 := by
    simpa [prefixWord, tailWord_3375281, baseEnd_3375281] using wordTrace_append hprefix tailTrace_3375281
  have hstable : (prefixWord ++ tailWord_3375281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375281).length < 2 ^ (prefixWord ++ tailWord_3375281).sum := by decide
  have hdescent : baseEnd_3375281 < baseStart_3375281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375290 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_3375290 : Nat := 118140960795 + 3375290 * 2 ^ 59
def prefixEnd_3375290 : Nat := 4983230072969 + 3 ^ 40 * 3375290 * 2
def baseEnd_3375290 : Nat := 1155430745542802930701553

theorem tailTrace_3375290 : CollatzResearch.WordTrace tailWord_3375290 prefixEnd_3375290 1155430745542802930701553 := by
  unfold tailWord_3375290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30776734985477064620822831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82071293294605505655527549 30776734985477064620822831)
  ·
    refine ⟨46165102478215596931234247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30776734985477064620822831 46165102478215596931234247)
    ·
      refine ⟨69247653717323395396851371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46165102478215596931234247 69247653717323395396851371)
      ·
        refine ⟨103871480575985093095277057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69247653717323395396851371 103871480575985093095277057)
        ·
          refine ⟨77903610431988819821457793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103871480575985093095277057 77903610431988819821457793)
          ·
            refine ⟨58427707823991614866093345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77903610431988819821457793 58427707823991614866093345)
            ·
              refine ⟨43820780867993711149570009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58427707823991614866093345 43820780867993711149570009)
              ·
                refine ⟨32865585650995283362177507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43820780867993711149570009 32865585650995283362177507)
                ·
                  refine ⟨49298378476492925043266261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32865585650995283362177507 49298378476492925043266261)
                  ·
                    refine ⟨1155430745542802930701553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49298378476492925043266261 1155430745542802930701553)
                    ·
                      rfl

theorem cell22_3375290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_3375290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375290 prefixEnd_3375290 := by exact prefixLift 3375290
  have htrace : WordTrace (prefixWord ++ tailWord_3375290) baseStart_3375290 baseEnd_3375290 := by
    simpa [prefixWord, tailWord_3375290, baseEnd_3375290] using wordTrace_append hprefix tailTrace_3375290
  have hstable : (prefixWord ++ tailWord_3375290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375290).length < 2 ^ (prefixWord ++ tailWord_3375290).sum := by decide
  have hdescent : baseEnd_3375290 < baseStart_3375290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375296 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 1, 3]
def baseStart_3375296 : Nat := 118140960795 + 3375296 * 2 ^ 59
def prefixEnd_3375296 : Nat := 4983230072969 + 3 ^ 40 * 3375296 * 2
def baseEnd_3375296 : Nat := 1155432799465420915051535

theorem tailTrace_3375296 : CollatzResearch.WordTrace tailWord_3375296 prefixEnd_3375296 1155432799465420915051535 := by
  unfold tailWord_3375296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61553579389943260754004871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82071439186591014338673161 61553579389943260754004871)
  ·
    refine ⟨92330369084914891131007307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61553579389943260754004871 92330369084914891131007307)
    ·
      refine ⟨138495553627372336696510961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92330369084914891131007307 138495553627372336696510961)
      ·
        refine ⟨103871665220529252522383221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138495553627372336696510961 103871665220529252522383221)
        ·
          refine ⟨9737968614424617423973427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103871665220529252522383221 9737968614424617423973427)
          ·
            refine ⟨14606952921636926135960141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9737968614424617423973427 14606952921636926135960141)
            ·
              refine ⟨5477607345613847300985053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14606952921636926135960141 5477607345613847300985053)
              ·
                refine ⟨2054102754605192737869395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5477607345613847300985053 2054102754605192737869395)
                ·
                  refine ⟨3081154131907789106804093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054102754605192737869395 3081154131907789106804093)
                  ·
                    refine ⟨1155432799465420915051535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081154131907789106804093 1155432799465420915051535)
                    ·
                      rfl

theorem cell22_3375296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_3375296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375296 prefixEnd_3375296 := by exact prefixLift 3375296
  have htrace : WordTrace (prefixWord ++ tailWord_3375296) baseStart_3375296 baseEnd_3375296 := by
    simpa [prefixWord, tailWord_3375296, baseEnd_3375296] using wordTrace_append hprefix tailTrace_3375296
  have hstable : (prefixWord ++ tailWord_3375296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375296).length < 2 ^ (prefixWord ++ tailWord_3375296).sum := by decide
  have hdescent : baseEnd_3375296 < baseStart_3375296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375352 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_3375352 : Nat := 118140960795 + 3375352 * 2 ^ 59
def prefixEnd_3375352 : Nat := 4983230072969 + 3 ^ 40 * 3375352 * 2
def baseEnd_3375352 : Nat := 1155451969409855435651363

theorem tailTrace_3375352 : CollatzResearch.WordTrace tailWord_3375352 prefixEnd_3375352 1155451969409855435651363 := by
  unfold tailWord_3375352
  simp only [CollatzResearch.WordTrace]
  refine ⟨61554600633841821536024155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82072800845122428714698873 61554600633841821536024155)
  ·
    refine ⟨92331900950762732304036233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61554600633841821536024155 92331900950762732304036233)
    ·
      refine ⟨69248925713072049228027175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92331900950762732304036233 69248925713072049228027175)
      ·
        refine ⟨103873388569608073842040763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69248925713072049228027175 103873388569608073842040763)
        ·
          refine ⟨155810082854412110763061145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103873388569608073842040763 155810082854412110763061145)
          ·
            refine ⟨116857562140809083072295859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155810082854412110763061145 116857562140809083072295859)
            ·
              refine ⟨175286343211213624608443789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116857562140809083072295859 175286343211213624608443789)
              ·
                refine ⟨65732378704205109228166421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175286343211213624608443789 65732378704205109228166421)
                ·
                  refine ⟨3081205251759614495070301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65732378704205109228166421 3081205251759614495070301)
                  ·
                    refine ⟨1155451969409855435651363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081205251759614495070301 1155451969409855435651363)
                    ·
                      rfl

theorem cell22_3375352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_3375352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375352 prefixEnd_3375352 := by exact prefixLift 3375352
  have htrace : WordTrace (prefixWord ++ tailWord_3375352) baseStart_3375352 baseEnd_3375352 := by
    simpa [prefixWord, tailWord_3375352, baseEnd_3375352] using wordTrace_append hprefix tailTrace_3375352
  have hstable : (prefixWord ++ tailWord_3375352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375352).length < 2 ^ (prefixWord ++ tailWord_3375352).sum := by decide
  have hdescent : baseEnd_3375352 < baseStart_3375352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375356 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_3375356 : Nat := 118140960795 + 3375356 * 2 ^ 59
def prefixEnd_3375356 : Nat := 4983230072969 + 3 ^ 40 * 3375356 * 2
def baseEnd_3375356 : Nat := 1155453338691600758551351

theorem tailTrace_3375356 : CollatzResearch.WordTrace tailWord_3375356 prefixEnd_3375356 1155453338691600758551351 := by
  unfold tailWord_3375356
  simp only [CollatzResearch.WordTrace]
  refine ⟨61554673579834575877596961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82072898106446101170129281 61554673579834575877596961)
  ·
    refine ⟨46166005184875931908197721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61554673579834575877596961 46166005184875931908197721)
    ·
      refine ⟨34624503888656948931148291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46166005184875931908197721 34624503888656948931148291)
      ·
        refine ⟨51936755832985423396722437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34624503888656948931148291 51936755832985423396722437)
        ·
          refine ⟨9738141718684766886885457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51936755832985423396722437 9738141718684766886885457)
          ·
            refine ⟨7303606289013575165164093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9738141718684766886885457 7303606289013575165164093)
            ·
              refine ⟨2738852358380090686936535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7303606289013575165164093 2738852358380090686936535)
              ·
                refine ⟨4108278537570136030404803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738852358380090686936535 4108278537570136030404803)
                ·
                  refine ⟨6162417806355204045607205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108278537570136030404803 6162417806355204045607205)
                  ·
                    refine ⟨1155453338691600758551351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162417806355204045607205 1155453338691600758551351)
                    ·
                      rfl

theorem cell22_3375356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_3375356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375356 prefixEnd_3375356 := by exact prefixLift 3375356
  have htrace : WordTrace (prefixWord ++ tailWord_3375356) baseStart_3375356 baseEnd_3375356 := by
    simpa [prefixWord, tailWord_3375356, baseEnd_3375356] using wordTrace_append hprefix tailTrace_3375356
  have hstable : (prefixWord ++ tailWord_3375356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375356).length < 2 ^ (prefixWord ++ tailWord_3375356).sum := by decide
  have hdescent : baseEnd_3375356 < baseStart_3375356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375369 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_3375369 : Nat := 118140960795 + 3375369 * 2 ^ 59
def prefixEnd_3375369 : Nat := 4983230072969 + 3 ^ 40 * 3375369 * 2
def baseEnd_3375369 : Nat := 1155457788857273057976311

theorem tailTrace_3375369 : CollatzResearch.WordTrace tailWord_3375369 prefixEnd_3375369 1155457788857273057976311 := by
  unfold tailWord_3375369
  simp only [CollatzResearch.WordTrace]
  refine ⟨123109821308622054975417161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82073214205748036650278107 123109821308622054975417161)
  ·
    refine ⟨92332365981466541231562871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123109821308622054975417161 92332365981466541231562871)
    ·
      refine ⟨138498548972199811847344307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92332365981466541231562871 138498548972199811847344307)
      ·
        refine ⟨207747823458299717771016461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138498548972199811847344307 207747823458299717771016461)
        ·
          refine ⟨77905433796862394164131173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207747823458299717771016461 77905433796862394164131173)
          ·
            refine ⟨14607268836911698905774595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77905433796862394164131173 14607268836911698905774595)
            ·
              refine ⟨21910903255367548358661893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14607268836911698905774595 21910903255367548358661893)
              ·
                refine ⟨4108294360381415317249105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21910903255367548358661893 4108294360381415317249105)
                ·
                  refine ⟨3081220770286061487936829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4108294360381415317249105 3081220770286061487936829)
                  ·
                    refine ⟨1155457788857273057976311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081220770286061487936829 1155457788857273057976311)
                    ·
                      rfl

theorem cell22_3375369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_3375369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375369 prefixEnd_3375369 := by exact prefixLift 3375369
  have htrace : WordTrace (prefixWord ++ tailWord_3375369) baseStart_3375369 baseEnd_3375369 := by
    simpa [prefixWord, tailWord_3375369, baseEnd_3375369] using wordTrace_append hprefix tailTrace_3375369
  have hstable : (prefixWord ++ tailWord_3375369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375369).length < 2 ^ (prefixWord ++ tailWord_3375369).sum := by decide
  have hdescent : baseEnd_3375369 < baseStart_3375369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375431 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 1, 3]
def baseStart_3375431 : Nat := 118140960795 + 3375431 * 2 ^ 59
def prefixEnd_3375431 : Nat := 4983230072969 + 3 ^ 40 * 3375431 * 2
def baseEnd_3375431 : Nat := 1155479012724325562926121

theorem tailTrace_3375431 : CollatzResearch.WordTrace tailWord_3375431 prefixEnd_3375431 1155479012724325562926121 := by
  unfold tailWord_3375431
  simp only [CollatzResearch.WordTrace]
  refine ⟨123112082634397439564174147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82074721756264959709449431 123112082634397439564174147)
  ·
    refine ⟨184668123951596159346261221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123112082634397439564174147 184668123951596159346261221)
    ·
      refine ⟨34625273240924279877423979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184668123951596159346261221 34625273240924279877423979)
      ·
        refine ⟨51937909861386419816135969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34625273240924279877423979 51937909861386419816135969)
        ·
          refine ⟨38953432396039814862101977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51937909861386419816135969 38953432396039814862101977)
          ·
            refine ⟨29215074297029861146576483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38953432396039814862101977 29215074297029861146576483)
            ·
              refine ⟨43822611445544791719864725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29215074297029861146576483 43822611445544791719864725)
              ·
                refine ⟨2054184911509912111868659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43822611445544791719864725 2054184911509912111868659)
                ·
                  refine ⟨3081277367264868167802989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054184911509912111868659 3081277367264868167802989)
                  ·
                    refine ⟨1155479012724325562926121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081277367264868167802989 1155479012724325562926121)
                    ·
                      rfl

theorem cell22_3375431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_3375431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375431 prefixEnd_3375431 := by exact prefixLift 3375431
  have htrace : WordTrace (prefixWord ++ tailWord_3375431) baseStart_3375431 baseEnd_3375431 := by
    simpa [prefixWord, tailWord_3375431, baseEnd_3375431] using wordTrace_append hprefix tailTrace_3375431
  have hstable : (prefixWord ++ tailWord_3375431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375431).length < 2 ^ (prefixWord ++ tailWord_3375431).sum := by decide
  have hdescent : baseEnd_3375431 < baseStart_3375431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375487 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_3375487 : Nat := 118140960795 + 3375487 * 2 ^ 59
def prefixEnd_3375487 : Nat := 4983230072969 + 3 ^ 40 * 3375487 * 2
def baseEnd_3375487 : Nat := 1155498182668760083525949

theorem tailTrace_3375487 : CollatzResearch.WordTrace tailWord_3375487 prefixEnd_3375487 1155498182668760083525949 := by
  unfold tailWord_3375487
  simp only [CollatzResearch.WordTrace]
  refine ⟨123114125122194561128212715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82076083414796374085475143 123114125122194561128212715)
  ·
    refine ⟨184671187683291841692319073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123114125122194561128212715 184671187683291841692319073)
    ·
      refine ⟨138503390762468881269239305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184671187683291841692319073 138503390762468881269239305)
      ·
        refine ⟨103877543071851660951929479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138503390762468881269239305 103877543071851660951929479)
        ·
          refine ⟨155816314607777491427894219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103877543071851660951929479 155816314607777491427894219)
          ·
            refine ⟨233724471911666237141841329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155816314607777491427894219 233724471911666237141841329)
            ·
              refine ⟨175293353933749677856380997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233724471911666237141841329 175293353933749677856380997)
              ·
                refine ⟨32867503862578064598071437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175293353933749677856380997 32867503862578064598071437)
                ·
                  refine ⟨12325313948466774224276789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32867503862578064598071437 12325313948466774224276789)
                  ·
                    refine ⟨1155498182668760083525949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12325313948466774224276789 1155498182668760083525949)
                    ·
                      rfl

theorem cell22_3375487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_3375487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375487 prefixEnd_3375487 := by exact prefixLift 3375487
  have htrace : WordTrace (prefixWord ++ tailWord_3375487) baseStart_3375487 baseEnd_3375487 := by
    simpa [prefixWord, tailWord_3375487, baseEnd_3375487] using wordTrace_append hprefix tailTrace_3375487
  have hstable : (prefixWord ++ tailWord_3375487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375487).length < 2 ^ (prefixWord ++ tailWord_3375487).sum := by decide
  have hdescent : baseEnd_3375487 < baseStart_3375487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375570 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_3375570 : Nat := 118140960795 + 3375570 * 2 ^ 59
def prefixEnd_3375570 : Nat := 4983230072969 + 3 ^ 40 * 3375570 * 2
def baseEnd_3375570 : Nat := 1155526595264975533700695

theorem tailTrace_3375570 : CollatzResearch.WordTrace tailWord_3375570 prefixEnd_3375570 1155526595264975533700695 := by
  unfold tailWord_3375570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30779288095223466575871041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82078101587262577535656109 30779288095223466575871041)
  ·
    refine ⟨23084466071417599931903281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30779288095223466575871041 23084466071417599931903281)
    ·
      refine ⟨17313349553563199948927461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23084466071417599931903281 17313349553563199948927461)
      ·
        refine ⟨3246253041293099990423899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17313349553563199948927461 3246253041293099990423899)
        ·
          refine ⟨4869379561939649985635849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246253041293099990423899 4869379561939649985635849)
          ·
            refine ⟨3652034671454737489226887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4869379561939649985635849 3652034671454737489226887)
            ·
              refine ⟨5478052007182106233840331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652034671454737489226887 5478052007182106233840331)
              ·
                refine ⟨8217078010773159350760497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478052007182106233840331 8217078010773159350760497)
                ·
                  refine ⟨6162808508079869513070373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217078010773159350760497 6162808508079869513070373)
                  ·
                    refine ⟨1155526595264975533700695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162808508079869513070373 1155526595264975533700695)
                    ·
                      rfl

theorem cell22_3375570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_3375570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375570 prefixEnd_3375570 := by exact prefixLift 3375570
  have htrace : WordTrace (prefixWord ++ tailWord_3375570) baseStart_3375570 baseEnd_3375570 := by
    simpa [prefixWord, tailWord_3375570, baseEnd_3375570] using wordTrace_append hprefix tailTrace_3375570
  have hstable : (prefixWord ++ tailWord_3375570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375570).length < 2 ^ (prefixWord ++ tailWord_3375570).sum := by decide
  have hdescent : baseEnd_3375570 < baseStart_3375570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375583 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 1, 3]
def baseStart_3375583 : Nat := 118140960795 + 3375583 * 2 ^ 59
def prefixEnd_3375583 : Nat := 4983230072969 + 3 ^ 40 * 3375583 * 2
def baseEnd_3375583 : Nat := 1155531045430647833125655

theorem tailTrace_3375583 : CollatzResearch.WordTrace tailWord_3375583 prefixEnd_3375583 1155531045430647833125655 := by
  unfold tailWord_3375583
  simp only [CollatzResearch.WordTrace]
  refine ⟨123117626529846769523707403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82078417686564513015804935 123117626529846769523707403)
  ·
    refine ⟨184676439794770154285561105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123117626529846769523707403 184676439794770154285561105)
    ·
      refine ⟨138507329846077615714170829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184676439794770154285561105 138507329846077615714170829)
      ·
        refine ⟨51940248692279105892814061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138507329846077615714170829 51940248692279105892814061)
        ·
          refine ⟨19477593259604664709805273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51940248692279105892814061 19477593259604664709805273)
          ·
            refine ⟨14608194944703498532353955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19477593259604664709805273 14608194944703498532353955)
            ·
              refine ⟨21912292417055247798530933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14608194944703498532353955 21912292417055247798530933)
              ·
                refine ⟨2054277414098929481112275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21912292417055247798530933 2054277414098929481112275)
                ·
                  refine ⟨3081416121148394221668413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054277414098929481112275 3081416121148394221668413)
                  ·
                    refine ⟨1155531045430647833125655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081416121148394221668413 1155531045430647833125655)
                    ·
                      rfl

theorem cell22_3375583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_3375583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375583 prefixEnd_3375583 := by exact prefixLift 3375583
  have htrace : WordTrace (prefixWord ++ tailWord_3375583) baseStart_3375583 baseEnd_3375583 := by
    simpa [prefixWord, tailWord_3375583, baseEnd_3375583] using wordTrace_append hprefix tailTrace_3375583
  have hstable : (prefixWord ++ tailWord_3375583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375583).length < 2 ^ (prefixWord ++ tailWord_3375583).sum := by decide
  have hdescent : baseEnd_3375583 < baseStart_3375583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375609 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_3375609 : Nat := 118140960795 + 3375609 * 2 ^ 59
def prefixEnd_3375609 : Nat := 4983230072969 + 3 ^ 40 * 3375609 * 2
def baseEnd_3375609 : Nat := 1155539945761992431975575

theorem tailTrace_3375609 : CollatzResearch.WordTrace tailWord_3375609 prefixEnd_3375609 1155539945761992431975575 := by
  unfold tailWord_3375609
  simp only [CollatzResearch.WordTrace]
  refine ⟨123118574827752575964153881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82079049885168383976102587 123118574827752575964153881)
  ·
    refine ⟨92338931120814431973115411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123118574827752575964153881 92338931120814431973115411)
    ·
      refine ⟨138508396681221647959673117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92338931120814431973115411 138508396681221647959673117)
      ·
        refine ⟨51940648755458117984877419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138508396681221647959673117 51940648755458117984877419)
        ·
          refine ⟨77910973133187176977316129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51940648755458117984877419 77910973133187176977316129)
          ·
            refine ⟨58433229849890382732987097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77910973133187176977316129 58433229849890382732987097)
            ·
              refine ⟨43824922387417787049740323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58433229849890382732987097 43824922387417787049740323)
              ·
                refine ⟨65737383581126680574610485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43824922387417787049740323 65737383581126680574610485)
                ·
                  refine ⟨6162879710730626303869733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65737383581126680574610485 6162879710730626303869733)
                  ·
                    refine ⟨1155539945761992431975575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162879710730626303869733 1155539945761992431975575)
                    ·
                      rfl

theorem cell22_3375609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_3375609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375609 prefixEnd_3375609 := by exact prefixLift 3375609
  have htrace : WordTrace (prefixWord ++ tailWord_3375609) baseStart_3375609 baseEnd_3375609 := by
    simpa [prefixWord, tailWord_3375609, baseEnd_3375609] using wordTrace_append hprefix tailTrace_3375609
  have hstable : (prefixWord ++ tailWord_3375609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375609).length < 2 ^ (prefixWord ++ tailWord_3375609).sum := by decide
  have hdescent : baseEnd_3375609 < baseStart_3375609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375658 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_3375658 : Nat := 118140960795 + 3375658 * 2 ^ 59
def prefixEnd_3375658 : Nat := 4983230072969 + 3 ^ 40 * 3375658 * 2
def baseEnd_3375658 : Nat := 385185573154457545833475

theorem tailTrace_3375658 : CollatzResearch.WordTrace tailWord_3375658 prefixEnd_3375658 385185573154457545833475 := by
  unfold tailWord_3375658
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780090501143764333171907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82080241336383371555125085 30780090501143764333171907)
  ·
    refine ⟨46170135751715646499757861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30780090501143764333171907 46170135751715646499757861)
    ·
      refine ⟨8656900453446683718704599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46170135751715646499757861 8656900453446683718704599)
      ·
        refine ⟨12985350680170025578056899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8656900453446683718704599 12985350680170025578056899)
        ·
          refine ⟨19478026020255038367085349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12985350680170025578056899 19478026020255038367085349)
          ·
            refine ⟨3652129878797819693828503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19478026020255038367085349 3652129878797819693828503)
            ·
              refine ⟨5478194818196729540742755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652129878797819693828503 5478194818196729540742755)
              ·
                refine ⟨8217292227295094311114133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478194818196729540742755 8217292227295094311114133)
                ·
                  refine ⟨385185573154457545833475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8217292227295094311114133 385185573154457545833475)
                  ·
                    rfl

theorem cell22_3375658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_3375658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375658 prefixEnd_3375658 := by exact prefixLift 3375658
  have htrace : WordTrace (prefixWord ++ tailWord_3375658) baseStart_3375658 baseEnd_3375658 := by
    simpa [prefixWord, tailWord_3375658, baseEnd_3375658] using wordTrace_append hprefix tailTrace_3375658
  have hstable : (prefixWord ++ tailWord_3375658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375658).length < 2 ^ (prefixWord ++ tailWord_3375658).sum := by decide
  have hdescent : baseEnd_3375658 < baseStart_3375658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375673 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_3375673 : Nat := 118140960795 + 3375673 * 2 ^ 59
def prefixEnd_3375673 : Nat := 4983230072969 + 3 ^ 40 * 3375673 * 2
def baseEnd_3375673 : Nat := 1155561854269917598375379

theorem tailTrace_3375673 : CollatzResearch.WordTrace tailWord_3375673 prefixEnd_3375673 1155561854269917598375379 := by
  unfold tailWord_3375673
  simp only [CollatzResearch.WordTrace]
  refine ⟨123120909099520714894483673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82080606066347143262989115 123120909099520714894483673)
  ·
    refine ⟨92340681824640536170862755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123120909099520714894483673 92340681824640536170862755)
    ·
      refine ⟨138511022736960804256294133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92340681824640536170862755 138511022736960804256294133)
      ·
        refine ⟨12985408381590075399027575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138511022736960804256294133 12985408381590075399027575)
        ·
          refine ⟨19478112572385113098541363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12985408381590075399027575 19478112572385113098541363)
          ·
            refine ⟨29217168858577669647812045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19478112572385113098541363 29217168858577669647812045)
            ·
              refine ⟨10956438321966626117929517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29217168858577669647812045 10956438321966626117929517)
              ·
                refine ⟨4108664370737484794223569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10956438321966626117929517 4108664370737484794223569)
                ·
                  refine ⟨3081498278053113595667677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4108664370737484794223569 3081498278053113595667677)
                  ·
                    refine ⟨1155561854269917598375379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081498278053113595667677 1155561854269917598375379)
                    ·
                      rfl

theorem cell22_3375673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_3375673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375673 prefixEnd_3375673 := by exact prefixLift 3375673
  have htrace : WordTrace (prefixWord ++ tailWord_3375673) baseStart_3375673 baseEnd_3375673 := by
    simpa [prefixWord, tailWord_3375673, baseEnd_3375673] using wordTrace_append hprefix tailTrace_3375673
  have hstable : (prefixWord ++ tailWord_3375673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375673).length < 2 ^ (prefixWord ++ tailWord_3375673).sum := by decide
  have hdescent : baseEnd_3375673 < baseStart_3375673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375720 : List Nat := [2, 1, 4, 3, 3, 1, 1, 7]
def baseStart_3375720 : Nat := 118140960795 + 3375720 * 2 ^ 59
def prefixEnd_3375720 : Nat := 4983230072969 + 3 ^ 40 * 3375720 * 2
def baseEnd_3375720 : Nat := 128397549258936126938915

theorem tailTrace_3375720 : CollatzResearch.WordTrace tailWord_3375720 prefixEnd_3375720 128397549258936126938915 := by
  unfold tailWord_3375720
  simp only [CollatzResearch.WordTrace]
  refine ⟨61561311665175220960722307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82081748886900294614296409 61561311665175220960722307)
  ·
    refine ⟨92341967497762831441083461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61561311665175220960722307 92341967497762831441083461)
    ·
      refine ⟨17314118905830530895203149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92341967497762831441083461 17314118905830530895203149)
      ·
        refine ⟨6492794589686449085701181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17314118905830530895203149 6492794589686449085701181)
        ·
          refine ⟨2434797971132418407137943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6492794589686449085701181 2434797971132418407137943)
          ·
            refine ⟨3652196956698627610706915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434797971132418407137943 3652196956698627610706915)
            ·
              refine ⟨5478295435047941416060373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652196956698627610706915 5478295435047941416060373)
              ·
                refine ⟨128397549258936126938915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5478295435047941416060373 128397549258936126938915)
                ·
                  rfl

theorem cell22_3375720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_3375720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375720 prefixEnd_3375720 := by exact prefixLift 3375720
  have htrace : WordTrace (prefixWord ++ tailWord_3375720) baseStart_3375720 baseEnd_3375720 := by
    simpa [prefixWord, tailWord_3375720, baseEnd_3375720] using wordTrace_append hprefix tailTrace_3375720
  have hstable : (prefixWord ++ tailWord_3375720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375720).length < 2 ^ (prefixWord ++ tailWord_3375720).sum := by decide
  have hdescent : baseEnd_3375720 < baseStart_3375720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375808 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_3375808 : Nat := 118140960795 + 3375808 * 2 ^ 59
def prefixEnd_3375808 : Nat := 4983230072969 + 3 ^ 40 * 3375808 * 2
def baseEnd_3375808 : Nat := 1155608067528822246249965

theorem tailTrace_3375808 : CollatzResearch.WordTrace tailWord_3375808 prefixEnd_3375808 1155608067528822246249965 := by
  unfold tailWord_3375808
  simp only [CollatzResearch.WordTrace]
  refine ⟨61562916477015816475324039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82083888636021088633765385 61562916477015816475324039)
  ·
    refine ⟨92344374715523724712986059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61562916477015816475324039 92344374715523724712986059)
    ·
      refine ⟨138516562073285587069479089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92344374715523724712986059 138516562073285587069479089)
      ·
        refine ⟨103887421554964190302109317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138516562073285587069479089 103887421554964190302109317)
        ·
          refine ⟨19478891541555785681645497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103887421554964190302109317 19478891541555785681645497)
          ·
            refine ⟨14609168656166839261234123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19478891541555785681645497 14609168656166839261234123)
            ·
              refine ⟨21913752984250258891851185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14609168656166839261234123 21913752984250258891851185)
              ·
                refine ⟨16435314738187694168888389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21913752984250258891851185 16435314738187694168888389)
                ·
                  refine ⟨3081621513410192656666573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16435314738187694168888389 3081621513410192656666573)
                  ·
                    refine ⟨1155608067528822246249965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081621513410192656666573 1155608067528822246249965)
                    ·
                      rfl

theorem cell22_3375808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_3375808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375808 prefixEnd_3375808 := by exact prefixLift 3375808
  have htrace : WordTrace (prefixWord ++ tailWord_3375808) baseStart_3375808 baseEnd_3375808 := by
    simpa [prefixWord, tailWord_3375808, baseEnd_3375808] using wordTrace_append hprefix tailTrace_3375808
  have hstable : (prefixWord ++ tailWord_3375808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375808).length < 2 ^ (prefixWord ++ tailWord_3375808).sum := by decide
  have hdescent : baseEnd_3375808 < baseStart_3375808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375866 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_3375866 : Nat := 118140960795 + 3375866 * 2 ^ 59
def prefixEnd_3375866 : Nat := 4983230072969 + 3 ^ 40 * 3375866 * 2
def baseEnd_3375866 : Nat := 385209307371376476099929

theorem tailTrace_3375866 : CollatzResearch.WordTrace tailWord_3375866 prefixEnd_3375866 385209307371376476099929 := by
  unfold tailWord_3375866
  simp only [CollatzResearch.WordTrace]
  refine ⟨30781987096955377214064863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82085298925214339237506301 30781987096955377214064863)
  ·
    refine ⟨46172980645433065821097295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30781987096955377214064863 46172980645433065821097295)
    ·
      refine ⟨69259470968149598731645943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46172980645433065821097295 69259470968149598731645943)
      ·
        refine ⟨103889206452224398097468915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69259470968149598731645943 103889206452224398097468915)
        ·
          refine ⟨155833809678336597146203373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103889206452224398097468915 155833809678336597146203373)
          ·
            refine ⟨58437678629376223929826265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155833809678336597146203373 58437678629376223929826265)
            ·
              refine ⟨43828258972032167947369699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58437678629376223929826265 43828258972032167947369699)
              ·
                refine ⟨65742388458048251921054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43828258972032167947369699 65742388458048251921054549)
                ·
                  refine ⟨385209307371376476099929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65742388458048251921054549 385209307371376476099929)
                  ·
                    rfl

theorem cell22_3375866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_3375866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375866 prefixEnd_3375866 := by exact prefixLift 3375866
  have htrace : WordTrace (prefixWord ++ tailWord_3375866) baseStart_3375866 baseEnd_3375866 := by
    simpa [prefixWord, tailWord_3375866, baseEnd_3375866] using wordTrace_append hprefix tailTrace_3375866
  have hstable : (prefixWord ++ tailWord_3375866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375866).length < 2 ^ (prefixWord ++ tailWord_3375866).sum := by decide
  have hdescent : baseEnd_3375866 < baseStart_3375866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375898 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_3375898 : Nat := 118140960795 + 3375898 * 2 ^ 59
def prefixEnd_3375898 : Nat := 4983230072969 + 3 ^ 40 * 3375898 * 2
def baseEnd_3375898 : Nat := 1155638876368092011499689

theorem tailTrace_3375898 : CollatzResearch.WordTrace tailWord_3375898 prefixEnd_3375898 1155638876368092011499689 := by
  unfold tailWord_3375898
  simp only [CollatzResearch.WordTrace]
  refine ⟨30782278880926394580356087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82086077015803718880949565 30782278880926394580356087)
  ·
    refine ⟨46173418321389591870534131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30782278880926394580356087 46173418321389591870534131)
    ·
      refine ⟨69260127482084387805801197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46173418321389591870534131 69260127482084387805801197)
      ·
        refine ⟨25972547805781645427175449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69260127482084387805801197 25972547805781645427175449)
        ·
          refine ⟨19479410854336234070381587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25972547805781645427175449 19479410854336234070381587)
          ·
            refine ⟨29219116281504351105572381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19479410854336234070381587 29219116281504351105572381)
            ·
              refine ⟨10957168605564131664589643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29219116281504351105572381 10957168605564131664589643)
              ·
                refine ⟨16435752908346197496884465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10957168605564131664589643 16435752908346197496884465)
                ·
                  refine ⟨12326814681259648122663349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16435752908346197496884465 12326814681259648122663349)
                  ·
                    refine ⟨1155638876368092011499689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12326814681259648122663349 1155638876368092011499689)
                    ·
                      rfl

theorem cell22_3375898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_3375898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375898 prefixEnd_3375898 := by exact prefixLift 3375898
  have htrace : WordTrace (prefixWord ++ tailWord_3375898) baseStart_3375898 baseEnd_3375898 := by
    simpa [prefixWord, tailWord_3375898, baseEnd_3375898] using wordTrace_append hprefix tailTrace_3375898
  have hstable : (prefixWord ++ tailWord_3375898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375898).length < 2 ^ (prefixWord ++ tailWord_3375898).sum := by decide
  have hdescent : baseEnd_3375898 < baseStart_3375898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375934 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3375934 : Nat := 118140960795 + 3375934 * 2 ^ 59
def prefixEnd_3375934 : Nat := 4983230072969 + 3 ^ 40 * 3375934 * 2
def baseEnd_3375934 : Nat := 385217066634599972533193

theorem tailTrace_3375934 : CollatzResearch.WordTrace tailWord_3375934 prefixEnd_3375934 385217066634599972533193 := by
  unfold tailWord_3375934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391303568946894558716857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82086952367716770979823237 15391303568946894558716857)
  ·
    refine ⟨11543477676710170919037643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15391303568946894558716857 11543477676710170919037643)
    ·
      refine ⟨17315216515065256378556465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543477676710170919037643 17315216515065256378556465)
      ·
        refine ⟨12986412386298942283917349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17315216515065256378556465 12986412386298942283917349)
        ·
          refine ⟨2434952322431051678234503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12986412386298942283917349 2434952322431051678234503)
          ·
            refine ⟨3652428483646577517351755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434952322431051678234503 3652428483646577517351755)
            ·
              refine ⟨5478642725469866276027633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652428483646577517351755 5478642725469866276027633)
              ·
                refine ⟨4108982044102399707020725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5478642725469866276027633 4108982044102399707020725)
                ·
                  refine ⟨385217066634599972533193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4108982044102399707020725 385217066634599972533193)
                  ·
                    rfl

theorem cell22_3375934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3375934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375934 prefixEnd_3375934 := by exact prefixLift 3375934
  have htrace : WordTrace (prefixWord ++ tailWord_3375934) baseStart_3375934 baseEnd_3375934 := by
    simpa [prefixWord, tailWord_3375934, baseEnd_3375934] using wordTrace_append hprefix tailTrace_3375934
  have hstable : (prefixWord ++ tailWord_3375934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375934).length < 2 ^ (prefixWord ++ tailWord_3375934).sum := by decide
  have hdescent : baseEnd_3375934 < baseStart_3375934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375945 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 4]
def baseStart_3375945 : Nat := 118140960795 + 3375945 * 2 ^ 59
def prefixEnd_3375945 : Nat := 4983230072969 + 3 ^ 40 * 3375945 * 2
def baseEnd_3375945 : Nat := 385218321809533185191515

theorem tailTrace_3375945 : CollatzResearch.WordTrace tailWord_3375945 prefixEnd_3375945 385218321809533185191515 := by
  unfold tailWord_3375945
  simp only [CollatzResearch.WordTrace]
  refine ⟨123130829754535305348385289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82087219836356870232256859 123130829754535305348385289)
  ·
    refine ⟨92348122315901479011288967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123130829754535305348385289 92348122315901479011288967)
    ·
      refine ⟨138522183473852218516933451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92348122315901479011288967 138522183473852218516933451)
      ·
        refine ⟨207783275210778327775400177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138522183473852218516933451 207783275210778327775400177)
        ·
          refine ⟨155837456408083745831550133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207783275210778327775400177 155837456408083745831550133)
          ·
            refine ⟨14609761538257851171707825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155837456408083745831550133 14609761538257851171707825)
            ·
              refine ⟨10957321153693388378780869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14609761538257851171707825 10957321153693388378780869)
              ·
                refine ⟨2054497716317510321021413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10957321153693388378780869 2054497716317510321021413)
                ·
                  refine ⟨385218321809533185191515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2054497716317510321021413 385218321809533185191515)
                  ·
                    rfl

theorem cell22_3375945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_3375945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375945 prefixEnd_3375945 := by exact prefixLift 3375945
  have htrace : WordTrace (prefixWord ++ tailWord_3375945) baseStart_3375945 baseEnd_3375945 := by
    simpa [prefixWord, tailWord_3375945, baseEnd_3375945] using wordTrace_append hprefix tailTrace_3375945
  have hstable : (prefixWord ++ tailWord_3375945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375945).length < 2 ^ (prefixWord ++ tailWord_3375945).sum := by decide
  have hdescent : baseEnd_3375945 < baseStart_3375945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375960 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_3375960 : Nat := 118140960795 + 3375960 * 2 ^ 59
def prefixEnd_3375960 : Nat := 4983230072969 + 3 ^ 40 * 3375960 * 2
def baseEnd_3375960 : Nat := 1155660100235144516449499

theorem tailTrace_3375960 : CollatzResearch.WordTrace tailWord_3375960 prefixEnd_3375960 1155660100235144516449499 := by
  unfold tailWord_3375960
  simp only [CollatzResearch.WordTrace]
  refine ⟨61565688424740481455090667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82087584566320641940120889 61565688424740481455090667)
  ·
    refine ⟨92348532637110722182636001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61565688424740481455090667 92348532637110722182636001)
    ·
      refine ⟨69261399477833041636977001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92348532637110722182636001 69261399477833041636977001)
      ·
        refine ⟨51946049608374781227732751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69261399477833041636977001 51946049608374781227732751)
        ·
          refine ⟨77919074412562171841599127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51946049608374781227732751 77919074412562171841599127)
          ·
            refine ⟨116878611618843257762398691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77919074412562171841599127 116878611618843257762398691)
            ·
              refine ⟨175317917428264886643598037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116878611618843257762398691 175317917428264886643598037)
              ·
                refine ⟨4109013689724958280709329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 175317917428264886643598037 4109013689724958280709329)
                ·
                  refine ⟨3081760267293718710531997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109013689724958280709329 3081760267293718710531997)
                  ·
                    refine ⟨1155660100235144516449499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081760267293718710531997 1155660100235144516449499)
                    ·
                      rfl

theorem cell22_3375960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_3375960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375960 prefixEnd_3375960 := by exact prefixLift 3375960
  have htrace : WordTrace (prefixWord ++ tailWord_3375960) baseStart_3375960 baseEnd_3375960 := by
    simpa [prefixWord, tailWord_3375960, baseEnd_3375960] using wordTrace_append hprefix tailTrace_3375960
  have hstable : (prefixWord ++ tailWord_3375960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375960).length < 2 ^ (prefixWord ++ tailWord_3375960).sum := by decide
  have hdescent : baseEnd_3375960 < baseStart_3375960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375990 : List Nat := [5, 1, 1, 3, 1, 1, 10]
def baseStart_3375990 : Nat := 118140960795 + 3375990 * 2 ^ 59
def prefixEnd_3375990 : Nat := 4983230072969 + 3 ^ 40 * 3375990 * 2
def baseEnd_3375990 : Nat := 42802606290675349562941

theorem tailTrace_3375990 : CollatzResearch.WordTrace tailWord_3375990 prefixEnd_3375990 42802606290675349562941 := by
  unfold tailWord_3375990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695779439960767377110839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82088314026248185355848949 7695779439960767377110839)
  ·
    refine ⟨11543669159941151065666259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7695779439960767377110839 11543669159941151065666259)
    ·
      refine ⟨17315503739911726598499389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543669159941151065666259 17315503739911726598499389)
      ·
        refine ⟨6493313902466897474437271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17315503739911726598499389 6493313902466897474437271)
        ·
          refine ⟨9739970853700346211655907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493313902466897474437271 9739970853700346211655907)
          ·
            refine ⟨14609956280550519317483861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9739970853700346211655907 14609956280550519317483861)
            ·
              refine ⟨42802606290675349562941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14609956280550519317483861 42802606290675349562941)
              ·
                rfl

theorem cell22_3375990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 10].length) (baseStart_3375990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3375990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3375990 prefixEnd_3375990 := by exact prefixLift 3375990
  have htrace : WordTrace (prefixWord ++ tailWord_3375990) baseStart_3375990 baseEnd_3375990 := by
    simpa [prefixWord, tailWord_3375990, baseEnd_3375990] using wordTrace_append hprefix tailTrace_3375990
  have hstable : (prefixWord ++ tailWord_3375990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375990).length < 2 ^ (prefixWord ++ tailWord_3375990).sum := by decide
  have hdescent : baseEnd_3375990 < baseStart_3375990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376003 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_3376003 : Nat := 118140960795 + 3376003 * 2 ^ 59
def prefixEnd_3376003 : Nat := 4983230072969 + 3 ^ 40 * 3376003 * 2
def baseEnd_3376003 : Nat := 1155674820013906737624367

theorem tailTrace_3376003 : CollatzResearch.WordTrace tailWord_3376003 prefixEnd_3376003 1155674820013906737624367 := by
  unfold tailWord_3376003
  simp only [CollatzResearch.WordTrace]
  refine ⟨123132945188325181253996663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82088630125550120835997775 123132945188325181253996663)
  ·
    refine ⟨184699417782487771880994995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123132945188325181253996663 184699417782487771880994995)
    ·
      refine ⟨277049126673731657821492493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184699417782487771880994995 277049126673731657821492493)
      ·
        refine ⟨103893422502649371683059685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277049126673731657821492493 103893422502649371683059685)
        ·
          refine ⟨19480016719246757190573691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103893422502649371683059685 19480016719246757190573691)
          ·
            refine ⟨29220025078870135785860537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19480016719246757190573691 29220025078870135785860537)
            ·
              refine ⟨21915018809152601839395403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29220025078870135785860537 21915018809152601839395403)
              ·
                refine ⟨32872528213728902759093105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21915018809152601839395403 32872528213728902759093105)
                ·
                  refine ⟨24654396160296677069319829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32872528213728902759093105 24654396160296677069319829)
                  ·
                    refine ⟨1155674820013906737624367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24654396160296677069319829 1155674820013906737624367)
                    ·
                      rfl

theorem cell22_3376003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_3376003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376003 prefixEnd_3376003 := by exact prefixLift 3376003
  have htrace : WordTrace (prefixWord ++ tailWord_3376003) baseStart_3376003 baseEnd_3376003 := by
    simpa [prefixWord, tailWord_3376003, baseEnd_3376003] using wordTrace_append hprefix tailTrace_3376003
  have hstable : (prefixWord ++ tailWord_3376003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376003).length < 2 ^ (prefixWord ++ tailWord_3376003).sum := by decide
  have hdescent : baseEnd_3376003 < baseStart_3376003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376056 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 1, 3]
def baseStart_3376056 : Nat := 118140960795 + 3376056 * 2 ^ 59
def prefixEnd_3376056 : Nat := 4983230072969 + 3 ^ 40 * 3376056 * 2
def baseEnd_3376056 : Nat := 1155692962997032266049205

theorem tailTrace_3376056 : CollatzResearch.WordTrace tailWord_3376056 prefixEnd_3376056 1155692962997032266049205 := by
  unfold tailWord_3376056
  simp only [CollatzResearch.WordTrace]
  refine ⟨61567439128566585652838011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82089918838088780870450681 61567439128566585652838011)
  ·
    refine ⟨92351158692849878479257017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61567439128566585652838011 92351158692849878479257017)
    ·
      refine ⟨69263369019637408859442763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92351158692849878479257017 69263369019637408859442763)
      ·
        refine ⟨103895053529456113289164145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69263369019637408859442763 103895053529456113289164145)
        ·
          refine ⟨77921290147092084966873109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103895053529456113289164145 77921290147092084966873109)
          ·
            refine ⟨3652560475644941482822177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77921290147092084966873109 3652560475644941482822177)
            ·
              refine ⟨2739420356733706112116633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652560475644941482822177 2739420356733706112116633)
              ·
                refine ⟨2054565267550279584087475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739420356733706112116633 2054565267550279584087475)
                ·
                  refine ⟨3081847901325419376131213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054565267550279584087475 3081847901325419376131213)
                  ·
                    refine ⟨1155692962997032266049205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081847901325419376131213 1155692962997032266049205)
                    ·
                      rfl

theorem cell22_3376056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_3376056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376056 prefixEnd_3376056 := by exact prefixLift 3376056
  have htrace : WordTrace (prefixWord ++ tailWord_3376056) baseStart_3376056 baseEnd_3376056 := by
    simpa [prefixWord, tailWord_3376056, baseEnd_3376056] using wordTrace_append hprefix tailTrace_3376056
  have hstable : (prefixWord ++ tailWord_3376056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376056).length < 2 ^ (prefixWord ++ tailWord_3376056).sum := by decide
  have hdescent : baseEnd_3376056 < baseStart_3376056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376082 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3376082 : Nat := 118140960795 + 3376082 * 2 ^ 59
def prefixEnd_3376082 : Nat := 4983230072969 + 3 ^ 40 * 3376082 * 2
def baseEnd_3376082 : Nat := 1155701863328376864899125

theorem tailTrace_3376082 : CollatzResearch.WordTrace tailWord_3376082 prefixEnd_3376082 1155701863328376864899125 := by
  unfold tailWord_3376082
  simp only [CollatzResearch.WordTrace]
  refine ⟨30783956638759744436530625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82090551036692651830748333 30783956638759744436530625)
  ·
    refine ⟨23087967479069808327397969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30783956638759744436530625 23087967479069808327397969)
    ·
      refine ⟨17315975609302356245548477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23087967479069808327397969 17315975609302356245548477)
      ·
        refine ⟨6493490853488383592080679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17315975609302356245548477 6493490853488383592080679)
        ·
          refine ⟨9740236280232575388121019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493490853488383592080679 9740236280232575388121019)
          ·
            refine ⟨14610354420348863082181529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740236280232575388121019 14610354420348863082181529)
            ·
              refine ⟨10957765815261647311636147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610354420348863082181529 10957765815261647311636147)
              ·
                refine ⟨16436648722892470967454221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10957765815261647311636147 16436648722892470967454221)
                ·
                  refine ⟨6163743271084676612795333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16436648722892470967454221 6163743271084676612795333)
                  ·
                    refine ⟨1155701863328376864899125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6163743271084676612795333 1155701863328376864899125)
                    ·
                      rfl

theorem cell22_3376082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3376082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376082 prefixEnd_3376082 := by exact prefixLift 3376082
  have htrace : WordTrace (prefixWord ++ tailWord_3376082) baseStart_3376082 baseEnd_3376082 := by
    simpa [prefixWord, tailWord_3376082, baseEnd_3376082] using wordTrace_append hprefix tailTrace_3376082
  have hstable : (prefixWord ++ tailWord_3376082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376082).length < 2 ^ (prefixWord ++ tailWord_3376082).sum := by decide
  have hdescent : baseEnd_3376082 < baseStart_3376082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376114 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3376114 : Nat := 118140960795 + 3376114 * 2 ^ 59
def prefixEnd_3376114 : Nat := 4983230072969 + 3 ^ 40 * 3376114 * 2
def baseEnd_3376114 : Nat := 385237605860779816033009

theorem tailTrace_3376114 : CollatzResearch.WordTrace tailWord_3376114 prefixEnd_3376114 385237605860779816033009 := by
  unfold tailWord_3376114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30784248422730761802821849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82091329127282031474191597 30784248422730761802821849)
  ·
    refine ⟨23088186317048071352116387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30784248422730761802821849 23088186317048071352116387)
    ·
      refine ⟨34632279475572107028174581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23088186317048071352116387 34632279475572107028174581)
      ·
        refine ⟨3246776200834885033891367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34632279475572107028174581 3246776200834885033891367)
        ·
          refine ⟨4870164301252327550837051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246776200834885033891367 4870164301252327550837051)
          ·
            refine ⟨7305246451878491326255577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870164301252327550837051 7305246451878491326255577)
            ·
              refine ⟨5478934838908868494691683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305246451878491326255577 5478934838908868494691683)
              ·
                refine ⟨8218402258363302742037525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478934838908868494691683 8218402258363302742037525)
                ·
                  refine ⟨385237605860779816033009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8218402258363302742037525 385237605860779816033009)
                  ·
                    rfl

theorem cell22_3376114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3376114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376114 prefixEnd_3376114 := by exact prefixLift 3376114
  have htrace : WordTrace (prefixWord ++ tailWord_3376114) baseStart_3376114 baseEnd_3376114 := by
    simpa [prefixWord, tailWord_3376114, baseEnd_3376114] using wordTrace_append hprefix tailTrace_3376114
  have hstable : (prefixWord ++ tailWord_3376114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376114).length < 2 ^ (prefixWord ++ tailWord_3376114).sum := by decide
  have hdescent : baseEnd_3376114 < baseStart_3376114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376142 : List Nat := [4, 1, 1, 2, 2, 2, 4, 6]
def baseStart_3376142 : Nat := 118140960795 + 3376142 * 2 ^ 59
def prefixEnd_3376142 : Nat := 4983230072969 + 3 ^ 40 * 3376142 * 2
def baseEnd_3376142 : Nat := 128413600283839634266549

theorem tailTrace_3376142 : CollatzResearch.WordTrace tailWord_3376142 prefixEnd_3376142 128413600283839634266549 := by
  unfold tailWord_3376142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392251866852700999163335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82092009956547738662204453 15392251866852700999163335)
  ·
    refine ⟨23088377800279051498745003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15392251866852700999163335 23088377800279051498745003)
    ·
      refine ⟨34632566700418577248117505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23088377800279051498745003 34632566700418577248117505)
      ·
        refine ⟨25974425025313932936088129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34632566700418577248117505 25974425025313932936088129)
        ·
          refine ⟨19480818768985449702066097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25974425025313932936088129 19480818768985449702066097)
          ·
            refine ⟨14610614076739087276549573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19480818768985449702066097 14610614076739087276549573)
            ·
              refine ⟨2739490139388578864353045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14610614076739087276549573 2739490139388578864353045)
              ·
                refine ⟨128413600283839634266549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2739490139388578864353045 128413600283839634266549)
                ·
                  rfl

theorem cell22_3376142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_3376142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376142 prefixEnd_3376142 := by exact prefixLift 3376142
  have htrace : WordTrace (prefixWord ++ tailWord_3376142) baseStart_3376142 baseEnd_3376142 := by
    simpa [prefixWord, tailWord_3376142, baseEnd_3376142] using wordTrace_append hprefix tailTrace_3376142
  have hstable : (prefixWord ++ tailWord_3376142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376142).length < 2 ^ (prefixWord ++ tailWord_3376142).sum := by decide
  have hdescent : baseEnd_3376142 < baseStart_3376142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376221 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3376221 : Nat := 118140960795 + 3376221 * 2 ^ 59
def prefixEnd_3376221 : Nat := 4983230072969 + 3 ^ 40 * 3376221 * 2
def baseEnd_3376221 : Nat := 385249815289675611891233

theorem tailTrace_3376221 : CollatzResearch.WordTrace tailWord_3376221 prefixEnd_3376221 385249815289675611891233 := by
  unfold tailWord_3376221
  simp only [CollatzResearch.WordTrace]
  refine ⟨123140896301535404485432517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82093930867690269656955011 123140896301535404485432517)
  ·
    refine ⟨23088918056537888341018597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123140896301535404485432517 23088918056537888341018597)
    ·
      refine ⟨4329172135600854063940987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23088918056537888341018597 4329172135600854063940987)
      ·
        refine ⟨6493758203401281095911481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329172135600854063940987 6493758203401281095911481)
        ·
          refine ⟨4870318652550960821933611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6493758203401281095911481 4870318652550960821933611)
          ·
            refine ⟨7305477978826441232900417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870318652550960821933611 7305477978826441232900417)
            ·
              refine ⟨5479108484119830924675313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305477978826441232900417 5479108484119830924675313)
              ·
                refine ⟨4109331363089873193506485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5479108484119830924675313 4109331363089873193506485)
                ·
                  refine ⟨385249815289675611891233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4109331363089873193506485 385249815289675611891233)
                  ·
                    rfl

theorem cell22_3376221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3376221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376221 prefixEnd_3376221 := by exact prefixLift 3376221
  have htrace : WordTrace (prefixWord ++ tailWord_3376221) baseStart_3376221 baseEnd_3376221 := by
    simpa [prefixWord, tailWord_3376221, baseEnd_3376221] using wordTrace_append hprefix tailTrace_3376221
  have hstable : (prefixWord ++ tailWord_3376221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376221).length < 2 ^ (prefixWord ++ tailWord_3376221).sum := by decide
  have hdescent : baseEnd_3376221 < baseStart_3376221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376247 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 1, 5]
def baseStart_3376247 : Nat := 118140960795 + 3376247 * 2 ^ 59
def prefixEnd_3376247 : Nat := 4983230072969 + 3 ^ 40 * 3376247 * 2
def baseEnd_3376247 : Nat := 1155758346200371434523619

theorem tailTrace_3376247 : CollatzResearch.WordTrace tailWord_3376247 prefixEnd_3376247 1155758346200371434523619 := by
  unfold tailWord_3376247
  simp only [CollatzResearch.WordTrace]
  refine ⟨123141844599441210925878995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82094563066294140617252663 123141844599441210925878995)
  ·
    refine ⟨184712766899161816388818493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123141844599441210925878995 184712766899161816388818493)
    ·
      refine ⟨69267287587185681145806935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184712766899161816388818493 69267287587185681145806935)
      ·
        refine ⟨103900931380778521718710403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69267287587185681145806935 103900931380778521718710403)
        ·
          refine ⟨155851397071167782578065605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103900931380778521718710403 155851397071167782578065605)
          ·
            refine ⟨29222136950843959233387301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155851397071167782578065605 29222136950843959233387301)
            ·
              refine ⟨5479150678283242356260119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29222136950843959233387301 5479150678283242356260119)
              ·
                refine ⟨8218726017424863534390179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479150678283242356260119 8218726017424863534390179)
                ·
                  refine ⟨12328089026137295301585269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8218726017424863534390179 12328089026137295301585269)
                  ·
                    refine ⟨1155758346200371434523619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12328089026137295301585269 1155758346200371434523619)
                    ·
                      rfl

theorem cell22_3376247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_3376247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376247 prefixEnd_3376247 := by exact prefixLift 3376247
  have htrace : WordTrace (prefixWord ++ tailWord_3376247) baseStart_3376247 baseEnd_3376247 := by
    simpa [prefixWord, tailWord_3376247, baseEnd_3376247] using wordTrace_append hprefix tailTrace_3376247
  have hstable : (prefixWord ++ tailWord_3376247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376247).length < 2 ^ (prefixWord ++ tailWord_3376247).sum := by decide
  have hdescent : baseEnd_3376247 < baseStart_3376247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376384 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 4]
def baseStart_3376384 : Nat := 118140960795 + 3376384 * 2 ^ 59
def prefixEnd_3376384 : Nat := 4983230072969 + 3 ^ 40 * 3376384 * 2
def baseEnd_3376384 : Nat := 385268414700049581282733

theorem tailTrace_3376384 : CollatzResearch.WordTrace tailWord_3376384 prefixEnd_3376384 385268414700049581282733 := by
  unfold tailWord_3376384
  simp only [CollatzResearch.WordTrace]
  refine ⟨61573420699972441661808103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82097894266629922215744137 61573420699972441661808103)
  ·
    refine ⟨92360131049958662492712155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61573420699972441661808103 92360131049958662492712155)
    ·
      refine ⟨138540196574937993739068233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92360131049958662492712155 138540196574937993739068233)
      ·
        refine ⟨103905147431203495304301175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138540196574937993739068233 103905147431203495304301175)
        ·
          refine ⟨155857721146805242956451763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103905147431203495304301175 155857721146805242956451763)
          ·
            refine ⟨233786581720207864434677645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155857721146805242956451763 233786581720207864434677645)
            ·
              refine ⟨87669968145077949163004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233786581720207864434677645 87669968145077949163004117)
              ·
                refine ⟨2054764878400264433507909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87669968145077949163004117 2054764878400264433507909)
                ·
                  refine ⟨385268414700049581282733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2054764878400264433507909 385268414700049581282733)
                  ·
                    rfl

theorem cell22_3376384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_3376384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376384 prefixEnd_3376384 := by exact prefixLift 3376384
  have htrace : WordTrace (prefixWord ++ tailWord_3376384) baseStart_3376384 baseEnd_3376384 := by
    simpa [prefixWord, tailWord_3376384, baseEnd_3376384] using wordTrace_append hprefix tailTrace_3376384
  have hstable : (prefixWord ++ tailWord_3376384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376384).length < 2 ^ (prefixWord ++ tailWord_3376384).sum := by decide
  have hdescent : baseEnd_3376384 < baseStart_3376384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376416 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_3376416 : Nat := 118140960795 + 3376416 * 2 ^ 59
def prefixEnd_3376416 : Nat := 4983230072969 + 3 ^ 40 * 3376416 * 2
def baseEnd_3376416 : Nat := 1155816198354111327048101

theorem tailTrace_3376416 : CollatzResearch.WordTrace tailWord_3376416 prefixEnd_3376416 1155816198354111327048101 := by
  unfold tailWord_3376416
  simp only [CollatzResearch.WordTrace]
  refine ⟨61574004267914476394390551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82098672357219301859187401 61574004267914476394390551)
  ·
    refine ⟨92361006401871714591585827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61574004267914476394390551 92361006401871714591585827)
    ·
      refine ⟨138541509602807571887378741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92361006401871714591585827 138541509602807571887378741)
      ·
        refine ⟨12988266525263209864441757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138541509602807571887378741 12988266525263209864441757)
        ·
          refine ⟨4870599946973703699165659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12988266525263209864441757 4870599946973703699165659)
          ·
            refine ⟨7305899920460555548748489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870599946973703699165659 7305899920460555548748489)
            ·
              refine ⟨5479424940345416661561367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305899920460555548748489 5479424940345416661561367)
              ·
                refine ⟨8219137410518124992342051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479424940345416661561367 8219137410518124992342051)
                ·
                  refine ⟨12328706115777187488513077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219137410518124992342051 12328706115777187488513077)
                  ·
                    refine ⟨1155816198354111327048101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12328706115777187488513077 1155816198354111327048101)
                    ·
                      rfl

theorem cell22_3376416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_3376416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376416 prefixEnd_3376416 := by exact prefixLift 3376416
  have htrace : WordTrace (prefixWord ++ tailWord_3376416) baseStart_3376416 baseEnd_3376416 := by
    simpa [prefixWord, tailWord_3376416, baseEnd_3376416] using wordTrace_append hprefix tailTrace_3376416
  have hstable : (prefixWord ++ tailWord_3376416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376416).length < 2 ^ (prefixWord ++ tailWord_3376416).sum := by decide
  have hdescent : baseEnd_3376416 < baseStart_3376416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376474 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_3376474 : Nat := 118140960795 + 3376474 * 2 ^ 59
def prefixEnd_3376474 : Nat := 4983230072969 + 3 ^ 40 * 3376474 * 2
def baseEnd_3376474 : Nat := 385278684313139503032641

theorem tailTrace_3376474 : CollatzResearch.WordTrace tailWord_3376474 prefixEnd_3376474 385278684313139503032641 := by
  unfold tailWord_3376474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30787530992404707173598119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82100082646412552462928317 30787530992404707173598119)
  ·
    refine ⟨46181296488607060760397179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30787530992404707173598119 46181296488607060760397179)
    ·
      refine ⟨69271944732910591140595769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46181296488607060760397179 69271944732910591140595769)
      ·
        refine ⟨51953958549682943355446827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69271944732910591140595769 51953958549682943355446827)
        ·
          refine ⟨77930937824524415033170241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51953958549682943355446827 77930937824524415033170241)
          ·
            refine ⟨58448203368393311274877681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77930937824524415033170241 58448203368393311274877681)
            ·
              refine ⟨43836152526294983456158261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58448203368393311274877681 43836152526294983456158261)
              ·
                refine ⟨4109639299340154699014837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43836152526294983456158261 4109639299340154699014837)
                ·
                  refine ⟨385278684313139503032641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4109639299340154699014837 385278684313139503032641)
                  ·
                    rfl

theorem cell22_3376474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_3376474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376474 prefixEnd_3376474 := by exact prefixLift 3376474
  have htrace : WordTrace (prefixWord ++ tailWord_3376474) baseStart_3376474 baseEnd_3376474 := by
    simpa [prefixWord, tailWord_3376474, baseEnd_3376474] using wordTrace_append hprefix tailTrace_3376474
  have hstable : (prefixWord ++ tailWord_3376474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376474).length < 2 ^ (prefixWord ++ tailWord_3376474).sum := by decide
  have hdescent : baseEnd_3376474 < baseStart_3376474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376551 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3376551 : Nat := 118140960795 + 3376551 * 2 ^ 59
def prefixEnd_3376551 : Nat := 4983230072969 + 3 ^ 40 * 3376551 * 2
def baseEnd_3376551 : Nat := 1155862411613015974922687

theorem tailTrace_3376551 : CollatzResearch.WordTrace tailWord_3376551 prefixEnd_3376551 1155862411613015974922687 := by
  unfold tailWord_3376551
  simp only [CollatzResearch.WordTrace]
  refine ⟨123152932390339870844945507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82101954926893247229963671 123152932390339870844945507)
  ·
    refine ⟨184729398585509806267418261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123152932390339870844945507 184729398585509806267418261)
    ·
      refine ⟨8659190558695772168785231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184729398585509806267418261 8659190558695772168785231)
      ·
        refine ⟨12988785838043658253177847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8659190558695772168785231 12988785838043658253177847)
        ·
          refine ⟨19483178757065487379766771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12988785838043658253177847 19483178757065487379766771)
          ·
            refine ⟨29224768135598231069650157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19483178757065487379766771 29224768135598231069650157)
            ·
              refine ⟨10959288050849336651118809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29224768135598231069650157 10959288050849336651118809)
              ·
                refine ⟨8219466038137002488339107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10959288050849336651118809 8219466038137002488339107)
                ·
                  refine ⟨12329199057205503732508661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219466038137002488339107 12329199057205503732508661)
                  ·
                    refine ⟨1155862411613015974922687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12329199057205503732508661 1155862411613015974922687)
                    ·
                      rfl

theorem cell22_3376551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3376551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376551 prefixEnd_3376551 := by exact prefixLift 3376551
  have htrace : WordTrace (prefixWord ++ tailWord_3376551) baseStart_3376551 baseEnd_3376551 := by
    simpa [prefixWord, tailWord_3376551, baseEnd_3376551] using wordTrace_append hprefix tailTrace_3376551
  have hstable : (prefixWord ++ tailWord_3376551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376551).length < 2 ^ (prefixWord ++ tailWord_3376551).sum := by decide
  have hdescent : baseEnd_3376551 < baseStart_3376551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376630 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3376630 : Nat := 118140960795 + 3376630 * 2 ^ 59
def prefixEnd_3376630 : Nat := 4983230072969 + 3 ^ 40 * 3376630 * 2
def baseEnd_3376630 : Nat := 1155889454927486102197445

theorem tailTrace_3376630 : CollatzResearch.WordTrace tailWord_3376630 prefixEnd_3376630 1155889454927486102197445 := by
  unfold tailWord_3376630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697238359815854208566959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82103875838035778224714229 7697238359815854208566959)
  ·
    refine ⟨11545857539723781312850439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7697238359815854208566959 11545857539723781312850439)
    ·
      refine ⟨17318786309585671969275659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11545857539723781312850439 17318786309585671969275659)
      ·
        refine ⟨25978179464378507953913489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17318786309585671969275659 25978179464378507953913489)
        ·
          refine ⟨19483634598283880965435117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25978179464378507953913489 19483634598283880965435117)
          ·
            refine ⟨7306362974356455362038169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19483634598283880965435117 7306362974356455362038169)
            ·
              refine ⟨5479772230767341521528627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7306362974356455362038169 5479772230767341521528627)
              ·
                refine ⟨8219658346151012282292941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479772230767341521528627 8219658346151012282292941)
                ·
                  refine ⟨3082371879806629605859853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8219658346151012282292941 3082371879806629605859853)
                  ·
                    refine ⟨1155889454927486102197445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082371879806629605859853 1155889454927486102197445)
                    ·
                      rfl

theorem cell22_3376630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3376630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376630 prefixEnd_3376630 := by exact prefixLift 3376630
  have htrace : WordTrace (prefixWord ++ tailWord_3376630) baseStart_3376630 baseEnd_3376630 := by
    simpa [prefixWord, tailWord_3376630, baseEnd_3376630] using wordTrace_append hprefix tailTrace_3376630
  have hstable : (prefixWord ++ tailWord_3376630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376630).length < 2 ^ (prefixWord ++ tailWord_3376630).sum := by decide
  have hdescent : baseEnd_3376630 < baseStart_3376630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376639 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_3376639 : Nat := 118140960795 + 3376639 * 2 ^ 59
def prefixEnd_3376639 : Nat := 4983230072969 + 3 ^ 40 * 3376639 * 2
def baseEnd_3376639 : Nat := 1155892535811413078722417

theorem tailTrace_3376639 : CollatzResearch.WordTrace tailWord_3376639 prefixEnd_3376639 1155892535811413078722417 := by
  unfold tailWord_3376639
  simp only [CollatzResearch.WordTrace]
  refine ⟨123156142014021061874148971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82104094676014041249432647 123156142014021061874148971)
  ·
    refine ⟨184734213021031592811223457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123156142014021061874148971 184734213021031592811223457)
    ·
      refine ⟨138550659765773694608417593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184734213021031592811223457 138550659765773694608417593)
      ·
        refine ⟨103912994824330270956313195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138550659765773694608417593 103912994824330270956313195)
        ·
          refine ⟨155869492236495406434469793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103912994824330270956313195 155869492236495406434469793)
          ·
            refine ⟨116902119177371554825852345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155869492236495406434469793 116902119177371554825852345)
            ·
              refine ⟨87676589383028666119389259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116902119177371554825852345 87676589383028666119389259)
              ·
                refine ⟨131514884074542999179083889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87676589383028666119389259 131514884074542999179083889)
                ·
                  refine ⟨98636163055907249384312917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131514884074542999179083889 98636163055907249384312917)
                  ·
                    refine ⟨1155892535811413078722417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98636163055907249384312917 1155892535811413078722417)
                    ·
                      rfl

theorem cell22_3376639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_3376639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376639 prefixEnd_3376639 := by exact prefixLift 3376639
  have htrace : WordTrace (prefixWord ++ tailWord_3376639) baseStart_3376639 baseEnd_3376639 := by
    simpa [prefixWord, tailWord_3376639, baseEnd_3376639] using wordTrace_append hprefix tailTrace_3376639
  have hstable : (prefixWord ++ tailWord_3376639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376639).length < 2 ^ (prefixWord ++ tailWord_3376639).sum := by decide
  have hdescent : baseEnd_3376639 < baseStart_3376639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376664 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 1, 3]
def baseStart_3376664 : Nat := 118140960795 + 3376664 * 2 ^ 59
def prefixEnd_3376664 : Nat := 4983230072969 + 3 ^ 40 * 3376664 * 2
def baseEnd_3376664 : Nat := 1155901093822321346847341

theorem tailTrace_3376664 : CollatzResearch.WordTrace tailWord_3376664 prefixEnd_3376664 1155901093822321346847341 := by
  unfold tailWord_3376664
  simp only [CollatzResearch.WordTrace]
  refine ⟨61578526919465245571904523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82104702559286994095872697 61578526919465245571904523)
  ·
    refine ⟨92367790379197868357856785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61578526919465245571904523 92367790379197868357856785)
    ·
      refine ⟨69275842784398401268392589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92367790379197868357856785 69275842784398401268392589)
      ·
        refine ⟨25978441044149400475647221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69275842784398401268392589 25978441044149400475647221)
        ·
          refine ⟨2435478847889006294591927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25978441044149400475647221 2435478847889006294591927)
          ·
            refine ⟨3653218271833509441887891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435478847889006294591927 3653218271833509441887891)
            ·
              refine ⟨5479827407750264162831837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653218271833509441887891 5479827407750264162831837)
              ·
                refine ⟨2054935277906349061061939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5479827407750264162831837 2054935277906349061061939)
                ·
                  refine ⟨3082402916859523591592909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054935277906349061061939 3082402916859523591592909)
                  ·
                    refine ⟨1155901093822321346847341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082402916859523591592909 1155901093822321346847341)
                    ·
                      rfl

theorem cell22_3376664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_3376664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376664 prefixEnd_3376664 := by exact prefixLift 3376664
  have htrace : WordTrace (prefixWord ++ tailWord_3376664) baseStart_3376664 baseEnd_3376664 := by
    simpa [prefixWord, tailWord_3376664, baseEnd_3376664] using wordTrace_append hprefix tailTrace_3376664
  have hstable : (prefixWord ++ tailWord_3376664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376664).length < 2 ^ (prefixWord ++ tailWord_3376664).sum := by decide
  have hdescent : baseEnd_3376664 < baseStart_3376664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376673 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3376673 : Nat := 118140960795 + 3376673 * 2 ^ 59
def prefixEnd_3376673 : Nat := 4983230072969 + 3 ^ 40 * 3376673 * 2
def baseEnd_3376673 : Nat := 1155904174706248323372313

theorem tailTrace_3376673 : CollatzResearch.WordTrace tailWord_3376673 prefixEnd_3376673 1155904174706248323372313 := by
  unfold tailWord_3376673
  simp only [CollatzResearch.WordTrace]
  refine ⟨123157382095897885680886673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82104921397265257120591115 123157382095897885680886673)
  ·
    refine ⟨92368036571923414260665005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123157382095897885680886673 92368036571923414260665005)
    ·
      refine ⟨34638013714471280347749377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92368036571923414260665005 34638013714471280347749377)
      ·
        refine ⟨25978510285853460260812033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34638013714471280347749377 25978510285853460260812033)
        ·
          refine ⟨19483882714390095195609025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25978510285853460260812033 19483882714390095195609025)
          ·
            refine ⟨14612912035792571396706769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19483882714390095195609025 14612912035792571396706769)
            ·
              refine ⟨10959684026844428547530077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14612912035792571396706769 10959684026844428547530077)
              ·
                refine ⟨4109881510066660705323779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10959684026844428547530077 4109881510066660705323779)
                ·
                  refine ⟨6164822265099991057985669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109881510066660705323779 6164822265099991057985669)
                  ·
                    refine ⟨1155904174706248323372313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6164822265099991057985669 1155904174706248323372313)
                    ·
                      rfl

theorem cell22_3376673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3376673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376673 prefixEnd_3376673 := by exact prefixLift 3376673
  have htrace : WordTrace (prefixWord ++ tailWord_3376673) baseStart_3376673 baseEnd_3376673 := by
    simpa [prefixWord, tailWord_3376673, baseEnd_3376673] using wordTrace_append hprefix tailTrace_3376673
  have hstable : (prefixWord ++ tailWord_3376673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376673).length < 2 ^ (prefixWord ++ tailWord_3376673).sum := by decide
  have hdescent : baseEnd_3376673 < baseStart_3376673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376694 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_3376694 : Nat := 118140960795 + 3376694 * 2 ^ 59
def prefixEnd_3376694 : Nat := 4983230072969 + 3 ^ 40 * 3376694 * 2
def baseEnd_3376694 : Nat := 385303787811803756199083

theorem tailTrace_3376694 : CollatzResearch.WordTrace tailWord_3376694 prefixEnd_3376694 385303787811803756199083 := by
  unfold tailWord_3376694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697384251801362891712571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82105432019214537511600757 7697384251801362891712571)
  ·
    refine ⟨11546076377702044337568857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7697384251801362891712571 11546076377702044337568857)
    ·
      refine ⟨8659557283276533253176643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11546076377702044337568857 8659557283276533253176643)
      ·
        refine ⟨12989335924914799879764965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8659557283276533253176643 12989335924914799879764965)
        ·
          refine ⟨2435500485921524977455931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12989335924914799879764965 2435500485921524977455931)
          ·
            refine ⟨3653250728882287466183897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435500485921524977455931 3653250728882287466183897)
            ·
              refine ⟨2739938046661715599637923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3653250728882287466183897 2739938046661715599637923)
              ·
                refine ⟨4109907069992573399456885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739938046661715599637923 4109907069992573399456885)
                ·
                  refine ⟨385303787811803756199083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4109907069992573399456885 385303787811803756199083)
                  ·
                    rfl

theorem cell22_3376694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_3376694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376694 prefixEnd_3376694 := by exact prefixLift 3376694
  have htrace : WordTrace (prefixWord ++ tailWord_3376694) baseStart_3376694 baseEnd_3376694 := by
    simpa [prefixWord, tailWord_3376694, baseEnd_3376694] using wordTrace_append hprefix tailTrace_3376694
  have hstable : (prefixWord ++ tailWord_3376694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376694).length < 2 ^ (prefixWord ++ tailWord_3376694).sum := by decide
  have hdescent : baseEnd_3376694 < baseStart_3376694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376716 : List Nat := [2, 2, 1, 3, 1, 3, 2, 8]
def baseStart_3376716 : Nat := 118140960795 + 3376716 * 2 ^ 59
def prefixEnd_3376716 : Nat := 4983230072969 + 3 ^ 40 * 3376716 * 2
def baseEnd_3376716 : Nat := 128435432720556727171909

theorem tailTrace_3376716 : CollatzResearch.WordTrace tailWord_3376716 prefixEnd_3376716 128435432720556727171909 := by
  unfold tailWord_3376716
  simp only [CollatzResearch.WordTrace]
  refine ⟨61579475217371052012351001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82105966956494736016468001 61579475217371052012351001)
  ·
    refine ⟨46184606413028289009263251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61579475217371052012351001 46184606413028289009263251)
    ·
      refine ⟨69276909619542433513894877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46184606413028289009263251 69276909619542433513894877)
      ·
        refine ⟨25978841107328412567710579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69276909619542433513894877 25978841107328412567710579)
        ·
          refine ⟨38968261660992618851565869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25978841107328412567710579 38968261660992618851565869)
          ·
            refine ⟨14613098122872232069337201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38968261660992618851565869 14613098122872232069337201)
            ·
              refine ⟨10959823592154174052002901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14613098122872232069337201 10959823592154174052002901)
              ·
                refine ⟨128435432720556727171909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10959823592154174052002901 128435432720556727171909)
                ·
                  rfl

theorem cell22_3376716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_3376716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376716 prefixEnd_3376716 := by exact prefixLift 3376716
  have htrace : WordTrace (prefixWord ++ tailWord_3376716) baseStart_3376716 baseEnd_3376716 := by
    simpa [prefixWord, tailWord_3376716, baseEnd_3376716] using wordTrace_append hprefix tailTrace_3376716
  have hstable : (prefixWord ++ tailWord_3376716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376716).length < 2 ^ (prefixWord ++ tailWord_3376716).sum := by decide
  have hdescent : baseEnd_3376716 < baseStart_3376716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376733 : List Nat := [1, 4, 4, 2, 11]
def baseStart_3376733 : Nat := 118140960795 + 3376733 * 2 ^ 59
def prefixEnd_3376733 : Nat := 4983230072969 + 3 ^ 40 * 3376733 * 2
def baseEnd_3376733 : Nat := 4756891826882420439803

theorem tailTrace_3376733 : CollatzResearch.WordTrace tailWord_3376733 prefixEnd_3376733 4756891826882420439803 := by
  unfold tailWord_3376733
  simp only [CollatzResearch.WordTrace]
  refine ⟨123159570475680515928070853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82106380317120343952047235 123159570475680515928070853)
  ·
    refine ⟨23092419464190096736513285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123159570475680515928070853 23092419464190096736513285)
    ·
      refine ⟨4329828649535643138096241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23092419464190096736513285 4329828649535643138096241)
      ·
        refine ⟨3247371487151732353572181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4329828649535643138096241 3247371487151732353572181)
        ·
          refine ⟨4756891826882420439803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3247371487151732353572181 4756891826882420439803)
          ·
            rfl

theorem cell22_3376733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 11].length) (baseStart_3376733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376733 prefixEnd_3376733 := by exact prefixLift 3376733
  have htrace : WordTrace (prefixWord ++ tailWord_3376733) baseStart_3376733 baseEnd_3376733 := by
    simpa [prefixWord, tailWord_3376733, baseEnd_3376733] using wordTrace_append hprefix tailTrace_3376733
  have hstable : (prefixWord ++ tailWord_3376733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376733).length < 2 ^ (prefixWord ++ tailWord_3376733).sum := by decide
  have hdescent : baseEnd_3376733 < baseStart_3376733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376748 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_3376748 : Nat := 118140960795 + 3376748 * 2 ^ 59
def prefixEnd_3376748 : Nat := 4983230072969 + 3 ^ 40 * 3376748 * 2
def baseEnd_3376748 : Nat := 1155929848738973127747083

theorem tailTrace_3376748 : CollatzResearch.WordTrace tailWord_3376748 prefixEnd_3376748 1155929848738973127747083 := by
  unfold tailWord_3376748
  simp only [CollatzResearch.WordTrace]
  refine ⟨61580058785313086744933449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82106745047084115659911265 61580058785313086744933449)
  ·
    refine ⟨46185044088984815058700087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61580058785313086744933449 46185044088984815058700087)
    ·
      refine ⟨69277566133477222588050131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46185044088984815058700087 69277566133477222588050131)
      ·
        refine ⟨103916349200215833882075197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69277566133477222588050131 103916349200215833882075197)
        ·
          refine ⟨38968630950080937705778199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103916349200215833882075197 38968630950080937705778199)
          ·
            refine ⟨58452946425121406558667299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38968630950080937705778199 58452946425121406558667299)
            ·
              refine ⟨87679419637682109838000949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58452946425121406558667299 87679419637682109838000949)
              ·
                refine ⟨8219945591032697797312589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87679419637682109838000949 8219945591032697797312589)
                ·
                  refine ⟨3082479596637261673992221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8219945591032697797312589 3082479596637261673992221)
                  ·
                    refine ⟨1155929848738973127747083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082479596637261673992221 1155929848738973127747083)
                    ·
                      rfl

theorem cell22_3376748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_3376748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376748 prefixEnd_3376748 := by exact prefixLift 3376748
  have htrace : WordTrace (prefixWord ++ tailWord_3376748) baseStart_3376748 baseEnd_3376748 := by
    simpa [prefixWord, tailWord_3376748, baseEnd_3376748] using wordTrace_append hprefix tailTrace_3376748
  have hstable : (prefixWord ++ tailWord_3376748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376748).length < 2 ^ (prefixWord ++ tailWord_3376748).sum := by decide
  have hdescent : baseEnd_3376748 < baseStart_3376748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376750 : List Nat := [4, 1, 2, 2, 3, 2, 1, 7]
def baseStart_3376750 : Nat := 118140960795 + 3376750 * 2 ^ 59
def prefixEnd_3376750 : Nat := 4983230072969 + 3 ^ 40 * 3376750 * 2
def baseEnd_3376750 : Nat := 128436725931093976577453

theorem tailTrace_3376750 : CollatzResearch.WordTrace tailWord_3376750 prefixEnd_3376750 128436725931093976577453 := by
  unfold tailWord_3376750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15395023814577365978929963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82106793677745951887626469 15395023814577365978929963)
  ·
    refine ⟨23092535721866048968394945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15395023814577365978929963 23092535721866048968394945)
    ·
      refine ⟨17319401791399536726296209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23092535721866048968394945 17319401791399536726296209)
      ·
        refine ⟨12989551343549652544722157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17319401791399536726296209 12989551343549652544722157)
        ·
          refine ⟨4871081753831119704270809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12989551343549652544722157 4871081753831119704270809)
          ·
            refine ⟨3653311315373339778203107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4871081753831119704270809 3653311315373339778203107)
            ·
              refine ⟨5479966973060009667304661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653311315373339778203107 5479966973060009667304661)
              ·
                refine ⟨128436725931093976577453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5479966973060009667304661 128436725931093976577453)
                ·
                  rfl

theorem cell22_3376750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_3376750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376750 prefixEnd_3376750 := by exact prefixLift 3376750
  have htrace : WordTrace (prefixWord ++ tailWord_3376750) baseStart_3376750 baseEnd_3376750 := by
    simpa [prefixWord, tailWord_3376750, baseEnd_3376750] using wordTrace_append hprefix tailTrace_3376750
  have hstable : (prefixWord ++ tailWord_3376750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376750).length < 2 ^ (prefixWord ++ tailWord_3376750).sum := by decide
  have hdescent : baseEnd_3376750 < baseStart_3376750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376765 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_3376765 : Nat := 118140960795 + 3376765 * 2 ^ 59
def prefixEnd_3376765 : Nat := 4983230072969 + 3 ^ 40 * 3376765 * 2
def baseEnd_3376765 : Nat := 1155935668186390750072031

theorem tailTrace_3376765 : CollatzResearch.WordTrace tailWord_3376765 prefixEnd_3376765 1155935668186390750072031 := by
  unfold tailWord_3376765
  simp only [CollatzResearch.WordTrace]
  refine ⟨123160737611564585393235749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82107158407709723595490499 123160737611564585393235749)
  ·
    refine ⟨23092638302168359761231703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123160737611564585393235749 23092638302168359761231703)
    ·
      refine ⟨34638957453252539641847555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23092638302168359761231703 34638957453252539641847555)
      ·
        refine ⟨51958436179878809462771333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34638957453252539641847555 51958436179878809462771333)
        ·
          refine ⟨9742206783727276774269625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51958436179878809462771333 9742206783727276774269625)
          ·
            refine ⟨7306655087795457580702219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9742206783727276774269625 7306655087795457580702219)
            ·
              refine ⟨10959982631693186371053329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306655087795457580702219 10959982631693186371053329)
              ·
                refine ⟨8219986973769889778289997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10959982631693186371053329 8219986973769889778289997)
                ·
                  refine ⟨3082495115163708666858749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8219986973769889778289997 3082495115163708666858749)
                  ·
                    refine ⟨1155935668186390750072031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082495115163708666858749 1155935668186390750072031)
                    ·
                      rfl

theorem cell22_3376765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_3376765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376765 prefixEnd_3376765 := by exact prefixLift 3376765
  have htrace : WordTrace (prefixWord ++ tailWord_3376765) baseStart_3376765 baseEnd_3376765 := by
    simpa [prefixWord, tailWord_3376765, baseEnd_3376765] using wordTrace_append hprefix tailTrace_3376765
  have hstable : (prefixWord ++ tailWord_3376765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376765).length < 2 ^ (prefixWord ++ tailWord_3376765).sum := by decide
  have hdescent : baseEnd_3376765 < baseStart_3376765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376782 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_3376782 : Nat := 118140960795 + 3376782 * 2 ^ 59
def prefixEnd_3376782 : Nat := 4983230072969 + 3 ^ 40 * 3376782 * 2
def baseEnd_3376782 : Nat := 1155941487633808372396979

theorem tailTrace_3376782 : CollatzResearch.WordTrace tailWord_3376782 prefixEnd_3376782 1155941487633808372396979 := by
  unfold tailWord_3376782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15395169706562874662075575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82107571768335331531069733 15395169706562874662075575)
  ·
    refine ⟨23092754559844311993113363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15395169706562874662075575 23092754559844311993113363)
    ·
      refine ⟨34639131839766467989670045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23092754559844311993113363 34639131839766467989670045)
      ·
        refine ⟨12989674439912425496126267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34639131839766467989670045 12989674439912425496126267)
        ·
          refine ⟨19484511659868638244189401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12989674439912425496126267 19484511659868638244189401)
          ·
            refine ⟨14613383744901478683142051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19484511659868638244189401 14613383744901478683142051)
            ·
              refine ⟨21920075617352218024713077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14613383744901478683142051 21920075617352218024713077)
              ·
                refine ⟨2055007089126770439816851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21920075617352218024713077 2055007089126770439816851)
                ·
                  refine ⟨3082510633690155659725277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055007089126770439816851 3082510633690155659725277)
                  ·
                    refine ⟨1155941487633808372396979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082510633690155659725277 1155941487633808372396979)
                    ·
                      rfl

theorem cell22_3376782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_3376782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376782 prefixEnd_3376782 := by exact prefixLift 3376782
  have htrace : WordTrace (prefixWord ++ tailWord_3376782) baseStart_3376782 baseEnd_3376782 := by
    simpa [prefixWord, tailWord_3376782, baseEnd_3376782] using wordTrace_append hprefix tailTrace_3376782
  have hstable : (prefixWord ++ tailWord_3376782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376782).length < 2 ^ (prefixWord ++ tailWord_3376782).sum := by decide
  have hdescent : baseEnd_3376782 < baseStart_3376782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376823 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 6]
def baseStart_3376823 : Nat := 118140960795 + 3376823 * 2 ^ 59
def prefixEnd_3376823 : Nat := 4983230072969 + 3 ^ 40 * 3376823 * 2
def baseEnd_3376823 : Nat := 385318507590565977373951

theorem tailTrace_3376823 : CollatzResearch.WordTrace tailWord_3376823 prefixEnd_3376823 385318507590565977373951 := by
  unfold tailWord_3376823
  simp only [CollatzResearch.WordTrace]
  refine ⟨123162853045354461298847123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82108568696902974199231415 123162853045354461298847123)
  ·
    refine ⟨184744279568031691948270685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123162853045354461298847123 184744279568031691948270685)
    ·
      refine ⟨69279104838011884480601507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184744279568031691948270685 69279104838011884480601507)
      ·
        refine ⟨103918657257017826720902261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69279104838011884480601507 103918657257017826720902261)
        ·
          refine ⟨9742374117845421255084587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103918657257017826720902261 9742374117845421255084587)
          ·
            refine ⟨14613561176768131882626881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9742374117845421255084587 14613561176768131882626881)
            ·
              refine ⟨10960170882576098911970161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14613561176768131882626881 10960170882576098911970161)
              ·
                refine ⟨8220128161932074183977621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10960170882576098911970161 8220128161932074183977621)
                ·
                  refine ⟨385318507590565977373951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8220128161932074183977621 385318507590565977373951)
                  ·
                    rfl

theorem cell22_3376823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 6].length) (baseStart_3376823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376823 prefixEnd_3376823 := by exact prefixLift 3376823
  have htrace : WordTrace (prefixWord ++ tailWord_3376823) baseStart_3376823 baseEnd_3376823 := by
    simpa [prefixWord, tailWord_3376823, baseEnd_3376823] using wordTrace_append hprefix tailTrace_3376823
  have hstable : (prefixWord ++ tailWord_3376823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376823).length < 2 ^ (prefixWord ++ tailWord_3376823).sum := by decide
  have hdescent : baseEnd_3376823 < baseStart_3376823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376855 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 2, 3]
def baseStart_3376855 : Nat := 118140960795 + 3376855 * 2 ^ 59
def prefixEnd_3376855 : Nat := 4983230072969 + 3 ^ 40 * 3376855 * 2
def baseEnd_3376855 : Nat := 1155966477025660515321755

theorem tailTrace_3376855 : CollatzResearch.WordTrace tailWord_3376855 prefixEnd_3376855 1155966477025660515321755 := by
  unfold tailWord_3376855
  simp only [CollatzResearch.WordTrace]
  refine ⟨123164020181238530764012019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82109346787492353842674679 123164020181238530764012019)
  ·
    refine ⟨184746030271857796146018029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123164020181238530764012019 184746030271857796146018029)
    ·
      refine ⟨69279761351946673554756761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184746030271857796146018029 69279761351946673554756761)
      ·
        refine ⟨51959821013960005166067571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69279761351946673554756761 51959821013960005166067571)
        ·
          refine ⟨77939731520940007749101357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51959821013960005166067571 77939731520940007749101357)
          ·
            refine ⟨29227399320352502905913009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77939731520940007749101357 29227399320352502905913009)
            ·
              refine ⟨21920549490264377179434757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29227399320352502905913009 21920549490264377179434757)
              ·
                refine ⟨4110103029424570721144017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21920549490264377179434757 4110103029424570721144017)
                ·
                  refine ⟨3082577272068428040858013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4110103029424570721144017 3082577272068428040858013)
                  ·
                    refine ⟨1155966477025660515321755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082577272068428040858013 1155966477025660515321755)
                    ·
                      rfl

theorem cell22_3376855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_3376855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376855 prefixEnd_3376855 := by exact prefixLift 3376855
  have htrace : WordTrace (prefixWord ++ tailWord_3376855) baseStart_3376855 baseEnd_3376855 := by
    simpa [prefixWord, tailWord_3376855, baseEnd_3376855] using wordTrace_append hprefix tailTrace_3376855
  have hstable : (prefixWord ++ tailWord_3376855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376855).length < 2 ^ (prefixWord ++ tailWord_3376855).sum := by decide
  have hdescent : baseEnd_3376855 < baseStart_3376855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376857 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 4]
def baseStart_3376857 : Nat := 118140960795 + 3376857 * 2 ^ 59
def prefixEnd_3376857 : Nat := 4983230072969 + 3 ^ 40 * 3376857 * 2
def baseEnd_3376857 : Nat := 385322387222177725590583

theorem tailTrace_3376857 : CollatzResearch.WordTrace tailWord_3376857 prefixEnd_3376857 385322387222177725590583 := by
  unfold tailWord_3376857
  simp only [CollatzResearch.WordTrace]
  refine ⟨123164093127231285105584825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82109395418154190070389883 123164093127231285105584825)
  ·
    refine ⟨92373069845423463829188619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123164093127231285105584825 92373069845423463829188619)
    ·
      refine ⟨138559604768135195743782929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92373069845423463829188619 138559604768135195743782929)
      ·
        refine ⟨103919703576101396807837197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138559604768135195743782929 103919703576101396807837197)
        ·
          refine ⟨38969888841038023802938949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103919703576101396807837197 38969888841038023802938949)
          ·
            refine ⟨7306854157694629463051053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38969888841038023802938949 7306854157694629463051053)
            ·
              refine ⟨2740070309135486048644145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7306854157694629463051053 2740070309135486048644145)
              ·
                refine ⟨2055052731851614536483109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740070309135486048644145 2055052731851614536483109)
                ·
                  refine ⟨385322387222177725590583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055052731851614536483109 385322387222177725590583)
                  ·
                    rfl

theorem cell22_3376857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_3376857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376857 prefixEnd_3376857 := by exact prefixLift 3376857
  have htrace : WordTrace (prefixWord ++ tailWord_3376857) baseStart_3376857 baseEnd_3376857 := by
    simpa [prefixWord, tailWord_3376857, baseEnd_3376857] using wordTrace_append hprefix tailTrace_3376857
  have hstable : (prefixWord ++ tailWord_3376857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376857).length < 2 ^ (prefixWord ++ tailWord_3376857).sum := by decide
  have hdescent : baseEnd_3376857 < baseStart_3376857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376868 : List Nat := [2, 3, 1, 1, 1, 3, 4, 7]
def baseStart_3376868 : Nat := 118140960795 + 3376868 * 2 ^ 59
def prefixEnd_3376868 : Nat := 4983230072969 + 3 ^ 40 * 3376868 * 2
def baseEnd_3376868 : Nat := 128441214132370312749635

theorem tailTrace_3376868 : CollatzResearch.WordTrace tailWord_3376868 prefixEnd_3376868 128441214132370312749635 := by
  unfold tailWord_3376868
  simp only [CollatzResearch.WordTrace]
  refine ⟨61582247165095716992117629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82109662886794289322823505 61582247165095716992117629)
  ·
    refine ⟨23093342686910893872044111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61582247165095716992117629 23093342686910893872044111)
    ·
      refine ⟨34640014030366340808066167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23093342686910893872044111 34640014030366340808066167)
      ·
        refine ⟨51960021045549511212099251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34640014030366340808066167 51960021045549511212099251)
        ·
          refine ⟨77940031568324266818148877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51960021045549511212099251 77940031568324266818148877)
          ·
            refine ⟨29227511838121600056805829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77940031568324266818148877 29227511838121600056805829)
            ·
              refine ⟨5480158469647800010651093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29227511838121600056805829 5480158469647800010651093)
              ·
                refine ⟨128441214132370312749635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5480158469647800010651093 128441214132370312749635)
                ·
                  rfl

theorem cell22_3376868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_3376868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376868 prefixEnd_3376868 := by exact prefixLift 3376868
  have htrace : WordTrace (prefixWord ++ tailWord_3376868) baseStart_3376868 baseEnd_3376868 := by
    simpa [prefixWord, tailWord_3376868, baseEnd_3376868] using wordTrace_append hprefix tailTrace_3376868
  have hstable : (prefixWord ++ tailWord_3376868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376868).length < 2 ^ (prefixWord ++ tailWord_3376868).sum := by decide
  have hdescent : baseEnd_3376868 < baseStart_3376868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376872 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_3376872 : Nat := 118140960795 + 3376872 * 2 ^ 59
def prefixEnd_3376872 : Nat := 4983230072969 + 3 ^ 40 * 3376872 * 2
def baseEnd_3376872 : Nat := 1155972296473078137646703

theorem tailTrace_3376872 : CollatzResearch.WordTrace tailWord_3376872 prefixEnd_3376872 1155972296473078137646703 := by
  unfold tailWord_3376872
  simp only [CollatzResearch.WordTrace]
  refine ⟨61582320111088471333690435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82109760148117961778253913 61582320111088471333690435)
  ·
    refine ⟨92373480166632707000535653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61582320111088471333690435 92373480166632707000535653)
    ·
      refine ⟨17320027531243632562600435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92373480166632707000535653 17320027531243632562600435)
      ·
        refine ⟨25980041296865448843900653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17320027531243632562600435 25980041296865448843900653)
        ·
          refine ⟨9742515486324543316462745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25980041296865448843900653 9742515486324543316462745)
          ·
            refine ⟨7306886614743407487347059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9742515486324543316462745 7306886614743407487347059)
            ·
              refine ⟨10960329922115111231020589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306886614743407487347059 10960329922115111231020589)
              ·
                refine ⟨4110123720793166711632721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10960329922115111231020589 4110123720793166711632721)
                ·
                  refine ⟨3082592790594875033724541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4110123720793166711632721 3082592790594875033724541)
                  ·
                    refine ⟨1155972296473078137646703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082592790594875033724541 1155972296473078137646703)
                    ·
                      rfl

theorem cell22_3376872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_3376872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376872 prefixEnd_3376872 := by exact prefixLift 3376872
  have htrace : WordTrace (prefixWord ++ tailWord_3376872) baseStart_3376872 baseEnd_3376872 := by
    simpa [prefixWord, tailWord_3376872, baseEnd_3376872] using wordTrace_append hprefix tailTrace_3376872
  have hstable : (prefixWord ++ tailWord_3376872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376872).length < 2 ^ (prefixWord ++ tailWord_3376872).sum := by decide
  have hdescent : baseEnd_3376872 < baseStart_3376872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376930 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3376930 : Nat := 118140960795 + 3376930 * 2 ^ 59
def prefixEnd_3376930 : Nat := 4983230072969 + 3 ^ 40 * 3376930 * 2
def baseEnd_3376930 : Nat := 385330717019461773232175

theorem tailTrace_3376930 : CollatzResearch.WordTrace tailWord_3376930 prefixEnd_3376930 385330717019461773232175 := by
  unfold tailWord_3376930
  simp only [CollatzResearch.WordTrace]
  refine ⟨30791688913991704643248061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82111170437311212381994829 30791688913991704643248061)
  ·
    refine ⟨11546883342746889241218023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30791688913991704643248061 11546883342746889241218023)
    ·
      refine ⟨17320325014120333861827035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11546883342746889241218023 17320325014120333861827035)
      ·
        refine ⟨25980487521180500792740553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17320325014120333861827035 25980487521180500792740553)
        ·
          refine ⟨19485365640885375594555415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25980487521180500792740553 19485365640885375594555415)
          ·
            refine ⟨29228048461328063391833123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19485365640885375594555415 29228048461328063391833123)
            ·
              refine ⟨43842072691992095087749685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29228048461328063391833123 43842072691992095087749685)
              ·
                refine ⟨4110194314874258914476533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43842072691992095087749685 4110194314874258914476533)
                ·
                  refine ⟨385330717019461773232175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4110194314874258914476533 385330717019461773232175)
                  ·
                    rfl

theorem cell22_3376930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3376930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376930 prefixEnd_3376930 := by exact prefixLift 3376930
  have htrace : WordTrace (prefixWord ++ tailWord_3376930) baseStart_3376930 baseEnd_3376930 := by
    simpa [prefixWord, tailWord_3376930, baseEnd_3376930] using wordTrace_append hprefix tailTrace_3376930
  have hstable : (prefixWord ++ tailWord_3376930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376930).length < 2 ^ (prefixWord ++ tailWord_3376930).sum := by decide
  have hdescent : baseEnd_3376930 < baseStart_3376930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376994 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3376994 : Nat := 118140960795 + 3376994 * 2 ^ 59
def prefixEnd_3376994 : Nat := 4983230072969 + 3 ^ 40 * 3376994 * 2
def baseEnd_3376994 : Nat := 1156014059566310486096329

theorem tailTrace_3376994 : CollatzResearch.WordTrace tailWord_3376994 prefixEnd_3376994 1156014059566310486096329 := by
  unfold tailWord_3376994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30792272481933739375830509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82112726618489971668881357 30792272481933739375830509)
  ·
    refine ⟨11547102180725152265936441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30792272481933739375830509 11547102180725152265936441)
    ·
      refine ⟨8660326635543864199452331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11547102180725152265936441 8660326635543864199452331)
      ·
        refine ⟨12990489953315796299178497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8660326635543864199452331 12990489953315796299178497)
        ·
          refine ⟨9742867464986847224383873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12990489953315796299178497 9742867464986847224383873)
          ·
            refine ⟨7307150598740135418287905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9742867464986847224383873 7307150598740135418287905)
            ·
              refine ⟨5480362949055101563715929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7307150598740135418287905 5480362949055101563715929)
              ·
                refine ⟨4110272211791326172786947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480362949055101563715929 4110272211791326172786947)
                ·
                  refine ⟨6165408317686989259180421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110272211791326172786947 6165408317686989259180421)
                  ·
                    refine ⟨1156014059566310486096329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6165408317686989259180421 1156014059566310486096329)
                    ·
                      rfl

theorem cell22_3376994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3376994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3376994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3376994 prefixEnd_3376994 := by exact prefixLift 3376994
  have htrace : WordTrace (prefixWord ++ tailWord_3376994) baseStart_3376994 baseEnd_3376994 := by
    simpa [prefixWord, tailWord_3376994, baseEnd_3376994] using wordTrace_append hprefix tailTrace_3376994
  have hstable : (prefixWord ++ tailWord_3376994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376994).length < 2 ^ (prefixWord ++ tailWord_3376994).sum := by decide
  have hdescent : baseEnd_3376994 < baseStart_3376994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377005 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3377005 : Nat := 118140960795 + 3377005 * 2 ^ 59
def prefixEnd_3377005 : Nat := 4983230072969 + 3 ^ 40 * 3377005 * 2
def baseEnd_3377005 : Nat := 1156017825091110124071295

theorem tailTrace_3377005 : CollatzResearch.WordTrace tailWord_3377005 prefixEnd_3377005 1156017825091110124071295 := by
  unfold tailWord_3377005
  simp only [CollatzResearch.WordTrace]
  refine ⟨123169491130695106381972469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82112994087130070921314979 123169491130695106381972469)
  ·
    refine ⟨11547139793502666223309919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123169491130695106381972469 11547139793502666223309919)
    ·
      refine ⟨17320709690253999334964879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11547139793502666223309919 17320709690253999334964879)
      ·
        refine ⟨25981064535380999002447319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17320709690253999334964879 25981064535380999002447319)
        ·
          refine ⟨38971596803071498503670979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25981064535380999002447319 38971596803071498503670979)
          ·
            refine ⟨58457395204607247755506469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38971596803071498503670979 58457395204607247755506469)
            ·
              refine ⟨10960761600863858954157463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58457395204607247755506469 10960761600863858954157463)
              ·
                refine ⟨16441142401295788431236195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10960761600863858954157463 16441142401295788431236195)
                ·
                  refine ⟨24661713601943682646854293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16441142401295788431236195 24661713601943682646854293)
                  ·
                    refine ⟨1156017825091110124071295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24661713601943682646854293 1156017825091110124071295)
                    ·
                      rfl

theorem cell22_3377005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3377005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377005 prefixEnd_3377005 := by exact prefixLift 3377005
  have htrace : WordTrace (prefixWord ++ tailWord_3377005) baseStart_3377005 baseEnd_3377005 := by
    simpa [prefixWord, tailWord_3377005, baseEnd_3377005] using wordTrace_append hprefix tailTrace_3377005
  have hstable : (prefixWord ++ tailWord_3377005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377005).length < 2 ^ (prefixWord ++ tailWord_3377005).sum := by decide
  have hdescent : baseEnd_3377005 < baseStart_3377005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377080 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_3377080 : Nat := 118140960795 + 3377080 * 2 ^ 59
def prefixEnd_3377080 : Nat := 4983230072969 + 3 ^ 40 * 3377080 * 2
def baseEnd_3377080 : Nat := 1156043499123834928446065

theorem tailTrace_3377080 : CollatzResearch.WordTrace tailWord_3377080 prefixEnd_3377080 1156043499123834928446065 := by
  unfold tailWord_3377080
  simp only [CollatzResearch.WordTrace]
  refine ⟨61586113302711697095476347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82114817736948929460635129 61586113302711697095476347)
  ·
    refine ⟨92379169954067545643214521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61586113302711697095476347 92379169954067545643214521)
    ·
      refine ⟨69284377465550659232410891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92379169954067545643214521 69284377465550659232410891)
      ·
        refine ⟨103926566198325988848616337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69284377465550659232410891 103926566198325988848616337)
        ·
          refine ⟨77944924648744491636462253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103926566198325988848616337 77944924648744491636462253)
          ·
            refine ⟨29229346743279184363673345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77944924648744491636462253 29229346743279184363673345)
            ·
              refine ⟨21922010057459388272755009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29229346743279184363673345 21922010057459388272755009)
              ·
                refine ⟨16441507543094541204566257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21922010057459388272755009 16441507543094541204566257)
                ·
                  refine ⟨12331130657320905903424693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16441507543094541204566257 12331130657320905903424693)
                  ·
                    refine ⟨1156043499123834928446065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12331130657320905903424693 1156043499123834928446065)
                    ·
                      rfl

theorem cell22_3377080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_3377080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377080 prefixEnd_3377080 := by exact prefixLift 3377080
  have htrace : WordTrace (prefixWord ++ tailWord_3377080) baseStart_3377080 baseEnd_3377080 := by
    simpa [prefixWord, tailWord_3377080, baseEnd_3377080] using wordTrace_append hprefix tailTrace_3377080
  have hstable : (prefixWord ++ tailWord_3377080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377080).length < 2 ^ (prefixWord ++ tailWord_3377080).sum := by decide
  have hdescent : baseEnd_3377080 < baseStart_3377080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377086 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3377086 : Nat := 118140960795 + 3377086 * 2 ^ 59
def prefixEnd_3377086 : Nat := 4983230072969 + 3 ^ 40 * 3377086 * 2
def baseEnd_3377086 : Nat := 1156045553046452912796047

theorem tailTrace_3377086 : CollatzResearch.WordTrace tailWord_3377086 prefixEnd_3377086 1156045553046452912796047 := by
  unfold tailWord_3377086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15396555680425207151958889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82114963628934438143780741 15396555680425207151958889)
  ·
    refine ⟨11547416760318905363969167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15396555680425207151958889 11547416760318905363969167)
    ·
      refine ⟨17321125140478358045953751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11547416760318905363969167 17321125140478358045953751)
      ·
        refine ⟨25981687710717537068930627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17321125140478358045953751 25981687710717537068930627)
        ·
          refine ⟨38972531566076305603395941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25981687710717537068930627 38972531566076305603395941)
          ·
            refine ⟨7307349668639307300636739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38972531566076305603395941 7307349668639307300636739)
            ·
              refine ⟨10961024502958960950955109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307349668639307300636739 10961024502958960950955109)
              ·
                refine ⟨2055192094304805178304083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10961024502958960950955109 2055192094304805178304083)
                ·
                  refine ⟨3082788141457207767456125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055192094304805178304083 3082788141457207767456125)
                  ·
                    refine ⟨1156045553046452912796047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082788141457207767456125 1156045553046452912796047)
                    ·
                      rfl

theorem cell22_3377086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3377086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377086 prefixEnd_3377086 := by exact prefixLift 3377086
  have htrace : WordTrace (prefixWord ++ tailWord_3377086) baseStart_3377086 baseEnd_3377086 := by
    simpa [prefixWord, tailWord_3377086, baseEnd_3377086] using wordTrace_append hprefix tailTrace_3377086
  have hstable : (prefixWord ++ tailWord_3377086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377086).length < 2 ^ (prefixWord ++ tailWord_3377086).sum := by decide
  have hdescent : baseEnd_3377086 < baseStart_3377086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377112 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_3377112 : Nat := 118140960795 + 3377112 * 2 ^ 59
def prefixEnd_3377112 : Nat := 4983230072969 + 3 ^ 40 * 3377112 * 2
def baseEnd_3377112 : Nat := 1156054453377797511645967

theorem tailTrace_3377112 : CollatzResearch.WordTrace tailWord_3377112 prefixEnd_3377112 1156054453377797511645967 := by
  unfold tailWord_3377112
  simp only [CollatzResearch.WordTrace]
  refine ⟨61586696870653731828058795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82115595827538309104078393 61586696870653731828058795)
  ·
    refine ⟨92380045305980597742088193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61586696870653731828058795 92380045305980597742088193)
    ·
      refine ⟨69285033979485448306566145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92380045305980597742088193 69285033979485448306566145)
      ·
        refine ⟨51963775484614086229924609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69285033979485448306566145 51963775484614086229924609)
        ·
          refine ⟨38972831613460564672443457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51963775484614086229924609 38972831613460564672443457)
          ·
            refine ⟨29229623710095423504332593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38972831613460564672443457 29229623710095423504332593)
            ·
              refine ⟨21922217782571567628249445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29229623710095423504332593 21922217782571567628249445)
              ·
                refine ⟨4110415834232168930296771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21922217782571567628249445 4110415834232168930296771)
                ·
                  refine ⟨6165623751348253395445157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110415834232168930296771 6165623751348253395445157)
                  ·
                    refine ⟨1156054453377797511645967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6165623751348253395445157 1156054453377797511645967)
                    ·
                      rfl

theorem cell22_3377112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_3377112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377112 prefixEnd_3377112 := by exact prefixLift 3377112
  have htrace : WordTrace (prefixWord ++ tailWord_3377112) baseStart_3377112 baseEnd_3377112 := by
    simpa [prefixWord, tailWord_3377112, baseEnd_3377112] using wordTrace_append hprefix tailTrace_3377112
  have hstable : (prefixWord ++ tailWord_3377112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377112).length < 2 ^ (prefixWord ++ tailWord_3377112).sum := by decide
  have hdescent : baseEnd_3377112 < baseStart_3377112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377133 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3377133 : Nat := 118140960795 + 3377133 * 2 ^ 59
def prefixEnd_3377133 : Nat := 4983230072969 + 3 ^ 40 * 3377133 * 2
def baseEnd_3377133 : Nat := 385353880702320152290301

theorem tailTrace_3377133 : CollatzResearch.WordTrace tailWord_3377133 prefixEnd_3377133 385353880702320152290301 := by
  unfold tailWord_3377133
  simp only [CollatzResearch.WordTrace]
  refine ⟨123174159674231384242632053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82116106449487589495088035 123174159674231384242632053)
  ·
    refine ⟨11547577469459192272746755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123174159674231384242632053 11547577469459192272746755)
    ·
      refine ⟨17321366204188788409120133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11547577469459192272746755 17321366204188788409120133)
      ·
        refine ⟨3247756163285397826710025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17321366204188788409120133 3247756163285397826710025)
        ·
          refine ⟨2435817122464048370032519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3247756163285397826710025 2435817122464048370032519)
          ·
            refine ⟨3653725683696072555048779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435817122464048370032519 3653725683696072555048779)
            ·
              refine ⟨5480588525544108832573169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653725683696072555048779 5480588525544108832573169)
              ·
                refine ⟨4110441394158081624429877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480588525544108832573169 4110441394158081624429877)
                ·
                  refine ⟨385353880702320152290301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4110441394158081624429877 385353880702320152290301)
                  ·
                    rfl

theorem cell22_3377133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3377133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377133 prefixEnd_3377133 := by exact prefixLift 3377133
  have htrace : WordTrace (prefixWord ++ tailWord_3377133) baseStart_3377133 baseEnd_3377133 := by
    simpa [prefixWord, tailWord_3377133, baseEnd_3377133] using wordTrace_append hprefix tailTrace_3377133
  have hstable : (prefixWord ++ tailWord_3377133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377133).length < 2 ^ (prefixWord ++ tailWord_3377133).sum := by decide
  have hdescent : baseEnd_3377133 < baseStart_3377133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377159 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 1, 5]
def baseStart_3377159 : Nat := 118140960795 + 3377159 * 2 ^ 59
def prefixEnd_3377159 : Nat := 4983230072969 + 3 ^ 40 * 3377159 * 2
def baseEnd_3377159 : Nat := 1156070542438305055720823

theorem tailTrace_3377159 : CollatzResearch.WordTrace tailWord_3377159 prefixEnd_3377159 1156070542438305055720823 := by
  unfold tailWord_3377159
  simp only [CollatzResearch.WordTrace]
  refine ⟨123175107972137190683078531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82116738648091460455385687 123175107972137190683078531)
  ·
    refine ⟨184762661958205786024617797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123175107972137190683078531 184762661958205786024617797)
    ·
      refine ⟨34642999117163584879615837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184762661958205786024617797 34642999117163584879615837)
      ·
        refine ⟨12991124668936344329855939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34642999117163584879615837 12991124668936344329855939)
        ·
          refine ⟨19486687003404516494783909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12991124668936344329855939 19486687003404516494783909)
          ·
            refine ⟨3653753813138346842771983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19486687003404516494783909 3653753813138346842771983)
            ·
              refine ⟨5480630719707520264157975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653753813138346842771983 5480630719707520264157975)
              ·
                refine ⟨8220946079561280396236963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480630719707520264157975 8220946079561280396236963)
                ·
                  refine ⟨12331419119341920594355445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8220946079561280396236963 12331419119341920594355445)
                  ·
                    refine ⟨1156070542438305055720823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12331419119341920594355445 1156070542438305055720823)
                    ·
                      rfl

theorem cell22_3377159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_3377159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377159 prefixEnd_3377159 := by exact prefixLift 3377159
  have htrace : WordTrace (prefixWord ++ tailWord_3377159) baseStart_3377159 baseEnd_3377159 := by
    simpa [prefixWord, tailWord_3377159, baseEnd_3377159] using wordTrace_append hprefix tailTrace_3377159
  have hstable : (prefixWord ++ tailWord_3377159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377159).length < 2 ^ (prefixWord ++ tailWord_3377159).sum := by decide
  have hdescent : baseEnd_3377159 < baseStart_3377159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377191 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3377191 : Nat := 118140960795 + 3377191 * 2 ^ 59
def prefixEnd_3377191 : Nat := 4983230072969 + 3 ^ 40 * 3377191 * 2
def baseEnd_3377191 : Nat := 1156081496692267638920725

theorem tailTrace_3377191 : CollatzResearch.WordTrace tailWord_3377191 prefixEnd_3377191 1156081496692267638920725 := by
  unfold tailWord_3377191
  simp only [CollatzResearch.WordTrace]
  refine ⟨123176275108021260148243427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82117516738680840098828951 123176275108021260148243427)
  ·
    refine ⟨184764412662031890222365141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123176275108021260148243427 184764412662031890222365141)
    ·
      refine ⟨4330415921766372427086683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 184764412662031890222365141 4330415921766372427086683)
      ·
        refine ⟨6495623882649558640630025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4330415921766372427086683 6495623882649558640630025)
        ·
          refine ⟨4871717911987168980472519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6495623882649558640630025 4871717911987168980472519)
          ·
            refine ⟨7307576867980753470708779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871717911987168980472519 7307576867980753470708779)
            ·
              refine ⟨10961365301971130206063169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307576867980753470708779 10961365301971130206063169)
              ·
                refine ⟨8221023976478347654547377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10961365301971130206063169 8221023976478347654547377)
                ·
                  refine ⟨6165767982358760740910533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8221023976478347654547377 6165767982358760740910533)
                  ·
                    refine ⟨1156081496692267638920725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6165767982358760740910533 1156081496692267638920725)
                    ·
                      rfl

theorem cell22_3377191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3377191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377191 prefixEnd_3377191 := by exact prefixLift 3377191
  have htrace : WordTrace (prefixWord ++ tailWord_3377191) baseStart_3377191 baseEnd_3377191 := by
    simpa [prefixWord, tailWord_3377191, baseEnd_3377191] using wordTrace_append hprefix tailTrace_3377191
  have hstable : (prefixWord ++ tailWord_3377191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377191).length < 2 ^ (prefixWord ++ tailWord_3377191).sum := by decide
  have hdescent : baseEnd_3377191 < baseStart_3377191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377311 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 4, 3]
def baseStart_3377311 : Nat := 118140960795 + 3377311 * 2 ^ 59
def prefixEnd_3377311 : Nat := 4983230072969 + 3 ^ 40 * 3377311 * 2
def baseEnd_3377311 : Nat := 1156122575144627325920357

theorem tailTrace_3377311 : CollatzResearch.WordTrace tailWord_3377311 prefixEnd_3377311 1156122575144627325920357 := by
  unfold tailWord_3377311
  simp only [CollatzResearch.WordTrace]
  refine ⟨123180651867586520642611787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82120434578391013761741191 123180651867586520642611787)
  ·
    refine ⟨184770977801379780963917681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123180651867586520642611787 184770977801379780963917681)
    ·
      refine ⟨138578233351034835722938261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184770977801379780963917681 138578233351034835722938261)
      ·
        refine ⟨6495854688329757924512731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138578233351034835722938261 6495854688329757924512731)
        ·
          refine ⟨9743782032494636886769097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6495854688329757924512731 9743782032494636886769097)
          ·
            refine ⟨7307836524370977665076823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9743782032494636886769097 7307836524370977665076823)
            ·
              refine ⟨10961754786556466497615235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307836524370977665076823 10961754786556466497615235)
              ·
                refine ⟨16442632179834699746422853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10961754786556466497615235 16442632179834699746422853)
                ·
                  refine ⟨3082993533719006202454285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16442632179834699746422853 3082993533719006202454285)
                  ·
                    refine ⟨1156122575144627325920357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082993533719006202454285 1156122575144627325920357)
                    ·
                      rfl

theorem cell22_3377311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_3377311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377311 prefixEnd_3377311 := by exact prefixLift 3377311
  have htrace : WordTrace (prefixWord ++ tailWord_3377311) baseStart_3377311 baseEnd_3377311 := by
    simpa [prefixWord, tailWord_3377311, baseEnd_3377311] using wordTrace_append hprefix tailTrace_3377311
  have hstable : (prefixWord ++ tailWord_3377311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377311).length < 2 ^ (prefixWord ++ tailWord_3377311).sum := by decide
  have hdescent : baseEnd_3377311 < baseStart_3377311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377332 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3377332 : Nat := 118140960795 + 3377332 * 2 ^ 59
def prefixEnd_3377332 : Nat := 4983230072969 + 3 ^ 40 * 3377332 * 2
def baseEnd_3377332 : Nat := 1156129763873790271145293

theorem tailTrace_3377332 : CollatzResearch.WordTrace tailWord_3377332 prefixEnd_3377332 1156129763873790271145293 := by
  unfold tailWord_3377332
  simp only [CollatzResearch.WordTrace]
  refine ⟨61590708900255220614563125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82120945200340294152750833 61590708900255220614563125)
  ·
    refine ⟨5774128959398926932615293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61590708900255220614563125 5774128959398926932615293)
    ·
      refine ⟨2165298359774597599730735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5774128959398926932615293 2165298359774597599730735)
      ·
        refine ⟨3247947539661896399596103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165298359774597599730735 3247947539661896399596103)
        ·
          refine ⟨4871921309492844599394155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247947539661896399596103 4871921309492844599394155)
          ·
            refine ⟨7307881964239266899091233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871921309492844599394155 7307881964239266899091233)
            ·
              refine ⟨5480911473179450174318425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7307881964239266899091233 5480911473179450174318425)
              ·
                refine ⟨4110683604884587630738819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480911473179450174318425 4110683604884587630738819)
                ·
                  refine ⟨6166025407326881446108229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110683604884587630738819 6166025407326881446108229)
                  ·
                    refine ⟨1156129763873790271145293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166025407326881446108229 1156129763873790271145293)
                    ·
                      rfl

theorem cell22_3377332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3377332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377332 prefixEnd_3377332 := by exact prefixLift 3377332
  have htrace : WordTrace (prefixWord ++ tailWord_3377332) baseStart_3377332 baseEnd_3377332 := by
    simpa [prefixWord, tailWord_3377332, baseEnd_3377332] using wordTrace_append hprefix tailTrace_3377332
  have hstable : (prefixWord ++ tailWord_3377332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377332).length < 2 ^ (prefixWord ++ tailWord_3377332).sum := by decide
  have hdescent : baseEnd_3377332 < baseStart_3377332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377339 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 3, 3]
def baseStart_3377339 : Nat := 118140960795 + 3377339 * 2 ^ 59
def prefixEnd_3377339 : Nat := 4983230072969 + 3 ^ 40 * 3377339 * 2
def baseEnd_3377339 : Nat := 1156132160116844586220271

theorem tailTrace_3377339 : CollatzResearch.WordTrace tailWord_3377339 prefixEnd_3377339 1156132160116844586220271 := by
  unfold tailWord_3377339
  simp only [CollatzResearch.WordTrace]
  refine ⟨123181673111485081424631071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82121115407656720949754047 123181673111485081424631071)
  ·
    refine ⟨184772509667227622136946607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123181673111485081424631071 184772509667227622136946607)
    ·
      refine ⟨277158764500841433205419911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184772509667227622136946607 277158764500841433205419911)
      ·
        refine ⟨415738146751262149808129867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277158764500841433205419911 415738146751262149808129867)
        ·
          refine ⟨623607220126893224712194801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415738146751262149808129867 623607220126893224712194801)
          ·
            refine ⟨467705415095169918534146101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623607220126893224712194801 467705415095169918534146101)
            ·
              refine ⟨43847382665172179862576197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 467705415095169918534146101 43847382665172179862576197)
              ·
                refine ⟨8221384249719783724233037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43847382665172179862576197 8221384249719783724233037)
                ·
                  refine ⟨3083019093644918896587389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8221384249719783724233037 3083019093644918896587389)
                  ·
                    refine ⟨1156132160116844586220271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083019093644918896587389 1156132160116844586220271)
                    ·
                      rfl

theorem cell22_3377339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 3].length) (baseStart_3377339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377339 prefixEnd_3377339 := by exact prefixLift 3377339
  have htrace : WordTrace (prefixWord ++ tailWord_3377339) baseStart_3377339 baseEnd_3377339 := by
    simpa [prefixWord, tailWord_3377339, baseEnd_3377339] using wordTrace_append hprefix tailTrace_3377339
  have hstable : (prefixWord ++ tailWord_3377339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377339).length < 2 ^ (prefixWord ++ tailWord_3377339).sum := by decide
  have hdescent : baseEnd_3377339 < baseStart_3377339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377373 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3377373 : Nat := 118140960795 + 3377373 * 2 ^ 59
def prefixEnd_3377373 : Nat := 4983230072969 + 3 ^ 40 * 3377373 * 2
def baseEnd_3377373 : Nat := 1156143799011679830870167

theorem tailTrace_3377373 : CollatzResearch.WordTrace tailWord_3377373 prefixEnd_3377373 1156143799011679830870167 := by
  unfold tailWord_3377373
  simp only [CollatzResearch.WordTrace]
  refine ⟨123182913193361905231368773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82121942128907936820912515 123182913193361905231368773)
  ·
    refine ⟨23096796223755357230881645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123182913193361905231368773 23096796223755357230881645)
    ·
      refine ⟨8661298583908258961580617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23096796223755357230881645 8661298583908258961580617)
      ·
        refine ⟨6495973937931194221185463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8661298583908258961580617 6495973937931194221185463)
        ·
          refine ⟨9743960906896791331778195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6495973937931194221185463 9743960906896791331778195)
          ·
            refine ⟨14615941360345186997667293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743960906896791331778195 14615941360345186997667293)
            ·
              refine ⟨5480978010129445124125235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14615941360345186997667293 5480978010129445124125235)
              ·
                refine ⟨8221467015194167686187853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480978010129445124125235 8221467015194167686187853)
                ·
                  refine ⟨3083050130697812882320445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8221467015194167686187853 3083050130697812882320445)
                  ·
                    refine ⟨1156143799011679830870167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083050130697812882320445 1156143799011679830870167)
                    ·
                      rfl

theorem cell22_3377373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3377373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377373 prefixEnd_3377373 := by exact prefixLift 3377373
  have htrace : WordTrace (prefixWord ++ tailWord_3377373) baseStart_3377373 baseEnd_3377373 := by
    simpa [prefixWord, tailWord_3377373, baseEnd_3377373] using wordTrace_append hprefix tailTrace_3377373
  have hstable : (prefixWord ++ tailWord_3377373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377373).length < 2 ^ (prefixWord ++ tailWord_3377373).sum := by decide
  have hdescent : baseEnd_3377373 < baseStart_3377373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377519 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_3377519 : Nat := 118140960795 + 3377519 * 2 ^ 59
def prefixEnd_3377519 : Nat := 4983230072969 + 3 ^ 40 * 3377519 * 2
def baseEnd_3377519 : Nat := 1156193777795384116719719

theorem tailTrace_3377519 : CollatzResearch.WordTrace tailWord_3377519 prefixEnd_3377519 1156193777795384116719719 := by
  unfold tailWord_3377519
  simp only [CollatzResearch.WordTrace]
  refine ⟨123188238250832972166183611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82125492167221981444122407 123188238250832972166183611)
  ·
    refine ⟨184782357376249458249275417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123188238250832972166183611 184782357376249458249275417)
    ·
      refine ⟨138586768032187093686956563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184782357376249458249275417 138586768032187093686956563)
      ·
        refine ⟨207880152048280640530434845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138586768032187093686956563 207880152048280640530434845)
        ·
          refine ⟨77955057018105240198913067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207880152048280640530434845 77955057018105240198913067)
          ·
            refine ⟨116932585527157860298369601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77955057018105240198913067 116932585527157860298369601)
            ·
              refine ⟨87699439145368395223777201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116932585527157860298369601 87699439145368395223777201)
              ·
                refine ⟨65774579359026296417832901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87699439145368395223777201 65774579359026296417832901)
                ·
                  refine ⟨12332733629817430578343669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65774579359026296417832901 12332733629817430578343669)
                  ·
                    refine ⟨1156193777795384116719719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12332733629817430578343669 1156193777795384116719719)
                    ·
                      rfl

theorem cell22_3377519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_3377519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377519 prefixEnd_3377519 := by exact prefixLift 3377519
  have htrace : WordTrace (prefixWord ++ tailWord_3377519) baseStart_3377519 baseEnd_3377519 := by
    simpa [prefixWord, tailWord_3377519, baseEnd_3377519] using wordTrace_append hprefix tailTrace_3377519
  have hstable : (prefixWord ++ tailWord_3377519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377519).length < 2 ^ (prefixWord ++ tailWord_3377519).sum := by decide
  have hdescent : baseEnd_3377519 < baseStart_3377519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377568 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_3377568 : Nat := 118140960795 + 3377568 * 2 ^ 59
def prefixEnd_3377568 : Nat := 4983230072969 + 3 ^ 40 * 3377568 * 2
def baseEnd_3377568 : Nat := 1156210551496764322244569

theorem tailTrace_3377568 : CollatzResearch.WordTrace tailWord_3377568 prefixEnd_3377568 1156210551496764322244569 := by
  unfold tailWord_3377568
  simp only [CollatzResearch.WordTrace]
  refine ⟨61595012713827726767358679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82126683618436969023144905 61595012713827726767358679)
  ·
    refine ⟨92392519070741590151038019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61595012713827726767358679 92392519070741590151038019)
    ·
      refine ⟨138588778606112385226557029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92392519070741590151038019 138588778606112385226557029)
      ·
        refine ⟨25985395988646072229979443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138588778606112385226557029 25985395988646072229979443)
        ·
          refine ⟨38978093982969108344969165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25985395988646072229979443 38978093982969108344969165)
          ·
            refine ⟨14616785243613415629363437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38978093982969108344969165 14616785243613415629363437)
            ·
              refine ⟨5481294466355030861011289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14616785243613415629363437 5481294466355030861011289)
              ·
                refine ⟨4110970849766273145758467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5481294466355030861011289 4110970849766273145758467)
                ·
                  refine ⟨6166456274649409718637701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110970849766273145758467 6166456274649409718637701)
                  ·
                    refine ⟨1156210551496764322244569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166456274649409718637701 1156210551496764322244569)
                    ·
                      rfl

theorem cell22_3377568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_3377568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377568 prefixEnd_3377568 := by exact prefixLift 3377568
  have htrace : WordTrace (prefixWord ++ tailWord_3377568) baseStart_3377568 baseEnd_3377568 := by
    simpa [prefixWord, tailWord_3377568, baseEnd_3377568] using wordTrace_append hprefix tailTrace_3377568
  have hstable : (prefixWord ++ tailWord_3377568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377568).length < 2 ^ (prefixWord ++ tailWord_3377568).sum := by decide
  have hdescent : baseEnd_3377568 < baseStart_3377568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377585 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 1, 4]
def baseStart_3377585 : Nat := 118140960795 + 3377585 * 2 ^ 59
def prefixEnd_3377585 : Nat := 4983230072969 + 3 ^ 40 * 3377585 * 2
def baseEnd_3377585 : Nat := 1156216370944181944569517

theorem tailTrace_3377585 : CollatzResearch.WordTrace tailWord_3377585 prefixEnd_3377585 1156216370944181944569517 := by
  unfold tailWord_3377585
  simp only [CollatzResearch.WordTrace]
  refine ⟨123190645468593865438086209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82127096979062576958724139 123190645468593865438086209)
  ·
    refine ⟨92392984101445399078564657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123190645468593865438086209 92392984101445399078564657)
    ·
      refine ⟨69294738076084049308923493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92392984101445399078564657 69294738076084049308923493)
      ·
        refine ⟨12992763389265759245423155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69294738076084049308923493 12992763389265759245423155)
        ·
          refine ⟨19489145083898638868134733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12992763389265759245423155 19489145083898638868134733)
          ·
            refine ⟨7308429406461989575550525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19489145083898638868134733 7308429406461989575550525)
            ·
              refine ⟨2740661027423246090831447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7308429406461989575550525 2740661027423246090831447)
              ·
                refine ⟨4110991541134869136247171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740661027423246090831447 4110991541134869136247171)
                ·
                  refine ⟨6166487311702303704370757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110991541134869136247171 6166487311702303704370757)
                  ·
                    refine ⟨1156216370944181944569517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166487311702303704370757 1156216370944181944569517)
                    ·
                      rfl

theorem cell22_3377585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_3377585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377585 prefixEnd_3377585 := by exact prefixLift 3377585
  have htrace : WordTrace (prefixWord ++ tailWord_3377585) baseStart_3377585 baseEnd_3377585 := by
    simpa [prefixWord, tailWord_3377585, baseEnd_3377585] using wordTrace_append hprefix tailTrace_3377585
  have hstable : (prefixWord ++ tailWord_3377585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377585).length < 2 ^ (prefixWord ++ tailWord_3377585).sum := by decide
  have hdescent : baseEnd_3377585 < baseStart_3377585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377598 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_3377598 : Nat := 118140960795 + 3377598 * 2 ^ 59
def prefixEnd_3377598 : Nat := 4983230072969 + 3 ^ 40 * 3377598 * 2
def baseEnd_3377598 : Nat := 1156220821109854243994477

theorem tailTrace_3377598 : CollatzResearch.WordTrace tailWord_3377598 prefixEnd_3377598 1156220821109854243994477 := by
  unfold tailWord_3377598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398889952193346082288681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82127413078364512438872965 15398889952193346082288681)
  ·
    refine ⟨11549167464145009561716511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15398889952193346082288681 11549167464145009561716511)
    ·
      refine ⟨17323751196217514342574767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11549167464145009561716511 17323751196217514342574767)
      ·
        refine ⟨25985626794326271513862151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17323751196217514342574767 25985626794326271513862151)
        ·
          refine ⟨38978440191489407270793227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25985626794326271513862151 38978440191489407270793227)
          ·
            refine ⟨58467660287234110906189841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38978440191489407270793227 58467660287234110906189841)
            ·
              refine ⟨43850745215425583179642381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58467660287234110906189841 43850745215425583179642381)
              ·
                refine ⟨16444029455784593692365893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43850745215425583179642381 16444029455784593692365893)
                ·
                  refine ⟨3083255522959611317318605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16444029455784593692365893 3083255522959611317318605)
                  ·
                    refine ⟨1156220821109854243994477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083255522959611317318605 1156220821109854243994477)
                    ·
                      rfl

theorem cell22_3377598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_3377598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377598 prefixEnd_3377598 := by exact prefixLift 3377598
  have htrace : WordTrace (prefixWord ++ tailWord_3377598) baseStart_3377598 baseEnd_3377598 := by
    simpa [prefixWord, tailWord_3377598, baseEnd_3377598] using wordTrace_append hprefix tailTrace_3377598
  have hstable : (prefixWord ++ tailWord_3377598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377598).length < 2 ^ (prefixWord ++ tailWord_3377598).sum := by decide
  have hdescent : baseEnd_3377598 < baseStart_3377598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377634 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3377634 : Nat := 118140960795 + 3377634 * 2 ^ 59
def prefixEnd_3377634 : Nat := 4983230072969 + 3 ^ 40 * 3377634 * 2
def baseEnd_3377634 : Nat := 385411048215187383364789

theorem tailTrace_3377634 : CollatzResearch.WordTrace tailWord_3377634 prefixEnd_3377634 385411048215187383364789 := by
  unfold tailWord_3377634
  simp only [CollatzResearch.WordTrace]
  refine ⟨30798108161354086701654989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82128288430277564537746637 30798108161354086701654989)
  ·
    refine ⟨11549290560507782513120621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30798108161354086701654989 11549290560507782513120621)
    ·
      refine ⟨4330983960190418442420233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11549290560507782513120621 4330983960190418442420233)
      ·
        refine ⟨3248237970142813831815175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4330983960190418442420233 3248237970142813831815175)
        ·
          refine ⟨4872356955214220747722763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248237970142813831815175 4872356955214220747722763)
          ·
            refine ⟨7308535432821331121584145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872356955214220747722763 7308535432821331121584145)
            ·
              refine ⟨5481401574615998341188109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7308535432821331121584145 5481401574615998341188109)
              ·
                refine ⟨2055525590480999377945541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5481401574615998341188109 2055525590480999377945541)
                ·
                  refine ⟨385411048215187383364789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055525590480999377945541 385411048215187383364789)
                  ·
                    rfl

theorem cell22_3377634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3377634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377634 prefixEnd_3377634 := by exact prefixLift 3377634
  have htrace : WordTrace (prefixWord ++ tailWord_3377634) baseStart_3377634 baseEnd_3377634 := by
    simpa [prefixWord, tailWord_3377634, baseEnd_3377634] using wordTrace_append hprefix tailTrace_3377634
  have hstable : (prefixWord ++ tailWord_3377634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377634).length < 2 ^ (prefixWord ++ tailWord_3377634).sum := by decide
  have hdescent : baseEnd_3377634 < baseStart_3377634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377656 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_3377656 : Nat := 118140960795 + 3377656 * 2 ^ 59
def prefixEnd_3377656 : Nat := 4983230072969 + 3 ^ 40 * 3377656 * 2
def baseEnd_3377656 : Nat := 385413558565053808681433

theorem tailTrace_3377656 : CollatzResearch.WordTrace tailWord_3377656 prefixEnd_3377656 385413558565053808681433 := by
  unfold tailWord_3377656
  simp only [CollatzResearch.WordTrace]
  refine ⟨61596617525668322281960411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82128823367557763042613881 61596617525668322281960411)
  ·
    refine ⟨92394926288502483422940617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61596617525668322281960411 92394926288502483422940617)
    ·
      refine ⟨69296194716376862567205463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92394926288502483422940617 69296194716376862567205463)
      ·
        refine ⟨103944292074565293850808195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69296194716376862567205463 103944292074565293850808195)
        ·
          refine ⟨155916438111847940776212293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103944292074565293850808195 155916438111847940776212293)
          ·
            refine ⟨29234332145971488895539805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155916438111847940776212293 29234332145971488895539805)
            ·
              refine ⟨10962874554739308335827427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29234332145971488895539805 10962874554739308335827427)
              ·
                refine ⟨16444311832108962503741141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10962874554739308335827427 16444311832108962503741141)
                ·
                  refine ⟨385413558565053808681433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16444311832108962503741141 385413558565053808681433)
                  ·
                    rfl

theorem cell22_3377656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_3377656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377656 prefixEnd_3377656 := by exact prefixLift 3377656
  have htrace : WordTrace (prefixWord ++ tailWord_3377656) baseStart_3377656 baseEnd_3377656 := by
    simpa [prefixWord, tailWord_3377656, baseEnd_3377656] using wordTrace_append hprefix tailTrace_3377656
  have hstable : (prefixWord ++ tailWord_3377656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377656).length < 2 ^ (prefixWord ++ tailWord_3377656).sum := by decide
  have hdescent : baseEnd_3377656 < baseStart_3377656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377701 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 8]
def baseStart_3377701 : Nat := 118140960795 + 3377701 * 2 ^ 59
def prefixEnd_3377701 : Nat := 4983230072969 + 3 ^ 40 * 3377701 * 2
def baseEnd_3377701 : Nat := 385418693371598769556387

theorem tailTrace_3377701 : CollatzResearch.WordTrace tailWord_3377701 prefixEnd_3377701 385418693371598769556387 := by
  unfold tailWord_3377701
  simp only [CollatzResearch.WordTrace]
  refine ⟨123194876336173617249308957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82129917557449078166205971 123194876336173617249308957)
  ·
    refine ⟨46198078626065106468490859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123194876336173617249308957 46198078626065106468490859)
    ·
      refine ⟨69297117939097659702736289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46198078626065106468490859 69297117939097659702736289)
      ·
        refine ⟨51972838454323244777052217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69297117939097659702736289 51972838454323244777052217)
        ·
          refine ⟨38979628840742433582789163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51972838454323244777052217 38979628840742433582789163)
          ·
            refine ⟨58469443261113650374183745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38979628840742433582789163 58469443261113650374183745)
            ·
              refine ⟨43852082445835237780637809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58469443261113650374183745 43852082445835237780637809)
              ·
                refine ⟨32889061834376428335478357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43852082445835237780637809 32889061834376428335478357)
                ·
                  refine ⟨385418693371598769556387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32889061834376428335478357 385418693371598769556387)
                  ·
                    rfl

theorem cell22_3377701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_3377701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377701 prefixEnd_3377701 := by exact prefixLift 3377701
  have htrace : WordTrace (prefixWord ++ tailWord_3377701) baseStart_3377701 baseEnd_3377701 := by
    simpa [prefixWord, tailWord_3377701, baseEnd_3377701] using wordTrace_append hprefix tailTrace_3377701
  have hstable : (prefixWord ++ tailWord_3377701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377701).length < 2 ^ (prefixWord ++ tailWord_3377701).sum := by decide
  have hdescent : baseEnd_3377701 < baseStart_3377701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377731 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_3377731 : Nat := 118140960795 + 3377731 * 2 ^ 59
def prefixEnd_3377731 : Nat := 4983230072969 + 3 ^ 40 * 3377731 * 2
def baseEnd_3377731 : Nat := 1156266349727886230419069

theorem tailTrace_3377731 : CollatzResearch.WordTrace tailWord_3377731 prefixEnd_3377731 1156266349727886230419069 := by
  unfold tailWord_3377731
  simp only [CollatzResearch.WordTrace]
  refine ⟨123195970526064932372901047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82130647017376621581934031 123195970526064932372901047)
  ·
    refine ⟨184793955789097398559351571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123195970526064932372901047 184793955789097398559351571)
    ·
      refine ⟨277190933683646097839027357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184793955789097398559351571 277190933683646097839027357)
      ·
        refine ⟨103946600131367286689635259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277190933683646097839027357 103946600131367286689635259)
        ·
          refine ⟨155919900197050930034452889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103946600131367286689635259 155919900197050930034452889)
          ·
            refine ⟨116939925147788197525839667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155919900197050930034452889 116939925147788197525839667)
            ·
              refine ⟨175409887721682296288759501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116939925147788197525839667 175409887721682296288759501)
              ·
                refine ⟨65778707895630861108284813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175409887721682296288759501 65778707895630861108284813)
                ·
                  refine ⟨24667015460861572915606805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65778707895630861108284813 24667015460861572915606805)
                  ·
                    refine ⟨1156266349727886230419069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24667015460861572915606805 1156266349727886230419069)
                    ·
                      rfl

theorem cell22_3377731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_3377731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377731 prefixEnd_3377731 := by exact prefixLift 3377731
  have htrace : WordTrace (prefixWord ++ tailWord_3377731) baseStart_3377731 baseEnd_3377731 := by
    simpa [prefixWord, tailWord_3377731, baseEnd_3377731] using wordTrace_append hprefix tailTrace_3377731
  have hstable : (prefixWord ++ tailWord_3377731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377731).length < 2 ^ (prefixWord ++ tailWord_3377731).sum := by decide
  have hdescent : baseEnd_3377731 < baseStart_3377731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377793 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3377793 : Nat := 118140960795 + 3377793 * 2 ^ 59
def prefixEnd_3377793 : Nat := 4983230072969 + 3 ^ 40 * 3377793 * 2
def baseEnd_3377793 : Nat := 1156287573594938735368879

theorem tailTrace_3377793 : CollatzResearch.WordTrace tailWord_3377793 prefixEnd_3377793 1156287573594938735368879 := by
  unfold tailWord_3377793
  simp only [CollatzResearch.WordTrace]
  refine ⟨123198231851840316961658033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82132154567893544641105355 123198231851840316961658033)
  ·
    refine ⟨92398673888880237721243525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123198231851840316961658033 92398673888880237721243525)
    ·
      refine ⟨17324751354165044572733161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92398673888880237721243525 17324751354165044572733161)
      ·
        refine ⟨12993563515623783429549871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17324751354165044572733161 12993563515623783429549871)
        ·
          refine ⟨19490345273435675144324807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12993563515623783429549871 19490345273435675144324807)
          ·
            refine ⟨29235517910153512716487211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19490345273435675144324807 29235517910153512716487211)
            ·
              refine ⟨43853276865230269074730817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29235517910153512716487211 43853276865230269074730817)
              ·
                refine ⟨32889957648922701806048113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43853276865230269074730817 32889957648922701806048113)
                ·
                  refine ⟨24667468236692026354536085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32889957648922701806048113 24667468236692026354536085)
                  ·
                    refine ⟨1156287573594938735368879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24667468236692026354536085 1156287573594938735368879)
                    ·
                      rfl

theorem cell22_3377793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3377793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377793 prefixEnd_3377793 := by exact prefixLift 3377793
  have htrace : WordTrace (prefixWord ++ tailWord_3377793) baseStart_3377793 baseEnd_3377793 := by
    simpa [prefixWord, tailWord_3377793, baseEnd_3377793] using wordTrace_append hprefix tailTrace_3377793
  have hstable : (prefixWord ++ tailWord_3377793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377793).length < 2 ^ (prefixWord ++ tailWord_3377793).sum := by decide
  have hdescent : baseEnd_3377793 < baseStart_3377793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377825 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 7]
def baseStart_3377825 : Nat := 118140960795 + 3377825 * 2 ^ 59
def prefixEnd_3377825 : Nat := 4983230072969 + 3 ^ 40 * 3377825 * 2
def baseEnd_3377825 : Nat := 385432842616300439522927

theorem tailTrace_3377825 : CollatzResearch.WordTrace tailWord_3377825 prefixEnd_3377825 385432842616300439522927 := by
  unfold tailWord_3377825
  simp only [CollatzResearch.WordTrace]
  refine ⟨123199398987724386426822929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82132932658482924284548619 123199398987724386426822929)
  ·
    refine ⟨92399549240793289820117197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123199398987724386426822929 92399549240793289820117197)
    ·
      refine ⟨34649830965297483682543949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92399549240793289820117197 34649830965297483682543949)
      ·
        refine ⟨12993686611986556380953981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34649830965297483682543949 12993686611986556380953981)
        ·
          refine ⟨4872632479494958642857743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12993686611986556380953981 4872632479494958642857743)
          ·
            refine ⟨7308948719242437964286615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872632479494958642857743 7308948719242437964286615)
            ·
              refine ⟨10963423078863656946429923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308948719242437964286615 10963423078863656946429923)
              ·
                refine ⟨16445134618295485419644885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10963423078863656946429923 16445134618295485419644885)
                ·
                  refine ⟨385432842616300439522927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16445134618295485419644885 385432842616300439522927)
                  ·
                    rfl

theorem cell22_3377825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_3377825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377825 prefixEnd_3377825 := by exact prefixLift 3377825
  have htrace : WordTrace (prefixWord ++ tailWord_3377825) baseStart_3377825 baseEnd_3377825 := by
    simpa [prefixWord, tailWord_3377825, baseEnd_3377825] using wordTrace_append hprefix tailTrace_3377825
  have hstable : (prefixWord ++ tailWord_3377825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377825).length < 2 ^ (prefixWord ++ tailWord_3377825).sum := by decide
  have hdescent : baseEnd_3377825 < baseStart_3377825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377855 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 1, 4]
def baseStart_3377855 : Nat := 118140960795 + 3377855 * 2 ^ 59
def prefixEnd_3377855 : Nat := 4983230072969 + 3 ^ 40 * 3377855 * 2
def baseEnd_3377855 : Nat := 1156308797461991240318689

theorem tailTrace_3377855 : CollatzResearch.WordTrace tailWord_3377855 prefixEnd_3377855 1156308797461991240318689 := by
  unfold tailWord_3377855
  simp only [CollatzResearch.WordTrace]
  refine ⟨123200493177615701550415019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82133662118410467700276679 123200493177615701550415019)
  ·
    refine ⟨184800739766423552325622529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123200493177615701550415019 184800739766423552325622529)
    ·
      refine ⟨138600554824817664244216897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184800739766423552325622529 138600554824817664244216897)
      ·
        refine ⟨103950416118613248183162673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138600554824817664244216897 103950416118613248183162673)
        ·
          refine ⟨77962812088959936137372005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103950416118613248183162673 77962812088959936137372005)
          ·
            refine ⟨14618027266679988025757251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77962812088959936137372005 14618027266679988025757251)
            ·
              refine ⟨21927040900019982038635877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14618027266679988025757251 21927040900019982038635877)
              ·
                refine ⟨4111320168753746632244227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21927040900019982038635877 4111320168753746632244227)
                ·
                  refine ⟨6166980253130619948366341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111320168753746632244227 6166980253130619948366341)
                  ·
                    refine ⟨1156308797461991240318689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166980253130619948366341 1156308797461991240318689)
                    ·
                      rfl

theorem cell22_3377855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_3377855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377855 prefixEnd_3377855 := by exact prefixLift 3377855
  have htrace : WordTrace (prefixWord ++ tailWord_3377855) baseStart_3377855 baseEnd_3377855 := by
    simpa [prefixWord, tailWord_3377855, baseEnd_3377855] using wordTrace_append hprefix tailTrace_3377855
  have hstable : (prefixWord ++ tailWord_3377855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377855).length < 2 ^ (prefixWord ++ tailWord_3377855).sum := by decide
  have hdescent : baseEnd_3377855 < baseStart_3377855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377913 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_3377913 : Nat := 118140960795 + 3377913 * 2 ^ 59
def prefixEnd_3377913 : Nat := 4983230072969 + 3 ^ 40 * 3377913 * 2
def baseEnd_3377913 : Nat := 1156328652047298422368511

theorem tailTrace_3377913 : CollatzResearch.WordTrace tailWord_3377913 prefixEnd_3377913 1156328652047298422368511 := by
  unfold tailWord_3377913
  simp only [CollatzResearch.WordTrace]
  refine ⟨123202608611405577456026393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82135072407603718304017595 123202608611405577456026393)
  ·
    refine ⟨92401956458554183092019795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123202608611405577456026393 92401956458554183092019795)
    ·
      refine ⟨138602934687831274638029693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92401956458554183092019795 138602934687831274638029693)
      ·
        refine ⟨51976100507936727989261135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138602934687831274638029693 51976100507936727989261135)
        ·
          refine ⟨77964150761905091983891703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51976100507936727989261135 77964150761905091983891703)
          ·
            refine ⟨116946226142857637975837555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77964150761905091983891703 116946226142857637975837555)
            ·
              refine ⟨175419339214286456963756333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116946226142857637975837555 175419339214286456963756333)
              ·
                refine ⟨65782252205357421361408625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175419339214286456963756333 65782252205357421361408625)
                ·
                  refine ⟨49336689154018066021056469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65782252205357421361408625 49336689154018066021056469)
                  ·
                    refine ⟨1156328652047298422368511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49336689154018066021056469 1156328652047298422368511)
                    ·
                      rfl

theorem cell22_3377913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_3377913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377913 prefixEnd_3377913 := by exact prefixLift 3377913
  have htrace : WordTrace (prefixWord ++ tailWord_3377913) baseStart_3377913 baseEnd_3377913 := by
    simpa [prefixWord, tailWord_3377913, baseEnd_3377913] using wordTrace_append hprefix tailTrace_3377913
  have hstable : (prefixWord ++ tailWord_3377913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377913).length < 2 ^ (prefixWord ++ tailWord_3377913).sum := by decide
  have hdescent : baseEnd_3377913 < baseStart_3377913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377938 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_3377938 : Nat := 118140960795 + 3377938 * 2 ^ 59
def prefixEnd_3377938 : Nat := 4983230072969 + 3 ^ 40 * 3377938 * 2
def baseEnd_3377938 : Nat := 385445736686068896831145

theorem tailTrace_3377938 : CollatzResearch.WordTrace tailWord_3377938 prefixEnd_3377938 385445736686068896831145 := by
  unfold tailWord_3377938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30800880109078751681421617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82135680290876671150457645 30800880109078751681421617)
  ·
    refine ⟨23100660081809063761066213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30800880109078751681421617 23100660081809063761066213)
    ·
      refine ⟨4331373765339199455199915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23100660081809063761066213 4331373765339199455199915)
      ·
        refine ⟨6497060648008799182799873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331373765339199455199915 6497060648008799182799873)
        ·
          refine ⟨4872795486006599387099905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497060648008799182799873 4872795486006599387099905)
          ·
            refine ⟨3654596614504949540324929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4872795486006599387099905 3654596614504949540324929)
            ·
              refine ⟨2740947460878712155243697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3654596614504949540324929 2740947460878712155243697)
              ·
                refine ⟨2055710595659034116432773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740947460878712155243697 2055710595659034116432773)
                ·
                  refine ⟨385445736686068896831145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055710595659034116432773 385445736686068896831145)
                  ·
                    rfl

theorem cell22_3377938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_3377938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377938 prefixEnd_3377938 := by exact prefixLift 3377938
  have htrace : WordTrace (prefixWord ++ tailWord_3377938) baseStart_3377938 baseEnd_3377938 := by
    simpa [prefixWord, tailWord_3377938, baseEnd_3377938] using wordTrace_append hprefix tailTrace_3377938
  have hstable : (prefixWord ++ tailWord_3377938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377938).length < 2 ^ (prefixWord ++ tailWord_3377938).sum := by decide
  have hdescent : baseEnd_3377938 < baseStart_3377938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377949 : List Nat := [1, 4, 2, 4, 1, 2, 1, 7]
def baseStart_3377949 : Nat := 118140960795 + 3377949 * 2 ^ 59
def prefixEnd_3377949 : Nat := 4983230072969 + 3 ^ 40 * 3377949 * 2
def baseEnd_3377949 : Nat := 128482330620334036496489

theorem tailTrace_3377949 : CollatzResearch.WordTrace tailWord_3377949 prefixEnd_3377949 128482330620334036496489 := by
  unfold tailWord_3377949
  simp only [CollatzResearch.WordTrace]
  refine ⟨123203921639275155604336901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82135947759516770402891267 123203921639275155604336901)
  ·
    refine ⟨23100735307364091675813169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123203921639275155604336901 23100735307364091675813169)
    ·
      refine ⟨17325551480523068756859877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23100735307364091675813169 17325551480523068756859877)
      ·
        refine ⟨3248540902598075391911227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17325551480523068756859877 3248540902598075391911227)
        ·
          refine ⟨4872811353897113087866841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248540902598075391911227 4872811353897113087866841)
          ·
            refine ⟨3654608515422834815900131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4872811353897113087866841 3654608515422834815900131)
            ·
              refine ⟨5481912773134252223850197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654608515422834815900131 5481912773134252223850197)
              ·
                refine ⟨128482330620334036496489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5481912773134252223850197 128482330620334036496489)
                ·
                  rfl

theorem cell22_3377949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 7].length) (baseStart_3377949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3377949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3377949 prefixEnd_3377949 := by exact prefixLift 3377949
  have htrace : WordTrace (prefixWord ++ tailWord_3377949) baseStart_3377949 baseEnd_3377949 := by
    simpa [prefixWord, tailWord_3377949, baseEnd_3377949] using wordTrace_append hprefix tailTrace_3377949
  have hstable : (prefixWord ++ tailWord_3377949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377949).length < 2 ^ (prefixWord ++ tailWord_3377949).sum := by decide
  have hdescent : baseEnd_3377949 < baseStart_3377949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378024 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3378024 : Nat := 118140960795 + 3378024 * 2 ^ 59
def prefixEnd_3378024 : Nat := 4983230072969 + 3 ^ 40 * 3378024 * 2
def baseEnd_3378024 : Nat := 1156366649615731132843171

theorem tailTrace_3378024 : CollatzResearch.WordTrace tailWord_3378024 prefixEnd_3378024 1156366649615731132843171 := by
  unfold tailWord_3378024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61603328557001721706658563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82137771409335628942211417 61603328557001721706658563)
  ·
    refine ⟨92404992835502582559987845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61603328557001721706658563 92404992835502582559987845)
    ·
      refine ⟨17325936156656734229997721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92404992835502582559987845 17325936156656734229997721)
      ·
        refine ⟨12994452117492550672498291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17325936156656734229997721 12994452117492550672498291)
        ·
          refine ⟨19491678176238826008747437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12994452117492550672498291 19491678176238826008747437)
          ·
            refine ⟨7309379316089559753280289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19491678176238826008747437 7309379316089559753280289)
            ·
              refine ⟨5482034487067169814960217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7309379316089559753280289 5482034487067169814960217)
              ·
                refine ⟨4111525865300377361220163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5482034487067169814960217 4111525865300377361220163)
                ·
                  refine ⟨6167288797950566041830245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111525865300377361220163 6167288797950566041830245)
                  ·
                    refine ⟨1156366649615731132843171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167288797950566041830245 1156366649615731132843171)
                    ·
                      rfl

theorem cell22_3378024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3378024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378024 prefixEnd_3378024 := by exact prefixLift 3378024
  have htrace : WordTrace (prefixWord ++ tailWord_3378024) baseStart_3378024 baseEnd_3378024 := by
    simpa [prefixWord, tailWord_3378024, baseEnd_3378024] using wordTrace_append hprefix tailTrace_3378024
  have hstable : (prefixWord ++ tailWord_3378024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378024).length < 2 ^ (prefixWord ++ tailWord_3378024).sum := by decide
  have hdescent : baseEnd_3378024 < baseStart_3378024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378035 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 1, 6]
def baseStart_3378035 : Nat := 118140960795 + 3378035 * 2 ^ 59
def prefixEnd_3378035 : Nat := 4983230072969 + 3 ^ 40 * 3378035 * 2
def baseEnd_3378035 : Nat := 1156370415140530770818137

theorem tailTrace_3378035 : CollatzResearch.WordTrace tailWord_3378035 prefixEnd_3378035 1156370415140530770818137 := by
  unfold tailWord_3378035
  simp only [CollatzResearch.WordTrace]
  refine ⟨123207058316963592291967559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82138038877975728194645039 123207058316963592291967559)
  ·
    refine ⟨184810587475445388437951339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123207058316963592291967559 184810587475445388437951339)
    ·
      refine ⟨277215881213168082656927009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184810587475445388437951339 277215881213168082656927009)
      ·
        refine ⟨207911910909876061992695257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277215881213168082656927009 207911910909876061992695257)
        ·
          refine ⟨155933933182407046494521443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207911910909876061992695257 155933933182407046494521443)
          ·
            refine ⟨233900899773610569741782165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155933933182407046494521443 233900899773610569741782165)
            ·
              refine ⟨10964104676887995456646039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233900899773610569741782165 10964104676887995456646039)
              ·
                refine ⟨16446157015331993184969059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10964104676887995456646039 16446157015331993184969059)
                ·
                  refine ⟨24669235522997989777453589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16446157015331993184969059 24669235522997989777453589)
                  ·
                    refine ⟨1156370415140530770818137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24669235522997989777453589 1156370415140530770818137)
                    ·
                      rfl

theorem cell22_3378035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_3378035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378035 prefixEnd_3378035 := by exact prefixLift 3378035
  have htrace : WordTrace (prefixWord ++ tailWord_3378035) baseStart_3378035 baseEnd_3378035 := by
    simpa [prefixWord, tailWord_3378035, baseEnd_3378035] using wordTrace_append hprefix tailTrace_3378035
  have hstable : (prefixWord ++ tailWord_3378035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378035).length < 2 ^ (prefixWord ++ tailWord_3378035).sum := by decide
  have hdescent : baseEnd_3378035 < baseStart_3378035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378056 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 4]
def baseStart_3378056 : Nat := 118140960795 + 3378056 * 2 ^ 59
def prefixEnd_3378056 : Nat := 4983230072969 + 3 ^ 40 * 3378056 * 2
def baseEnd_3378056 : Nat := 385459201289897905347691

theorem tailTrace_3378056 : CollatzResearch.WordTrace tailWord_3378056 prefixEnd_3378056 385459201289897905347691 := by
  unfold tailWord_3378056
  simp only [CollatzResearch.WordTrace]
  refine ⟨61603912124943756439241011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82138549499925008585654681 61603912124943756439241011)
  ·
    refine ⟨92405868187415634658861517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61603912124943756439241011 92405868187415634658861517)
    ·
      refine ⟨34652200570280862997073069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92405868187415634658861517 34652200570280862997073069)
      ·
        refine ⟨12994575213855323623902401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34652200570280862997073069 12994575213855323623902401)
        ·
          refine ⟨9745931410391492717926801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12994575213855323623902401 9745931410391492717926801)
          ·
            refine ⟨7309448557793619538445101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9745931410391492717926801 7309448557793619538445101)
            ·
              refine ⟨2741043209172607326916913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7309448557793619538445101 2741043209172607326916913)
              ·
                refine ⟨2055782406879455495187685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741043209172607326916913 2055782406879455495187685)
                ·
                  refine ⟨385459201289897905347691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055782406879455495187685 385459201289897905347691)
                  ·
                    rfl

theorem cell22_3378056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_3378056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378056 prefixEnd_3378056 := by exact prefixLift 3378056
  have htrace : WordTrace (prefixWord ++ tailWord_3378056) baseStart_3378056 baseEnd_3378056 := by
    simpa [prefixWord, tailWord_3378056, baseEnd_3378056] using wordTrace_append hprefix tailTrace_3378056
  have hstable : (prefixWord ++ tailWord_3378056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378056).length < 2 ^ (prefixWord ++ tailWord_3378056).sum := by decide
  have hdescent : baseEnd_3378056 < baseStart_3378056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378095 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 7]
def baseStart_3378095 : Nat := 118140960795 + 3378095 * 2 ^ 59
def prefixEnd_3378095 : Nat := 4983230072969 + 3 ^ 40 * 3378095 * 2
def baseEnd_3378095 : Nat := 385463651455570204772651

theorem tailTrace_3378095 : CollatzResearch.WordTrace tailWord_3378095 prefixEnd_3378095 385463651455570204772651 := by
  unfold tailWord_3378095
  simp only [CollatzResearch.WordTrace]
  refine ⟨123209246696746222539151739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82139497797830815026101159 123209246696746222539151739)
  ·
    refine ⟨184813870045119333808727609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123209246696746222539151739 184813870045119333808727609)
    ·
      refine ⟨138610402533839500356545707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184813870045119333808727609 138610402533839500356545707)
      ·
        refine ⟨207915603800759250534818561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138610402533839500356545707 207915603800759250534818561)
        ·
          refine ⟨155936702850569437901113921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207915603800759250534818561 155936702850569437901113921)
          ·
            refine ⟨116952527137927078425835441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155936702850569437901113921 116952527137927078425835441)
            ·
              refine ⟨87714395353445308819376581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116952527137927078425835441 87714395353445308819376581)
              ·
                refine ⟨16446449128770995403633109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87714395353445308819376581 16446449128770995403633109)
                ·
                  refine ⟨385463651455570204772651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16446449128770995403633109 385463651455570204772651)
                  ·
                    rfl

theorem cell22_3378095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_3378095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378095 prefixEnd_3378095 := by exact prefixLift 3378095
  have htrace : WordTrace (prefixWord ++ tailWord_3378095) baseStart_3378095 baseEnd_3378095 := by
    simpa [prefixWord, tailWord_3378095, baseEnd_3378095] using wordTrace_append hprefix tailTrace_3378095
  have hstable : (prefixWord ++ tailWord_3378095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378095).length < 2 ^ (prefixWord ++ tailWord_3378095).sum := by decide
  have hdescent : baseEnd_3378095 < baseStart_3378095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378112 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_3378112 : Nat := 118140960795 + 3378112 * 2 ^ 59
def prefixEnd_3378112 : Nat := 4983230072969 + 3 ^ 40 * 3378112 * 2
def baseEnd_3378112 : Nat := 385465591271376078880967

theorem tailTrace_3378112 : CollatzResearch.WordTrace tailWord_3378112 prefixEnd_3378112 385465591271376078880967 := by
  unfold tailWord_3378112
  simp only [CollatzResearch.WordTrace]
  refine ⟨61604933368842317221260295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82139911158456422961680393 61604933368842317221260295)
  ·
    refine ⟨92407400053263475831890443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61604933368842317221260295 92407400053263475831890443)
    ·
      refine ⟨138611100079895213747835665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92407400053263475831890443 138611100079895213747835665)
      ·
        refine ⟨103958325059921410310876749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138611100079895213747835665 103958325059921410310876749)
        ·
          refine ⟨38984371897470528866578781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103958325059921410310876749 38984371897470528866578781)
          ·
            refine ⟨14619139461551448324967043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38984371897470528866578781 14619139461551448324967043)
            ·
              refine ⟨21928709192327172487450565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619139461551448324967043 21928709192327172487450565)
              ·
                refine ⟨4111632973561344841396981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21928709192327172487450565 4111632973561344841396981)
                ·
                  refine ⟨385465591271376078880967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4111632973561344841396981 385465591271376078880967)
                  ·
                    rfl

theorem cell22_3378112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_3378112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378112 prefixEnd_3378112 := by exact prefixLift 3378112
  have htrace : WordTrace (prefixWord ++ tailWord_3378112) baseStart_3378112 baseEnd_3378112 := by
    simpa [prefixWord, tailWord_3378112, baseEnd_3378112] using wordTrace_append hprefix tailTrace_3378112
  have hstable : (prefixWord ++ tailWord_3378112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378112).length < 2 ^ (prefixWord ++ tailWord_3378112).sum := by decide
  have hdescent : baseEnd_3378112 < baseStart_3378112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378127 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 2, 5]
def baseStart_3378127 : Nat := 118140960795 + 3378127 * 2 ^ 59
def prefixEnd_3378127 : Nat := 4983230072969 + 3 ^ 40 * 3378127 * 2
def baseEnd_3378127 : Nat := 1156401908620673197517855

theorem tailTrace_3378127 : CollatzResearch.WordTrace tailWord_3378127 prefixEnd_3378127 1156401908620673197517855 := by
  unfold tailWord_3378127
  simp only [CollatzResearch.WordTrace]
  refine ⟨123210413832630292004316635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82140275888420194669544423 123210413832630292004316635)
  ·
    refine ⟨184815620748945438006474953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123210413832630292004316635 184815620748945438006474953)
    ·
      refine ⟨138611715561709078504856215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184815620748945438006474953 138611715561709078504856215)
      ·
        refine ⟨207917573342563617757284323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138611715561709078504856215 207917573342563617757284323)
        ·
          refine ⟨311876360013845426635926485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207917573342563617757284323 311876360013845426635926485)
          ·
            refine ⟨7309602187824502186779527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 311876360013845426635926485 7309602187824502186779527)
            ·
              refine ⟨10964403281736753280169291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309602187824502186779527 10964403281736753280169291)
              ·
                refine ⟨16446604922605129920253937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10964403281736753280169291 16446604922605129920253937)
                ·
                  refine ⟨12334953691953847440190453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16446604922605129920253937 12334953691953847440190453)
                  ·
                    refine ⟨1156401908620673197517855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12334953691953847440190453 1156401908620673197517855)
                    ·
                      rfl

theorem cell22_3378127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_3378127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378127 prefixEnd_3378127 := by exact prefixLift 3378127
  have htrace : WordTrace (prefixWord ++ tailWord_3378127) baseStart_3378127 baseEnd_3378127 := by
    simpa [prefixWord, tailWord_3378127, baseEnd_3378127] using wordTrace_append hprefix tailTrace_3378127
  have hstable : (prefixWord ++ tailWord_3378127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378127).length < 2 ^ (prefixWord ++ tailWord_3378127).sum := by decide
  have hdescent : baseEnd_3378127 < baseStart_3378127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378159 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 1, 4]
def baseStart_3378159 : Nat := 118140960795 + 3378159 * 2 ^ 59
def prefixEnd_3378159 : Nat := 4983230072969 + 3 ^ 40 * 3378159 * 2
def baseEnd_3378159 : Nat := 1156412862874635780717757

theorem tailTrace_3378159 : CollatzResearch.WordTrace tailWord_3378159 prefixEnd_3378159 1156412862874635780717757 := by
  unfold tailWord_3378159
  simp only [CollatzResearch.WordTrace]
  refine ⟨123211580968514361469481531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82141053979009574312987687 123211580968514361469481531)
  ·
    refine ⟨184817371452771542204222297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123211580968514361469481531 184817371452771542204222297)
    ·
      refine ⟨138613028589578656653166723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184817371452771542204222297 138613028589578656653166723)
      ·
        refine ⟨207919542884367984979750085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138613028589578656653166723 207919542884367984979750085)
        ·
          refine ⟨38984914290818997183703141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207919542884367984979750085 38984914290818997183703141)
          ·
            refine ⟨7309671429528561971944339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38984914290818997183703141 7309671429528561971944339)
            ·
              refine ⟨10964507144292842957916509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309671429528561971944339 10964507144292842957916509)
              ·
                refine ⟨4111690179109816109218691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10964507144292842957916509 4111690179109816109218691)
                ·
                  refine ⟨6167535268664724163828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111690179109816109218691 6167535268664724163828037)
                  ·
                    refine ⟨1156412862874635780717757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167535268664724163828037 1156412862874635780717757)
                    ·
                      rfl

theorem cell22_3378159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_3378159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378159 prefixEnd_3378159 := by exact prefixLift 3378159
  have htrace : WordTrace (prefixWord ++ tailWord_3378159) baseStart_3378159 baseEnd_3378159 := by
    simpa [prefixWord, tailWord_3378159, baseEnd_3378159] using wordTrace_append hprefix tailTrace_3378159
  have hstable : (prefixWord ++ tailWord_3378159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378159).length < 2 ^ (prefixWord ++ tailWord_3378159).sum := by decide
  have hdescent : baseEnd_3378159 < baseStart_3378159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378187 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_3378187 : Nat := 118140960795 + 3378187 * 2 ^ 59
def prefixEnd_3378187 : Nat := 4983230072969 + 3 ^ 40 * 3378187 * 2
def baseEnd_3378187 : Nat := 1156422447846853041017671

theorem tailTrace_3378187 : CollatzResearch.WordTrace tailWord_3378187 prefixEnd_3378187 1156422447846853041017671 := by
  unfold tailWord_3378187
  simp only [CollatzResearch.WordTrace]
  refine ⟨123212602212412922251500815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82141734808275281501000543 123212602212412922251500815)
  ·
    refine ⟨184818903318619383377251223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123212602212412922251500815 184818903318619383377251223)
    ·
      refine ⟨277228354977929075065876835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184818903318619383377251223 277228354977929075065876835)
      ·
        refine ⟨415842532466893612598815253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277228354977929075065876835 415842532466893612598815253)
        ·
          refine ⟨19492618709385638090569465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 415842532466893612598815253 19492618709385638090569465)
          ·
            refine ⟨14619464032039228567927099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19492618709385638090569465 14619464032039228567927099)
            ·
              refine ⟨21929196048058842851890649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619464032039228567927099 21929196048058842851890649)
              ·
                refine ⟨16446897036044132138917987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21929196048058842851890649 16446897036044132138917987)
                ·
                  refine ⟨24670345554066198208376981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16446897036044132138917987 24670345554066198208376981)
                  ·
                    refine ⟨1156422447846853041017671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24670345554066198208376981 1156422447846853041017671)
                    ·
                      rfl

theorem cell22_3378187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_3378187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378187 prefixEnd_3378187 := by exact prefixLift 3378187
  have htrace : WordTrace (prefixWord ++ tailWord_3378187) baseStart_3378187 baseEnd_3378187 := by
    simpa [prefixWord, tailWord_3378187, baseEnd_3378187] using wordTrace_append hprefix tailTrace_3378187
  have hstable : (prefixWord ++ tailWord_3378187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378187).length < 2 ^ (prefixWord ++ tailWord_3378187).sum := by decide
  have hdescent : baseEnd_3378187 < baseStart_3378187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378202 : List Nat := [3, 1, 1, 3, 1, 2, 3, 8]
def baseStart_3378202 : Nat := 118140960795 + 3378202 * 2 ^ 59
def prefixEnd_3378202 : Nat := 4983230072969 + 3 ^ 40 * 3378202 * 2
def baseEnd_3378202 : Nat := 128491953628155333543625

theorem tailTrace_3378202 : CollatzResearch.WordTrace tailWord_3378202 prefixEnd_3378202 128491953628155333543625 := by
  unfold tailWord_3378202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30803287326839644953324215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82142099538239053208864573 30803287326839644953324215)
  ·
    refine ⟨46204930990259467429986323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30803287326839644953324215 46204930990259467429986323)
    ·
      refine ⟨69307396485389201144979485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46204930990259467429986323 69307396485389201144979485)
      ·
        refine ⟨25990273682020950429367307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69307396485389201144979485 25990273682020950429367307)
        ·
          refine ⟨38985410523031425644050961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25990273682020950429367307 38985410523031425644050961)
          ·
            refine ⟨29239057892273569233038221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38985410523031425644050961 29239057892273569233038221)
            ·
              refine ⟨10964646709602588462389333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29239057892273569233038221 10964646709602588462389333)
              ·
                refine ⟨128491953628155333543625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10964646709602588462389333 128491953628155333543625)
                ·
                  rfl

theorem cell22_3378202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_3378202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378202 prefixEnd_3378202 := by exact prefixLift 3378202
  have htrace : WordTrace (prefixWord ++ tailWord_3378202) baseStart_3378202 baseEnd_3378202 := by
    simpa [prefixWord, tailWord_3378202, baseEnd_3378202] using wordTrace_append hprefix tailTrace_3378202
  have hstable : (prefixWord ++ tailWord_3378202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378202).length < 2 ^ (prefixWord ++ tailWord_3378202).sum := by decide
  have hdescent : baseEnd_3378202 < baseStart_3378202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378268 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3378268 : Nat := 118140960795 + 3378268 * 2 ^ 59
def prefixEnd_3378268 : Nat := 4983230072969 + 3 ^ 40 * 3378268 * 2
def baseEnd_3378268 : Nat := 1156450175802195829742423

theorem tailTrace_3378268 : CollatzResearch.WordTrace tailWord_3378268 prefixEnd_3378268 1156450175802195829742423 := by
  unfold tailWord_3378268
  simp only [CollatzResearch.WordTrace]
  refine ⟨61607778262559736542599729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82143704350079648723466305 61607778262559736542599729)
  ·
    refine ⟨46205833696919802406949797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61607778262559736542599729 46205833696919802406949797)
    ·
      refine ⟨8663593818172462951303087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46205833696919802406949797 8663593818172462951303087)
      ·
        refine ⟨12995390727258694426954631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8663593818172462951303087 12995390727258694426954631)
        ·
          refine ⟨19493086090888041640431947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12995390727258694426954631 19493086090888041640431947)
          ·
            refine ⟨29239629136332062460647921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19493086090888041640431947 29239629136332062460647921)
            ·
              refine ⟨21929721852249046845485941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29239629136332062460647921 21929721852249046845485941)
              ·
                refine ⟨2055911423648348141764307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21929721852249046845485941 2055911423648348141764307)
                ·
                  refine ⟨3083867135472522212646461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055911423648348141764307 3083867135472522212646461)
                  ·
                    refine ⟨1156450175802195829742423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083867135472522212646461 1156450175802195829742423)
                    ·
                      rfl

theorem cell22_3378268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3378268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378268 prefixEnd_3378268 := by exact prefixLift 3378268
  have htrace : WordTrace (prefixWord ++ tailWord_3378268) baseStart_3378268 baseEnd_3378268 := by
    simpa [prefixWord, tailWord_3378268, baseEnd_3378268] using wordTrace_append hprefix tailTrace_3378268
  have hstable : (prefixWord ++ tailWord_3378268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378268).length < 2 ^ (prefixWord ++ tailWord_3378268).sum := by decide
  have hdescent : baseEnd_3378268 < baseStart_3378268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378285 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_3378285 : Nat := 118140960795 + 3378285 * 2 ^ 59
def prefixEnd_3378285 : Nat := 4983230072969 + 3 ^ 40 * 3378285 * 2
def baseEnd_3378285 : Nat := 1156455995249613452067371

theorem tailTrace_3378285 : CollatzResearch.WordTrace tailWord_3378285 prefixEnd_3378285 1156455995249613452067371 := by
  unfold tailWord_3378285
  simp only [CollatzResearch.WordTrace]
  refine ⟨123216176566057884988568309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82144117710705256659045539 123216176566057884988568309)
  ·
    refine ⟨11551516553067926717678279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123216176566057884988568309 11551516553067926717678279)
    ·
      refine ⟨17327274829601890076517419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11551516553067926717678279 17327274829601890076517419)
      ·
        refine ⟨25990912244402835114776129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17327274829601890076517419 25990912244402835114776129)
        ·
          refine ⟨19493184183302126336082097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25990912244402835114776129 19493184183302126336082097)
          ·
            refine ⟨14619888137476594752061573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19493184183302126336082097 14619888137476594752061573)
            ·
              refine ⟨2741229025776861516011545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14619888137476594752061573 2741229025776861516011545)
              ·
                refine ⟨2055921769332646137008659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741229025776861516011545 2055921769332646137008659)
                ·
                  refine ⟨3083882653998969205512989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055921769332646137008659 3083882653998969205512989)
                  ·
                    refine ⟨1156455995249613452067371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083882653998969205512989 1156455995249613452067371)
                    ·
                      rfl

theorem cell22_3378285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_3378285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378285 prefixEnd_3378285 := by exact prefixLift 3378285
  have htrace : WordTrace (prefixWord ++ tailWord_3378285) baseStart_3378285 baseEnd_3378285 := by
    simpa [prefixWord, tailWord_3378285, baseEnd_3378285] using wordTrace_append hprefix tailTrace_3378285
  have hstable : (prefixWord ++ tailWord_3378285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378285).length < 2 ^ (prefixWord ++ tailWord_3378285).sum := by decide
  have hdescent : baseEnd_3378285 < baseStart_3378285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378302 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3378302 : Nat := 118140960795 + 3378302 * 2 ^ 59
def prefixEnd_3378302 : Nat := 4983230072969 + 3 ^ 40 * 3378302 * 2
def baseEnd_3378302 : Nat := 1156461814697031074392319

theorem tailTrace_3378302 : CollatzResearch.WordTrace tailWord_3378302 prefixEnd_3378302 1156461814697031074392319 := by
  unfold tailWord_3378302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15402099575874537111492145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82144531071330864594624773 15402099575874537111492145)
  ·
    refine ⟨11551574681905902833619109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15402099575874537111492145 11551574681905902833619109)
    ·
      refine ⟨2165920252857356781303583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11551574681905902833619109 2165920252857356781303583)
      ·
        refine ⟨3248880379286035171955375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165920252857356781303583 3248880379286035171955375)
        ·
          refine ⟨4873320568929052757933063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248880379286035171955375 4873320568929052757933063)
          ·
            refine ⟨7309980853393579136899595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873320568929052757933063 7309980853393579136899595)
            ·
              refine ⟨10964971280090368705349393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309980853393579136899595 10964971280090368705349393)
              ·
                refine ⟨8223728460067776529012045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10964971280090368705349393 8223728460067776529012045)
                ·
                  refine ⟨3083898172525416198379517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8223728460067776529012045 3083898172525416198379517)
                  ·
                    refine ⟨1156461814697031074392319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083898172525416198379517 1156461814697031074392319)
                    ·
                      rfl

theorem cell22_3378302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3378302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378302 prefixEnd_3378302 := by exact prefixLift 3378302
  have htrace : WordTrace (prefixWord ++ tailWord_3378302) baseStart_3378302 baseEnd_3378302 := by
    simpa [prefixWord, tailWord_3378302, baseEnd_3378302] using wordTrace_append hprefix tailTrace_3378302
  have hstable : (prefixWord ++ tailWord_3378302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378302).length < 2 ^ (prefixWord ++ tailWord_3378302).sum := by decide
  have hdescent : baseEnd_3378302 < baseStart_3378302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378328 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 1, 4]
def baseStart_3378328 : Nat := 118140960795 + 3378328 * 2 ^ 59
def prefixEnd_3378328 : Nat := 4983230072969 + 3 ^ 40 * 3378328 * 2
def baseEnd_3378328 : Nat := 1156470715028375673242239

theorem tailTrace_3378328 : CollatzResearch.WordTrace tailWord_3378328 prefixEnd_3378328 1156470715028375673242239 := by
  unfold tailWord_3378328
  simp only [CollatzResearch.WordTrace]
  refine ⟨61608872452451051666191819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82145163269934735554922425 61608872452451051666191819)
  ·
    refine ⟨92413308678676577499287729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61608872452451051666191819 92413308678676577499287729)
    ·
      refine ⟨69309981509007433124465797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92413308678676577499287729 69309981509007433124465797)
      ·
        refine ⟨12995621532938893710837337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69309981509007433124465797 12995621532938893710837337)
        ·
          refine ⟨9746716149704170283128003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12995621532938893710837337 9746716149704170283128003)
          ·
            refine ⟨14620074224556255424692005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746716149704170283128003 14620074224556255424692005)
            ·
              refine ⟨2741263917104297892129751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14620074224556255424692005 2741263917104297892129751)
              ·
                refine ⟨4111895875656446838194627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741263917104297892129751 4111895875656446838194627)
                ·
                  refine ⟨6167843813484670257291941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111895875656446838194627 6167843813484670257291941)
                  ·
                    refine ⟨1156470715028375673242239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167843813484670257291941 1156470715028375673242239)
                    ·
                      rfl

theorem cell22_3378328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_3378328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378328 prefixEnd_3378328 := by exact prefixLift 3378328
  have htrace : WordTrace (prefixWord ++ tailWord_3378328) baseStart_3378328 baseEnd_3378328 := by
    simpa [prefixWord, tailWord_3378328, baseEnd_3378328] using wordTrace_append hprefix tailTrace_3378328
  have hstable : (prefixWord ++ tailWord_3378328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378328).length < 2 ^ (prefixWord ++ tailWord_3378328).sum := by decide
  have hdescent : baseEnd_3378328 < baseStart_3378328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378339 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 2, 4]
def baseStart_3378339 : Nat := 118140960795 + 3378339 * 2 ^ 59
def prefixEnd_3378339 : Nat := 4983230072969 + 3 ^ 40 * 3378339 * 2
def baseEnd_3378339 : Nat := 1156474480553175311217205

theorem tailTrace_3378339 : CollatzResearch.WordTrace tailWord_3378339 prefixEnd_3378339 1156474480553175311217205 := by
  unfold tailWord_3378339
  simp only [CollatzResearch.WordTrace]
  refine ⟨123218146107862252211034071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82145430738574834807356047 123218146107862252211034071)
  ·
    refine ⟨184827219161793378316551107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123218146107862252211034071 184827219161793378316551107)
    ·
      refine ⟨277240828742690067474826661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184827219161793378316551107 277240828742690067474826661)
      ·
        refine ⟨51982655389254387651529999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277240828742690067474826661 51982655389254387651529999)
        ·
          refine ⟨77973983083881581477294999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51982655389254387651529999 77973983083881581477294999)
          ·
            refine ⟨116960974625822372215942499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77973983083881581477294999 116960974625822372215942499)
            ·
              refine ⟨175441461938733558323913749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116960974625822372215942499 175441461938733558323913749)
              ·
                refine ⟨8223818528378135546433457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175441461938733558323913749 8223818528378135546433457)
                ·
                  refine ⟨6167863896283601659825093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8223818528378135546433457 6167863896283601659825093)
                  ·
                    refine ⟨1156474480553175311217205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167863896283601659825093 1156474480553175311217205)
                    ·
                      rfl

theorem cell22_3378339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_3378339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378339 prefixEnd_3378339 := by exact prefixLift 3378339
  have htrace : WordTrace (prefixWord ++ tailWord_3378339) baseStart_3378339 baseEnd_3378339 := by
    simpa [prefixWord, tailWord_3378339, baseEnd_3378339] using wordTrace_append hprefix tailTrace_3378339
  have hstable : (prefixWord ++ tailWord_3378339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378339).length < 2 ^ (prefixWord ++ tailWord_3378339).sum := by decide
  have hdescent : baseEnd_3378339 < baseStart_3378339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378341 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_3378341 : Nat := 118140960795 + 3378341 * 2 ^ 59
def prefixEnd_3378341 : Nat := 4983230072969 + 3 ^ 40 * 3378341 * 2
def baseEnd_3378341 : Nat := 1156475165194047972667199

theorem tailTrace_3378341 : CollatzResearch.WordTrace tailWord_3378341 prefixEnd_3378341 1156475165194047972667199 := by
  unfold tailWord_3378341
  simp only [CollatzResearch.WordTrace]
  refine ⟨123218219053855006552606877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82145479369236671035071251 123218219053855006552606877)
  ·
    refine ⟨46206832145195627457227579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123218219053855006552606877 46206832145195627457227579)
    ·
      refine ⟨69310248217793441185841369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46206832145195627457227579 69310248217793441185841369)
      ·
        refine ⟨51982686163345080889381027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69310248217793441185841369 51982686163345080889381027)
        ·
          refine ⟨77974029245017621334071541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51982686163345080889381027 77974029245017621334071541)
          ·
            refine ⟨7310065241720402000069207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77974029245017621334071541 7310065241720402000069207)
            ·
              refine ⟨10965097862580603000103811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310065241720402000069207 10965097862580603000103811)
              ·
                refine ⟨16447646793870904500155717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10965097862580603000103811 16447646793870904500155717)
                ·
                  refine ⟨3083933773850794593779197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16447646793870904500155717 3083933773850794593779197)
                  ·
                    refine ⟨1156475165194047972667199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083933773850794593779197 1156475165194047972667199)
                    ·
                      rfl

theorem cell22_3378341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_3378341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378341 prefixEnd_3378341 := by exact prefixLift 3378341
  have htrace : WordTrace (prefixWord ++ tailWord_3378341) baseStart_3378341 baseEnd_3378341 := by
    simpa [prefixWord, tailWord_3378341, baseEnd_3378341] using wordTrace_append hprefix tailTrace_3378341
  have hstable : (prefixWord ++ tailWord_3378341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378341).length < 2 ^ (prefixWord ++ tailWord_3378341).sum := by decide
  have hdescent : baseEnd_3378341 < baseStart_3378341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378343 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 4]
def baseStart_3378343 : Nat := 118140960795 + 3378343 * 2 ^ 59
def prefixEnd_3378343 : Nat := 4983230072969 + 3 ^ 40 * 3378343 * 2
def baseEnd_3378343 : Nat := 385491949944973544705731

theorem tailTrace_3378343 : CollatzResearch.WordTrace tailWord_3378343 prefixEnd_3378343 385491949944973544705731 := by
  unfold tailWord_3378343
  simp only [CollatzResearch.WordTrace]
  refine ⟨123218291999847760894179683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82145527999898507262786455 123218291999847760894179683)
  ·
    refine ⟨184827437999771641341269525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123218291999847760894179683 184827437999771641341269525)
    ·
      refine ⟨8663786156239295687872009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184827437999771641341269525 8663786156239295687872009)
      ·
        refine ⟨6497839617179471765904007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8663786156239295687872009 6497839617179471765904007)
        ·
          refine ⟨9746759425769207648856011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497839617179471765904007 9746759425769207648856011)
          ·
            refine ⟨14620139138653811473284017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746759425769207648856011 14620139138653811473284017)
            ·
              refine ⟨10965104353990358604963013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14620139138653811473284017 10965104353990358604963013)
              ·
                refine ⟨2055957066373192238430565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10965104353990358604963013 2055957066373192238430565)
                ·
                  refine ⟨385491949944973544705731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055957066373192238430565 385491949944973544705731)
                  ·
                    rfl

theorem cell22_3378343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 4].length) (baseStart_3378343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378343 prefixEnd_3378343 := by exact prefixLift 3378343
  have htrace : WordTrace (prefixWord ++ tailWord_3378343) baseStart_3378343 baseEnd_3378343 := by
    simpa [prefixWord, tailWord_3378343, baseEnd_3378343] using wordTrace_append hprefix tailTrace_3378343
  have hstable : (prefixWord ++ tailWord_3378343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378343).length < 2 ^ (prefixWord ++ tailWord_3378343).sum := by decide
  have hdescent : baseEnd_3378343 < baseStart_3378343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378388 : List Nat := [2, 4, 1, 4, 1, 2, 8]
def baseStart_3378388 : Nat := 118140960795 + 3378388 * 2 ^ 59
def prefixEnd_3378388 : Nat := 4983230072969 + 3 ^ 40 * 3378388 * 2
def baseEnd_3378388 : Nat := 42833009416835389508965

theorem tailTrace_3378388 : CollatzResearch.WordTrace tailWord_3378388 prefixEnd_3378388 42833009416835389508965 := by
  unfold tailWord_3378388
  simp only [CollatzResearch.WordTrace]
  refine ⟨61609966642342366789783909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82146622189789822386378545 61609966642342366789783909)
  ·
    refine ⟨11551868745439193773084483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61609966642342366789783909 11551868745439193773084483)
    ·
      refine ⟨17327803118158790659626725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11551868745439193773084483 17327803118158790659626725)
      ·
        refine ⟨3248963084654773248680011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17327803118158790659626725 3248963084654773248680011)
        ·
          refine ⟨4873444626982159873020017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248963084654773248680011 4873444626982159873020017)
          ·
            refine ⟨3655083470236619904765013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873444626982159873020017 3655083470236619904765013)
            ·
              refine ⟨42833009416835389508965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3655083470236619904765013 42833009416835389508965)
              ·
                rfl

theorem cell22_3378388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 8].length) (baseStart_3378388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378388 prefixEnd_3378388 := by exact prefixLift 3378388
  have htrace : WordTrace (prefixWord ++ tailWord_3378388) baseStart_3378388 baseEnd_3378388 := by
    simpa [prefixWord, tailWord_3378388, baseEnd_3378388] using wordTrace_append hprefix tailTrace_3378388
  have hstable : (prefixWord ++ tailWord_3378388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378388).length < 2 ^ (prefixWord ++ tailWord_3378388).sum := by decide
  have hdescent : baseEnd_3378388 < baseStart_3378388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378390 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3378390 : Nat := 118140960795 + 3378390 * 2 ^ 59
def prefixEnd_3378390 : Nat := 4983230072969 + 3 ^ 40 * 3378390 * 2
def baseEnd_3378390 : Nat := 1156491938895428178192049

theorem tailTrace_3378390 : CollatzResearch.WordTrace tailWord_3378390 prefixEnd_3378390 1156491938895428178192049 := by
  unfold tailWord_3378390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701250389417342995071289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82146670820451658614093749 7701250389417342995071289)
  ·
    refine ⟨5775937792063007246303467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7701250389417342995071289 5775937792063007246303467)
    ·
      refine ⟨8663906688094510869455201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5775937792063007246303467 8663906688094510869455201)
      ·
        refine ⟨6497930016070883152091401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8663906688094510869455201 6497930016070883152091401)
        ·
          refine ⟨4873447512053162364068551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497930016070883152091401 4873447512053162364068551)
          ·
            refine ⟨7310171268079743546102827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873447512053162364068551 7310171268079743546102827)
            ·
              refine ⟨10965256902119615319154241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310171268079743546102827 10965256902119615319154241)
              ·
                refine ⟨8223942676589711489365681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965256902119615319154241 8223942676589711489365681)
                ·
                  refine ⟨6167957007442283617024261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8223942676589711489365681 6167957007442283617024261)
                  ·
                    refine ⟨1156491938895428178192049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167957007442283617024261 1156491938895428178192049)
                    ·
                      rfl

theorem cell22_3378390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3378390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378390 prefixEnd_3378390 := by exact prefixLift 3378390
  have htrace : WordTrace (prefixWord ++ tailWord_3378390) baseStart_3378390 baseEnd_3378390 := by
    simpa [prefixWord, tailWord_3378390, baseEnd_3378390] using wordTrace_append hprefix tailTrace_3378390
  have hstable : (prefixWord ++ tailWord_3378390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378390).length < 2 ^ (prefixWord ++ tailWord_3378390).sum := by decide
  have hdescent : baseEnd_3378390 < baseStart_3378390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378399 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 7]
def baseStart_3378399 : Nat := 118140960795 + 3378399 * 2 ^ 59
def prefixEnd_3378399 : Nat := 4983230072969 + 3 ^ 40 * 3378399 * 2
def baseEnd_3378399 : Nat := 385498339926451718239007

theorem tailTrace_3378399 : CollatzResearch.WordTrace tailWord_3378399 prefixEnd_3378399 385498339926451718239007 := by
  unfold tailWord_3378399
  simp only [CollatzResearch.WordTrace]
  refine ⟨123220334487644882458218251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82146889658429921638812167 123220334487644882458218251)
  ·
    refine ⟨184830501731467323687327377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123220334487644882458218251 184830501731467323687327377)
    ·
      refine ⟨138622876298600492765495533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184830501731467323687327377 138622876298600492765495533)
      ·
        refine ⟨51983578611975184787060825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138622876298600492765495533 51983578611975184787060825)
        ·
          refine ⟨38987683958981388590295619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51983578611975184787060825 38987683958981388590295619)
          ·
            refine ⟨58481525938472082885443429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38987683958981388590295619 58481525938472082885443429)
            ·
              refine ⟨10965286113463515541020643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58481525938472082885443429 10965286113463515541020643)
              ·
                refine ⟨16447929170195273311530965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10965286113463515541020643 16447929170195273311530965)
                ·
                  refine ⟨385498339926451718239007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16447929170195273311530965 385498339926451718239007)
                  ·
                    rfl

theorem cell22_3378399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 7].length) (baseStart_3378399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378399 prefixEnd_3378399 := by exact prefixLift 3378399
  have htrace : WordTrace (prefixWord ++ tailWord_3378399) baseStart_3378399 baseEnd_3378399 := by
    simpa [prefixWord, tailWord_3378399, baseEnd_3378399] using wordTrace_append hprefix tailTrace_3378399
  have hstable : (prefixWord ++ tailWord_3378399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378399).length < 2 ^ (prefixWord ++ tailWord_3378399).sum := by decide
  have hdescent : baseEnd_3378399 < baseStart_3378399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378459 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_3378459 : Nat := 118140960795 + 3378459 * 2 ^ 59
def prefixEnd_3378459 : Nat := 4983230072969 + 3 ^ 40 * 3378459 * 2
def baseEnd_3378459 : Nat := 1156515559005534998216837

theorem tailTrace_3378459 : CollatzResearch.WordTrace tailWord_3378459 prefixEnd_3378459 1156515559005534998216837 := by
  unfold tailWord_3378459
  simp only [CollatzResearch.WordTrace]
  refine ⟨123222522867427512705402431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82148348578285008470268287 123222522867427512705402431)
  ·
    refine ⟨184833784301141269058103647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123222522867427512705402431 184833784301141269058103647)
    ·
      refine ⟨277250676451711903587155471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184833784301141269058103647 277250676451711903587155471)
      ·
        refine ⟨415876014677567855380733207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277250676451711903587155471 415876014677567855380733207)
        ·
          refine ⟨623814022016351783071099811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415876014677567855380733207 623814022016351783071099811)
          ·
            refine ⟨935721033024527674606649717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623814022016351783071099811 935721033024527674606649717)
            ·
              refine ⟨87723846846049469494373411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 935721033024527674606649717 87723846846049469494373411)
              ·
                refine ⟨131585770269074204241560117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87723846846049469494373411 131585770269074204241560117)
                ·
                  refine ⟨12336165962725706647646261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131585770269074204241560117 12336165962725706647646261)
                  ·
                    refine ⟨1156515559005534998216837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12336165962725706647646261 1156515559005534998216837)
                    ·
                      rfl

theorem cell22_3378459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_3378459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378459 prefixEnd_3378459 := by exact prefixLift 3378459
  have htrace : WordTrace (prefixWord ++ tailWord_3378459) baseStart_3378459 baseEnd_3378459 := by
    simpa [prefixWord, tailWord_3378459, baseEnd_3378459] using wordTrace_append hprefix tailTrace_3378459
  have hstable : (prefixWord ++ tailWord_3378459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378459).length < 2 ^ (prefixWord ++ tailWord_3378459).sum := by decide
  have hdescent : baseEnd_3378459 < baseStart_3378459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378476 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_3378476 : Nat := 118140960795 + 3378476 * 2 ^ 59
def prefixEnd_3378476 : Nat := 4983230072969 + 3 ^ 40 * 3378476 * 2
def baseEnd_3378476 : Nat := 1156521378452952620541785

theorem tailTrace_3378476 : CollatzResearch.WordTrace tailWord_3378476 prefixEnd_3378476 1156521378452952620541785 := by
  unfold tailWord_3378476
  simp only [CollatzResearch.WordTrace]
  refine ⟨61611571454182962304385641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82148761938910616405847521 61611571454182962304385641)
  ·
    refine ⟨46208678590637221728289231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61611571454182962304385641 46208678590637221728289231)
    ·
      refine ⟨69313017885955832592433847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46208678590637221728289231 69313017885955832592433847)
      ·
        refine ⟨103969526828933748888650771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69313017885955832592433847 103969526828933748888650771)
        ·
          refine ⟨155954290243400623332976157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103969526828933748888650771 155954290243400623332976157)
          ·
            refine ⟨58482858841275233749866059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155954290243400623332976157 58482858841275233749866059)
            ·
              refine ⟨87724288261912850624799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58482858841275233749866059 87724288261912850624799089)
              ·
                refine ⟨65793216196434637968599317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87724288261912850624799089 65793216196434637968599317)
                ·
                  refine ⟨3084057009207873654778093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65793216196434637968599317 3084057009207873654778093)
                  ·
                    refine ⟨1156521378452952620541785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084057009207873654778093 1156521378452952620541785)
                    ·
                      rfl

theorem cell22_3378476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_3378476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378476 prefixEnd_3378476 := by exact prefixLift 3378476
  have htrace : WordTrace (prefixWord ++ tailWord_3378476) baseStart_3378476 baseEnd_3378476 := by
    simpa [prefixWord, tailWord_3378476, baseEnd_3378476] using wordTrace_append hprefix tailTrace_3378476
  have hstable : (prefixWord ++ tailWord_3378476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378476).length < 2 ^ (prefixWord ++ tailWord_3378476).sum := by decide
  have hdescent : baseEnd_3378476 < baseStart_3378476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378497 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3378497 : Nat := 118140960795 + 3378497 * 2 ^ 59
def prefixEnd_3378497 : Nat := 4983230072969 + 3 ^ 40 * 3378497 * 2
def baseEnd_3378497 : Nat := 1156528567182115565766721

theorem tailTrace_3378497 : CollatzResearch.WordTrace tailWord_3378497 prefixEnd_3378497 1156528567182115565766721 := by
  unfold tailWord_3378497
  simp only [CollatzResearch.WordTrace]
  refine ⟨123223908841289845195285745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82149272560859896796857163 123223908841289845195285745)
  ·
    refine ⟨92417931630967383896464309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123223908841289845195285745 92417931630967383896464309)
    ·
      refine ⟨8664181090403192240293529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92417931630967383896464309 8664181090403192240293529)
      ·
        refine ⟨6498135817802394180220147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8664181090403192240293529 6498135817802394180220147)
        ·
          refine ⟨9747203726703591270330221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498135817802394180220147 9747203726703591270330221)
          ·
            refine ⟨3655201397513846726373833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9747203726703591270330221 3655201397513846726373833)
            ·
              refine ⟨2741401048135385044780375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3655201397513846726373833 2741401048135385044780375)
              ·
                refine ⟨4112101572203077567170563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741401048135385044780375 4112101572203077567170563)
                ·
                  refine ⟨6168152358304616350755845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112101572203077567170563 6168152358304616350755845)
                  ·
                    refine ⟨1156528567182115565766721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6168152358304616350755845 1156528567182115565766721)
                    ·
                      rfl

theorem cell22_3378497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3378497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378497 prefixEnd_3378497 := by exact prefixLift 3378497
  have htrace : WordTrace (prefixWord ++ tailWord_3378497) baseStart_3378497 baseEnd_3378497 := by
    simpa [prefixWord, tailWord_3378497, baseEnd_3378497] using wordTrace_append hprefix tailTrace_3378497
  have hstable : (prefixWord ++ tailWord_3378497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378497).length < 2 ^ (prefixWord ++ tailWord_3378497).sum := by decide
  have hdescent : baseEnd_3378497 < baseStart_3378497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378572 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_3378572 : Nat := 118140960795 + 3378572 * 2 ^ 59
def prefixEnd_3378572 : Nat := 4983230072969 + 3 ^ 40 * 3378572 * 2
def baseEnd_3378572 : Nat := 1156554241214840370141491

theorem tailTrace_3378572 : CollatzResearch.WordTrace tailWord_3378572 prefixEnd_3378572 1156554241214840370141491 := by
  unfold tailWord_3378572
  simp only [CollatzResearch.WordTrace]
  refine ⟨61613322158009066502132985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82151096210678755336177313 61613322158009066502132985)
  ·
    refine ⟨46209991618506799876599739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61613322158009066502132985 46209991618506799876599739)
    ·
      refine ⟨69314987427760199814899609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46209991618506799876599739 69314987427760199814899609)
      ·
        refine ⟨51986240570820149861174707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69314987427760199814899609 51986240570820149861174707)
        ·
          refine ⟨77979360856230224791762061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51986240570820149861174707 77979360856230224791762061)
          ·
            refine ⟨29242260321086334296910773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77979360856230224791762061 29242260321086334296910773)
            ·
              refine ⟨2741461905101843840335385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29242260321086334296910773 2741461905101843840335385)
              ·
                refine ⟨2056096428826382880251539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741461905101843840335385 2056096428826382880251539)
                ·
                  refine ⟨3084144643239574320377309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056096428826382880251539 3084144643239574320377309)
                  ·
                    refine ⟨1156554241214840370141491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084144643239574320377309 1156554241214840370141491)
                    ·
                      rfl

theorem cell22_3378572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_3378572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378572 prefixEnd_3378572 := by exact prefixLift 3378572
  have htrace : WordTrace (prefixWord ++ tailWord_3378572) baseStart_3378572 baseEnd_3378572 := by
    simpa [prefixWord, tailWord_3378572, baseEnd_3378572] using wordTrace_append hprefix tailTrace_3378572
  have hstable : (prefixWord ++ tailWord_3378572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378572).length < 2 ^ (prefixWord ++ tailWord_3378572).sum := by decide
  have hdescent : baseEnd_3378572 < baseStart_3378572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378585 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 5]
def baseStart_3378585 : Nat := 118140960795 + 3378585 * 2 ^ 59
def prefixEnd_3378585 : Nat := 4983230072969 + 3 ^ 40 * 3378585 * 2
def baseEnd_3378585 : Nat := 385519563793504223188817

theorem tailTrace_3378585 : CollatzResearch.WordTrace tailWord_3378585 prefixEnd_3378585 385519563793504223188817 := by
  unfold tailWord_3378585
  simp only [CollatzResearch.WordTrace]
  refine ⟨123227118464971036224489209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82151412309980690816326139 123227118464971036224489209)
  ·
    refine ⟨92420338848728277168366907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123227118464971036224489209 92420338848728277168366907)
    ·
      refine ⟨138630508273092415752550361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92420338848728277168366907 138630508273092415752550361)
      ·
        refine ⟨103972881204819311814412771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138630508273092415752550361 103972881204819311814412771)
        ·
          refine ⟨155959321807228967721619157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103972881204819311814412771 155959321807228967721619157)
          ·
            refine ⟨3655296604856928930975449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 155959321807228967721619157 3655296604856928930975449)
            ·
              refine ⟨2741472453642696698231587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3655296604856928930975449 2741472453642696698231587)
              ·
                refine ⟨4112208680464045047347381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741472453642696698231587 4112208680464045047347381)
                ·
                  refine ⟨385519563793504223188817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4112208680464045047347381 385519563793504223188817)
                  ·
                    rfl

theorem cell22_3378585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_3378585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378585 prefixEnd_3378585 := by exact prefixLift 3378585
  have htrace : WordTrace (prefixWord ++ tailWord_3378585) baseStart_3378585 baseEnd_3378585 := by
    simpa [prefixWord, tailWord_3378585, baseEnd_3378585] using wordTrace_append hprefix tailTrace_3378585
  have hstable : (prefixWord ++ tailWord_3378585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378585).length < 2 ^ (prefixWord ++ tailWord_3378585).sum := by decide
  have hdescent : baseEnd_3378585 < baseStart_3378585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378596 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_3378596 : Nat := 118140960795 + 3378596 * 2 ^ 59
def prefixEnd_3378596 : Nat := 4983230072969 + 3 ^ 40 * 3378596 * 2
def baseEnd_3378596 : Nat := 385520818968437435847139

theorem tailTrace_3378596 : CollatzResearch.WordTrace tailWord_3378596 prefixEnd_3378596 385520818968437435847139 := by
  unfold tailWord_3378596
  simp only [CollatzResearch.WordTrace]
  refine ⟨61613759833965592551569821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82151679778620790068759761 61613759833965592551569821)
  ·
    refine ⟨23105159937737097206838683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61613759833965592551569821 23105159937737097206838683)
    ·
      refine ⟨34657739906605645810258025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23105159937737097206838683 34657739906605645810258025)
      ·
        refine ⟨25993304929954234357693519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34657739906605645810258025 25993304929954234357693519)
        ·
          refine ⟨38989957394931351536540279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25993304929954234357693519 38989957394931351536540279)
          ·
            refine ⟨58484936092397027304810419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38989957394931351536540279 58484936092397027304810419)
            ·
              refine ⟨87727404138595540957215629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58484936092397027304810419 87727404138595540957215629)
              ·
                refine ⟨32897776551973327858955861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87727404138595540957215629 32897776551973327858955861)
                ·
                  refine ⟨385520818968437435847139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32897776551973327858955861 385520818968437435847139)
                  ·
                    rfl

theorem cell22_3378596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_3378596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378596 prefixEnd_3378596 := by exact prefixLift 3378596
  have htrace : WordTrace (prefixWord ++ tailWord_3378596) baseStart_3378596 baseEnd_3378596 := by
    simpa [prefixWord, tailWord_3378596, baseEnd_3378596] using wordTrace_append hprefix tailTrace_3378596
  have hstable : (prefixWord ++ tailWord_3378596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378596).length < 2 ^ (prefixWord ++ tailWord_3378596).sum := by decide
  have hdescent : baseEnd_3378596 < baseStart_3378596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378615 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 1, 4]
def baseStart_3378615 : Nat := 118140960795 + 3378615 * 2 ^ 59
def prefixEnd_3378615 : Nat := 4983230072969 + 3 ^ 40 * 3378615 * 2
def baseEnd_3378615 : Nat := 1156568960993602591316359

theorem tailTrace_3378615 : CollatzResearch.WordTrace tailWord_3378615 prefixEnd_3378615 1156568960993602591316359 := by
  unfold tailWord_3378615
  simp only [CollatzResearch.WordTrace]
  refine ⟨123228212654862351348081299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82152141769908234232054199 123228212654862351348081299)
  ·
    refine ⟨184842318982293527022121949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123228212654862351348081299 184842318982293527022121949)
    ·
      refine ⟨69315869618360072633295731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184842318982293527022121949 69315869618360072633295731)
      ·
        refine ⟨103973804427540108949943597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69315869618360072633295731 103973804427540108949943597)
        ·
          refine ⟨38990176660327540856228849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103973804427540108949943597 38990176660327540856228849)
          ·
            refine ⟨29242632495245655642171637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38990176660327540856228849 29242632495245655642171637)
            ·
              refine ⟨2741496796429280216453591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29242632495245655642171637 2741496796429280216453591)
              ·
                refine ⟨4112245194643920324680387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741496796429280216453591 4112245194643920324680387)
                ·
                  refine ⟨6168367791965880487020581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112245194643920324680387 6168367791965880487020581)
                  ·
                    refine ⟨1156568960993602591316359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6168367791965880487020581 1156568960993602591316359)
                    ·
                      rfl

theorem cell22_3378615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_3378615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378615 prefixEnd_3378615 := by exact prefixLift 3378615
  have htrace : WordTrace (prefixWord ++ tailWord_3378615) baseStart_3378615 baseEnd_3378615 := by
    simpa [prefixWord, tailWord_3378615, baseEnd_3378615] using wordTrace_append hprefix tailTrace_3378615
  have hstable : (prefixWord ++ tailWord_3378615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378615).length < 2 ^ (prefixWord ++ tailWord_3378615).sum := by decide
  have hdescent : baseEnd_3378615 < baseStart_3378615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378645 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_3378645 : Nat := 118140960795 + 3378645 * 2 ^ 59
def prefixEnd_3378645 : Nat := 4983230072969 + 3 ^ 40 * 3378645 * 2
def baseEnd_3378645 : Nat := 1156579230606692513066267

theorem tailTrace_3378645 : CollatzResearch.WordTrace tailWord_3378645 prefixEnd_3378645 1156579230606692513066267 := by
  unfold tailWord_3378645
  simp only [CollatzResearch.WordTrace]
  refine ⟨123229306844753666471673389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82152871229835777647782259 123229306844753666471673389)
  ·
    refine ⟨46210990066782624926877521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123229306844753666471673389 46210990066782624926877521)
    ·
      refine ⟨34658242550086968695158141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46210990066782624926877521 34658242550086968695158141)
      ·
        refine ⟨12996840956282613260684303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34658242550086968695158141 12996840956282613260684303)
        ·
          refine ⟨19495261434423919891026455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12996840956282613260684303 19495261434423919891026455)
          ·
            refine ⟨29242892151635879836539683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19495261434423919891026455 29242892151635879836539683)
            ·
              refine ⟨43864338227453819754809525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29242892151635879836539683 43864338227453819754809525)
              ·
                refine ⟨4112281708823795602013393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43864338227453819754809525 4112281708823795602013393)
                ·
                  refine ⟨3084211281617846701510045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112281708823795602013393 3084211281617846701510045)
                  ·
                    refine ⟨1156579230606692513066267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084211281617846701510045 1156579230606692513066267)
                    ·
                      rfl

theorem cell22_3378645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_3378645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378645 prefixEnd_3378645 := by exact prefixLift 3378645
  have htrace : WordTrace (prefixWord ++ tailWord_3378645) baseStart_3378645 baseEnd_3378645 := by
    simpa [prefixWord, tailWord_3378645, baseEnd_3378645] using wordTrace_append hprefix tailTrace_3378645
  have hstable : (prefixWord ++ tailWord_3378645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378645).length < 2 ^ (prefixWord ++ tailWord_3378645).sum := by decide
  have hdescent : baseEnd_3378645 < baseStart_3378645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378656 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_3378656 : Nat := 118140960795 + 3378656 * 2 ^ 59
def prefixEnd_3378656 : Nat := 4983230072969 + 3 ^ 40 * 3378656 * 2
def baseEnd_3378656 : Nat := 1156582996131492151041233

theorem tailTrace_3378656 : CollatzResearch.WordTrace tailWord_3378656 prefixEnd_3378656 1156582996131492151041233 := by
  unfold tailWord_3378656
  simp only [CollatzResearch.WordTrace]
  refine ⟨61614854023856907675161911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82153138698475876900215881 61614854023856907675161911)
  ·
    refine ⟨92422281035785361512742867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61614854023856907675161911 92422281035785361512742867)
    ·
      refine ⟨138633421553678042269114301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92422281035785361512742867 138633421553678042269114301)
      ·
        refine ⟨51987533082629265850917863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138633421553678042269114301 51987533082629265850917863)
        ·
          refine ⟨77981299623943898776376795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51987533082629265850917863 77981299623943898776376795)
          ·
            refine ⟨116971949435915848164565193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77981299623943898776376795 116971949435915848164565193)
            ·
              refine ⟨87728962076936886123423895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116971949435915848164565193 87728962076936886123423895)
              ·
                refine ⟨131593443115405329185135843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87728962076936886123423895 131593443115405329185135843)
                ·
                  refine ⟨197390164673107993777703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131593443115405329185135843 197390164673107993777703765)
                  ·
                    refine ⟨1156582996131492151041233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 197390164673107993777703765 1156582996131492151041233)
                    ·
                      rfl

theorem cell22_3378656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_3378656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378656 prefixEnd_3378656 := by exact prefixLift 3378656
  have htrace : WordTrace (prefixWord ++ tailWord_3378656) baseStart_3378656 baseEnd_3378656 := by
    simpa [prefixWord, tailWord_3378656, baseEnd_3378656] using wordTrace_append hprefix tailTrace_3378656
  have hstable : (prefixWord ++ tailWord_3378656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378656).length < 2 ^ (prefixWord ++ tailWord_3378656).sum := by decide
  have hdescent : baseEnd_3378656 < baseStart_3378656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378763 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 1, 5]
def baseStart_3378763 : Nat := 118140960795 + 3378763 * 2 ^ 59
def prefixEnd_3378763 : Nat := 4983230072969 + 3 ^ 40 * 3378763 * 2
def baseEnd_3378763 : Nat := 1156619624418179538615905

theorem tailTrace_3378763 : CollatzResearch.WordTrace tailWord_3378763 prefixEnd_3378763 1156619624418179538615905 := by
  unfold tailWord_3378763
  simp only [CollatzResearch.WordTrace]
  refine ⟨123233610658326172624468943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82155740438884115082979295 123233610658326172624468943)
  ·
    refine ⟨184850415987489258936703415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123233610658326172624468943 184850415987489258936703415)
    ·
      refine ⟨277275623981233888405055123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184850415987489258936703415 277275623981233888405055123)
      ·
        refine ⟨415913435971850832607582685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277275623981233888405055123 415913435971850832607582685)
        ·
          refine ⟨155967538489444062227843507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415913435971850832607582685 155967538489444062227843507)
          ·
            refine ⟨233951307734166093341765261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155967538489444062227843507 233951307734166093341765261)
            ·
              refine ⟨87731740400312285003161973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233951307734166093341765261 87731740400312285003161973)
              ·
                refine ⟨8224850662529276719046435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87731740400312285003161973 8224850662529276719046435)
                ·
                  refine ⟨12337275993793915078569653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224850662529276719046435 12337275993793915078569653)
                  ·
                    refine ⟨1156619624418179538615905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12337275993793915078569653 1156619624418179538615905)
                    ·
                      rfl

theorem cell22_3378763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_3378763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378763 prefixEnd_3378763 := by exact prefixLift 3378763
  have htrace : WordTrace (prefixWord ++ tailWord_3378763) baseStart_3378763 baseEnd_3378763 := by
    simpa [prefixWord, tailWord_3378763, baseEnd_3378763] using wordTrace_append hprefix tailTrace_3378763
  have hstable : (prefixWord ++ tailWord_3378763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378763).length < 2 ^ (prefixWord ++ tailWord_3378763).sum := by decide
  have hdescent : baseEnd_3378763 < baseStart_3378763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378778 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_3378778 : Nat := 118140960795 + 3378778 * 2 ^ 59
def prefixEnd_3378778 : Nat := 4983230072969 + 3 ^ 40 * 3378778 * 2
def baseEnd_3378778 : Nat := 1156624759224724499490859

theorem tailTrace_3378778 : CollatzResearch.WordTrace tailWord_3378778 prefixEnd_3378778 1156624759224724499490859 := by
  unfold tailWord_3378778
  simp only [CollatzResearch.WordTrace]
  refine ⟨30808539438317957546566247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82156105168847886790843325 30808539438317957546566247)
  ·
    refine ⟨46212809157476936319849371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30808539438317957546566247 46212809157476936319849371)
    ·
      refine ⟨69319213736215404479774057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46212809157476936319849371 69319213736215404479774057)
      ·
        refine ⟨51989410302161553359830543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69319213736215404479774057 51989410302161553359830543)
        ·
          refine ⟨77984115453242330039745815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51989410302161553359830543 77984115453242330039745815)
          ·
            refine ⟨116976173179863495059618723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77984115453242330039745815 116976173179863495059618723)
            ·
              refine ⟨175464259769795242589428085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116976173179863495059618723 175464259769795242589428085)
              ·
                refine ⟨16449774353418303992758883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175464259769795242589428085 16449774353418303992758883)
                ·
                  refine ⟨24674661530127455989138325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16449774353418303992758883 24674661530127455989138325)
                  ·
                    refine ⟨1156624759224724499490859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24674661530127455989138325 1156624759224724499490859)
                    ·
                      rfl

theorem cell22_3378778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_3378778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378778 prefixEnd_3378778 := by exact prefixLift 3378778
  have htrace : WordTrace (prefixWord ++ tailWord_3378778) baseStart_3378778 baseEnd_3378778 := by
    simpa [prefixWord, tailWord_3378778, baseEnd_3378778] using wordTrace_append hprefix tailTrace_3378778
  have hstable : (prefixWord ++ tailWord_3378778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378778).length < 2 ^ (prefixWord ++ tailWord_3378778).sum := by decide
  have hdescent : baseEnd_3378778 < baseStart_3378778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378780 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3378780 : Nat := 118140960795 + 3378780 * 2 ^ 59
def prefixEnd_3378780 : Nat := 4983230072969 + 3 ^ 40 * 3378780 * 2
def baseEnd_3378780 : Nat := 1156625443865597160940853

theorem tailTrace_3378780 : CollatzResearch.WordTrace tailWord_3378780 prefixEnd_3378780 1156625443865597160940853 := by
  unfold tailWord_3378780
  simp only [CollatzResearch.WordTrace]
  refine ⟨61617115349632292263918897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82156153799509723018558529 61617115349632292263918897)
  ·
    refine ⟨46212836512224219197939173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61617115349632292263918897 46212836512224219197939173)
    ·
      refine ⟨8664906846042041099613595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46212836512224219197939173 8664906846042041099613595)
      ·
        refine ⟨12997360269063061649420393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8664906846042041099613595 12997360269063061649420393)
        ·
          refine ⟨9748020201797296237065295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12997360269063061649420393 9748020201797296237065295)
          ·
            refine ⟨14622030302695944355597943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748020201797296237065295 14622030302695944355597943)
            ·
              refine ⟨21933045454043916533396915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14622030302695944355597943 21933045454043916533396915)
              ·
                refine ⟨32899568181065874800095373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21933045454043916533396915 32899568181065874800095373)
                ·
                  refine ⟨12337338067899703050035765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32899568181065874800095373 12337338067899703050035765)
                  ·
                    refine ⟨1156625443865597160940853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12337338067899703050035765 1156625443865597160940853)
                    ·
                      rfl

theorem cell22_3378780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3378780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378780 prefixEnd_3378780 := by exact prefixLift 3378780
  have htrace : WordTrace (prefixWord ++ tailWord_3378780) baseStart_3378780 baseEnd_3378780 := by
    simpa [prefixWord, tailWord_3378780, baseEnd_3378780] using wordTrace_append hprefix tailTrace_3378780
  have hstable : (prefixWord ++ tailWord_3378780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378780).length < 2 ^ (prefixWord ++ tailWord_3378780).sum := by decide
  have hdescent : baseEnd_3378780 < baseStart_3378780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378825 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_3378825 : Nat := 118140960795 + 3378825 * 2 ^ 59
def prefixEnd_3378825 : Nat := 4983230072969 + 3 ^ 40 * 3378825 * 2
def baseEnd_3378825 : Nat := 1156640848285232043565715

theorem tailTrace_3378825 : CollatzResearch.WordTrace tailWord_3378825 prefixEnd_3378825 1156640848285232043565715 := by
  unfold tailWord_3378825
  simp only [CollatzResearch.WordTrace]
  refine ⟨123235871984101557213225929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82157247989401038142150619 123235871984101557213225929)
  ·
    refine ⟨92426903988076167909919447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123235871984101557213225929 92426903988076167909919447)
    ·
      refine ⟨138640355982114251864879171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92426903988076167909919447 138640355982114251864879171)
      ·
        refine ⟨207960533973171377797318757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138640355982114251864879171 207960533973171377797318757)
        ·
          refine ⟨38992600119969633336997267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207960533973171377797318757 38992600119969633336997267)
          ·
            refine ⟨58488900179954450005495901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38992600119969633336997267 58488900179954450005495901)
            ·
              refine ⟨21933337567482918752060963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58488900179954450005495901 21933337567482918752060963)
              ·
                refine ⟨32900006351224378128091445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21933337567482918752060963 32900006351224378128091445)
                ·
                  refine ⟨3084375595427285449508573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32900006351224378128091445 3084375595427285449508573)
                  ·
                    refine ⟨1156640848285232043565715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084375595427285449508573 1156640848285232043565715)
                    ·
                      rfl

theorem cell22_3378825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_3378825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378825 prefixEnd_3378825 := by exact prefixLift 3378825
  have htrace : WordTrace (prefixWord ++ tailWord_3378825) baseStart_3378825 baseEnd_3378825 := by
    simpa [prefixWord, tailWord_3378825, baseEnd_3378825] using wordTrace_append hprefix tailTrace_3378825
  have hstable : (prefixWord ++ tailWord_3378825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378825).length < 2 ^ (prefixWord ++ tailWord_3378825).sum := by decide
  have hdescent : baseEnd_3378825 < baseStart_3378825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378893 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3378893 : Nat := 118140960795 + 3378893 * 2 ^ 59
def prefixEnd_3378893 : Nat := 4983230072969 + 3 ^ 40 * 3378893 * 2
def baseEnd_3378893 : Nat := 1156664126074902532865507

theorem tailTrace_3378893 : CollatzResearch.WordTrace tailWord_3378893 prefixEnd_3378893 1156664126074902532865507 := by
  unfold tailWord_3378893
  simp only [CollatzResearch.WordTrace]
  refine ⟨123238352147855204826701333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82158901431903469884467555 123238352147855204826701333)
  ·
    refine ⟨5776797756930712726251625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123238352147855204826701333 5776797756930712726251625)
    ·
      refine ⟨4332598317698034544688719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5776797756930712726251625 4332598317698034544688719)
      ·
        refine ⟨6498897476547051817033079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332598317698034544688719 6498897476547051817033079)
        ·
          refine ⟨9748346214820577725549619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498897476547051817033079 9748346214820577725549619)
          ·
            refine ⟨14622519322230866588324429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748346214820577725549619 14622519322230866588324429)
            ·
              refine ⟨5483444745836574970621661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14622519322230866588324429 5483444745836574970621661)
              ·
                refine ⟨2056291779688715613983123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5483444745836574970621661 2056291779688715613983123)
                ·
                  refine ⟨3084437669533073420974685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056291779688715613983123 3084437669533073420974685)
                  ·
                    refine ⟨1156664126074902532865507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084437669533073420974685 1156664126074902532865507)
                    ·
                      rfl

theorem cell22_3378893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3378893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378893 prefixEnd_3378893 := by exact prefixLift 3378893
  have htrace : WordTrace (prefixWord ++ tailWord_3378893) baseStart_3378893 baseEnd_3378893 := by
    simpa [prefixWord, tailWord_3378893, baseEnd_3378893] using wordTrace_append hprefix tailTrace_3378893
  have hstable : (prefixWord ++ tailWord_3378893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378893).length < 2 ^ (prefixWord ++ tailWord_3378893).sum := by decide
  have hdescent : baseEnd_3378893 < baseStart_3378893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378945 : List Nat := [1, 2, 4, 1, 1, 1, 4, 8]
def baseStart_3378945 : Nat := 118140960795 + 3378945 * 2 ^ 59
def prefixEnd_3378945 : Nat := 4983230072969 + 3 ^ 40 * 3378945 * 2
def baseEnd_3378945 : Nat := 128520214081954636729483

theorem tailTrace_3378945 : CollatzResearch.WordTrace tailWord_3378945 prefixEnd_3378945 128520214081954636729483 := by
  unfold tailWord_3378945
  simp only [CollatzResearch.WordTrace]
  refine ⟨123240248743666817707594289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82160165829111211805062859 123240248743666817707594289)
  ·
    refine ⟨92430186557750113280695717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123240248743666817707594289 92430186557750113280695717)
    ·
      refine ⟨17330659979578146240130447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92430186557750113280695717 17330659979578146240130447)
      ·
        refine ⟨25995989969367219360195671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17330659979578146240130447 25995989969367219360195671)
        ·
          refine ⟨38993984954050829040293507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25995989969367219360195671 38993984954050829040293507)
          ·
            refine ⟨58490977431076243560440261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38993984954050829040293507 58490977431076243560440261)
            ·
              refine ⟨10967058268326795667582549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58490977431076243560440261 10967058268326795667582549)
              ·
                refine ⟨128520214081954636729483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10967058268326795667582549 128520214081954636729483)
                ·
                  rfl

theorem cell22_3378945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 8].length) (baseStart_3378945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378945 prefixEnd_3378945 := by exact prefixLift 3378945
  have htrace : WordTrace (prefixWord ++ tailWord_3378945) baseStart_3378945 baseEnd_3378945 := by
    simpa [prefixWord, tailWord_3378945, baseEnd_3378945] using wordTrace_append hprefix tailTrace_3378945
  have hstable : (prefixWord ++ tailWord_3378945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378945).length < 2 ^ (prefixWord ++ tailWord_3378945).sum := by decide
  have hdescent : baseEnd_3378945 < baseStart_3378945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378962 : List Nat := [3, 2, 4, 1, 1, 11]
def baseStart_3378962 : Nat := 118140960795 + 3378962 * 2 ^ 59
def prefixEnd_3378962 : Nat := 4983230072969 + 3 ^ 40 * 3378962 * 2
def baseEnd_3378962 : Nat := 14280095631913695714695

theorem tailTrace_3378962 : CollatzResearch.WordTrace tailWord_3378962 prefixEnd_3378962 14280095631913695714695 := by
  unfold tailWord_3378962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30810217196151307402740785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82160579189736819740642093 30810217196151307402740785)
  ·
    refine ⟨23107662897113480552055589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30810217196151307402740785 23107662897113480552055589)
    ·
      refine ⟨4332686793208777603510423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23107662897113480552055589 4332686793208777603510423)
      ·
        refine ⟨6499030189813166405265635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332686793208777603510423 6499030189813166405265635)
        ·
          refine ⟨9748545284719749607898453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499030189813166405265635 9748545284719749607898453)
          ·
            refine ⟨14280095631913695714695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9748545284719749607898453 14280095631913695714695)
            ·
              rfl

theorem cell22_3378962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 11].length) (baseStart_3378962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378962 prefixEnd_3378962 := by exact prefixLift 3378962
  have htrace : WordTrace (prefixWord ++ tailWord_3378962) baseStart_3378962 baseEnd_3378962 := by
    simpa [prefixWord, tailWord_3378962, baseEnd_3378962] using wordTrace_append hprefix tailTrace_3378962
  have hstable : (prefixWord ++ tailWord_3378962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378962).length < 2 ^ (prefixWord ++ tailWord_3378962).sum := by decide
  have hdescent : baseEnd_3378962 < baseStart_3378962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378975 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_3378975 : Nat := 118140960795 + 3378975 * 2 ^ 59
def prefixEnd_3378975 : Nat := 4983230072969 + 3 ^ 40 * 3378975 * 2
def baseEnd_3378975 : Nat := 1156692196350681652315255

theorem tailTrace_3378975 : CollatzResearch.WordTrace tailWord_3378975 prefixEnd_3378975 1156692196350681652315255 := by
  unfold tailWord_3378975
  simp only [CollatzResearch.WordTrace]
  refine ⟨123241342933558132831186379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82160895289038755220790919 123241342933558132831186379)
  ·
    refine ⟨184862014400337199246779569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123241342933558132831186379 184862014400337199246779569)
    ·
      refine ⟨138646510800252899435084677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184862014400337199246779569 138646510800252899435084677)
      ·
        refine ⟨25996220775047418644078377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138646510800252899435084677 25996220775047418644078377)
        ·
          refine ⟨19497165581285563983058783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25996220775047418644078377 19497165581285563983058783)
          ·
            refine ⟨29245748371928345974588175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19497165581285563983058783 29245748371928345974588175)
            ·
              refine ⟨43868622557892518961882263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29245748371928345974588175 43868622557892518961882263)
              ·
                refine ⟨65802933836838778442823395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43868622557892518961882263 65802933836838778442823395)
                ·
                  refine ⟨98704400755258167664235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65802933836838778442823395 98704400755258167664235093)
                  ·
                    refine ⟨1156692196350681652315255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98704400755258167664235093 1156692196350681652315255)
                    ·
                      rfl

theorem cell22_3378975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_3378975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378975 prefixEnd_3378975 := by exact prefixLift 3378975
  have htrace : WordTrace (prefixWord ++ tailWord_3378975) baseStart_3378975 baseEnd_3378975 := by
    simpa [prefixWord, tailWord_3378975, baseEnd_3378975] using wordTrace_append hprefix tailTrace_3378975
  have hstable : (prefixWord ++ tailWord_3378975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378975).length < 2 ^ (prefixWord ++ tailWord_3378975).sum := by decide
  have hdescent : baseEnd_3378975 < baseStart_3378975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378994 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_3378994 : Nat := 118140960795 + 3378994 * 2 ^ 59
def prefixEnd_3378994 : Nat := 4983230072969 + 3 ^ 40 * 3378994 * 2
def baseEnd_3378994 : Nat := 1156698700438971936090197

theorem tailTrace_3378994 : CollatzResearch.WordTrace tailWord_3378994 prefixEnd_3378994 1156698700438971936090197 := by
  unfold tailWord_3378994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30810508980122324769032009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82161357280326199384085357 30810508980122324769032009)
  ·
    refine ⟨23107881735091743576774007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30810508980122324769032009 23107881735091743576774007)
    ·
      refine ⟨34661822602637615365161011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23107881735091743576774007 34661822602637615365161011)
      ·
        refine ⟨51992733903956423047741517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34661822602637615365161011 51992733903956423047741517)
        ·
          refine ⟨19497275213983658642903069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51992733903956423047741517 19497275213983658642903069)
          ·
            refine ⟨7311478205243871991088651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19497275213983658642903069 7311478205243871991088651)
            ·
              refine ⟨10967217307865807986632977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7311478205243871991088651 10967217307865807986632977)
              ·
                refine ⟨8225412980899355989974733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10967217307865807986632977 8225412980899355989974733)
                ·
                  refine ⟨3084529867837258496240525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8225412980899355989974733 3084529867837258496240525)
                  ·
                    refine ⟨1156698700438971936090197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084529867837258496240525 1156698700438971936090197)
                    ·
                      rfl

theorem cell22_3378994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_3378994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3378994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3378994 prefixEnd_3378994 := by exact prefixLift 3378994
  have htrace : WordTrace (prefixWord ++ tailWord_3378994) baseStart_3378994 baseEnd_3378994 := by
    simpa [prefixWord, tailWord_3378994, baseEnd_3378994] using wordTrace_append hprefix tailTrace_3378994
  have hstable : (prefixWord ++ tailWord_3378994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378994).length < 2 ^ (prefixWord ++ tailWord_3378994).sum := by decide
  have hdescent : baseEnd_3378994 < baseStart_3378994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379011 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 1, 3]
def baseStart_3379011 : Nat := 118140960795 + 3379011 * 2 ^ 59
def prefixEnd_3379011 : Nat := 4983230072969 + 3 ^ 40 * 3379011 * 2
def baseEnd_3379011 : Nat := 1156704519886389558415145

theorem tailTrace_3379011 : CollatzResearch.WordTrace tailWord_3379011 prefixEnd_3379011 1156704519886389558415145 := by
  unfold tailWord_3379011
  simp only [CollatzResearch.WordTrace]
  refine ⟨123242655961427710979496887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82161770640951807319664591 123242655961427710979496887)
  ·
    refine ⟨184863983942141566469245331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123242655961427710979496887 184863983942141566469245331)
    ·
      refine ⟨277295975913212349703867997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184863983942141566469245331 277295975913212349703867997)
      ·
        refine ⟨103985990967454631138950499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277295975913212349703867997 103985990967454631138950499)
        ·
          refine ⟨155978986451181946708425749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103985990967454631138950499 155978986451181946708425749)
          ·
            refine ⟨7311514989899153751957457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155978986451181946708425749 7311514989899153751957457)
            ·
              refine ⟨5483636242424365313968093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7311514989899153751957457 5483636242424365313968093)
              ·
                refine ⟨2056363590909136992738035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5483636242424365313968093 2056363590909136992738035)
                ·
                  refine ⟨3084545386363705489107053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056363590909136992738035 3084545386363705489107053)
                  ·
                    refine ⟨1156704519886389558415145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084545386363705489107053 1156704519886389558415145)
                    ·
                      rfl

theorem cell22_3379011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 3].length) (baseStart_3379011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379011 prefixEnd_3379011 := by exact prefixLift 3379011
  have htrace : WordTrace (prefixWord ++ tailWord_3379011) baseStart_3379011 baseEnd_3379011 := by
    simpa [prefixWord, tailWord_3379011, baseEnd_3379011] using wordTrace_append hprefix tailTrace_3379011
  have hstable : (prefixWord ++ tailWord_3379011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379011).length < 2 ^ (prefixWord ++ tailWord_3379011).sum := by decide
  have hdescent : baseEnd_3379011 < baseStart_3379011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379052 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_3379052 : Nat := 118140960795 + 3379052 * 2 ^ 59
def prefixEnd_3379052 : Nat := 4983230072969 + 3 ^ 40 * 3379052 * 2
def baseEnd_3379052 : Nat := 385572851674759706046673

theorem tailTrace_3379052 : CollatzResearch.WordTrace tailWord_3379052 prefixEnd_3379052 385572851674759706046673 := by
  unfold tailWord_3379052
  simp only [CollatzResearch.WordTrace]
  refine ⟨61622075677139587490869705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82162767569519449987826273 61622075677139587490869705)
  ·
    refine ⟨46216556757854690618152279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61622075677139587490869705 46216556757854690618152279)
    ·
      refine ⟨69324835136782035927228419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46216556757854690618152279 69324835136782035927228419)
      ·
        refine ⟨103987252705173053890842629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69324835136782035927228419 103987252705173053890842629)
        ·
          refine ⟨19497609882219947604532993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103987252705173053890842629 19497609882219947604532993)
          ·
            refine ⟨14623207411664960703399745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19497609882219947604532993 14623207411664960703399745)
            ·
              refine ⟨10967405558748720527549809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14623207411664960703399745 10967405558748720527549809)
              ·
                refine ⟨8225554169061540395662357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10967405558748720527549809 8225554169061540395662357)
                ·
                  refine ⟨385572851674759706046673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8225554169061540395662357 385572851674759706046673)
                  ·
                    rfl

theorem cell22_3379052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_3379052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379052 prefixEnd_3379052 := by exact prefixLift 3379052
  have htrace : WordTrace (prefixWord ++ tailWord_3379052) baseStart_3379052 baseEnd_3379052 := by
    simpa [prefixWord, tailWord_3379052, baseEnd_3379052] using wordTrace_append hprefix tailTrace_3379052
  have hstable : (prefixWord ++ tailWord_3379052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379052).length < 2 ^ (prefixWord ++ tailWord_3379052).sum := by decide
  have hdescent : baseEnd_3379052 < baseStart_3379052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379062 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_3379062 : Nat := 118140960795 + 3379062 * 2 ^ 59
def prefixEnd_3379062 : Nat := 4983230072969 + 3 ^ 40 * 3379062 * 2
def baseEnd_3379062 : Nat := 1156721978228642425389989

theorem tailTrace_3379062 : CollatzResearch.WordTrace tailWord_3379062 prefixEnd_3379062 1156721978228642425389989 := by
  unfold tailWord_3379062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702782255265184168100215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82163010722828631126402293 7702782255265184168100215)
  ·
    refine ⟨11554173382897776252150323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702782255265184168100215 11554173382897776252150323)
    ·
      refine ⟨17331260074346664378225485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11554173382897776252150323 17331260074346664378225485)
      ·
        refine ⟨6499222527879999141834557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17331260074346664378225485 6499222527879999141834557)
        ·
          refine ⟨2437208447954999678187959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6499222527879999141834557 2437208447954999678187959)
          ·
            refine ⟨3655812671932499517281939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437208447954999678187959 3655812671932499517281939)
            ·
              refine ⟨5483719007898749275922909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655812671932499517281939 5483719007898749275922909)
              ·
                refine ⟨2056394627962030978471091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5483719007898749275922909 2056394627962030978471091)
                ·
                  refine ⟨3084591941943046467706637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056394627962030978471091 3084591941943046467706637)
                  ·
                    refine ⟨1156721978228642425389989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084591941943046467706637 1156721978228642425389989)
                    ·
                      rfl

theorem cell22_3379062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_3379062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379062 prefixEnd_3379062 := by exact prefixLift 3379062
  have htrace : WordTrace (prefixWord ++ tailWord_3379062) baseStart_3379062 baseEnd_3379062 := by
    simpa [prefixWord, tailWord_3379062, baseEnd_3379062] using wordTrace_append hprefix tailTrace_3379062
  have hstable : (prefixWord ++ tailWord_3379062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379062).length < 2 ^ (prefixWord ++ tailWord_3379062).sum := by decide
  have hdescent : baseEnd_3379062 < baseStart_3379062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379084 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_3379084 : Nat := 118140960795 + 3379084 * 2 ^ 59
def prefixEnd_3379084 : Nat := 4983230072969 + 3 ^ 40 * 3379084 * 2
def baseEnd_3379084 : Nat := 1156729509278241701339921

theorem tailTrace_3379084 : CollatzResearch.WordTrace tailWord_3379084 prefixEnd_3379084 1156729509278241701339921 := by
  unfold tailWord_3379084
  simp only [CollatzResearch.WordTrace]
  refine ⟨61622659245081622223452153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82163545660108829631269537 61622659245081622223452153)
  ·
    refine ⟨46216994433811216667589115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61622659245081622223452153 46216994433811216667589115)
    ·
      refine ⟨69325491650716825001383673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46216994433811216667589115 69325491650716825001383673)
      ·
        refine ⟨51994118738037618751037755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69325491650716825001383673 51994118738037618751037755)
        ·
          refine ⟨77991178107056428126556633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51994118738037618751037755 77991178107056428126556633)
          ·
            refine ⟨58493383580292321094917475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77991178107056428126556633 58493383580292321094917475)
            ·
              refine ⟨87740075370438481642376213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58493383580292321094917475 87740075370438481642376213)
              ·
                refine ⟨4112816032989303826986385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87740075370438481642376213 4112816032989303826986385)
                ·
                  refine ⟨3084612024741977870239789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112816032989303826986385 3084612024741977870239789)
                  ·
                    refine ⟨1156729509278241701339921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084612024741977870239789 1156729509278241701339921)
                    ·
                      rfl

theorem cell22_3379084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_3379084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379084 prefixEnd_3379084 := by exact prefixLift 3379084
  have htrace : WordTrace (prefixWord ++ tailWord_3379084) baseStart_3379084 baseEnd_3379084 := by
    simpa [prefixWord, tailWord_3379084, baseEnd_3379084] using wordTrace_append hprefix tailTrace_3379084
  have hstable : (prefixWord ++ tailWord_3379084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379084).length < 2 ^ (prefixWord ++ tailWord_3379084).sum := by decide
  have hdescent : baseEnd_3379084 < baseStart_3379084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379101 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3379101 : Nat := 118140960795 + 3379101 * 2 ^ 59
def prefixEnd_3379101 : Nat := 4983230072969 + 3 ^ 40 * 3379101 * 2
def baseEnd_3379101 : Nat := 1156735328725659323664869

theorem tailTrace_3379101 : CollatzResearch.WordTrace tailWord_3379101 prefixEnd_3379101 1156735328725659323664869 := by
  unfold tailWord_3379101
  simp only [CollatzResearch.WordTrace]
  refine ⟨123245938531101656350273157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82163959020734437566848771 123245938531101656350273157)
  ·
    refine ⟨23108613474581560565676217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123245938531101656350273157 23108613474581560565676217)
    ·
      refine ⟨17331460105936170424257163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23108613474581560565676217 17331460105936170424257163)
      ·
        refine ⟨25997190158904255636385745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17331460105936170424257163 25997190158904255636385745)
        ·
          refine ⟨19497892619178191727289309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25997190158904255636385745 19497892619178191727289309)
          ·
            refine ⟨7311709732191821897733491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19497892619178191727289309 7311709732191821897733491)
            ·
              refine ⟨10967564598287732846600237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7311709732191821897733491 10967564598287732846600237)
              ·
                refine ⟨4112836724357899817475089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10967564598287732846600237 4112836724357899817475089)
                ·
                  refine ⟨3084627543268424863106317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112836724357899817475089 3084627543268424863106317)
                  ·
                    refine ⟨1156735328725659323664869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084627543268424863106317 1156735328725659323664869)
                    ·
                      rfl

theorem cell22_3379101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3379101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379101 prefixEnd_3379101 := by exact prefixLift 3379101
  have htrace : WordTrace (prefixWord ++ tailWord_3379101) baseStart_3379101 baseEnd_3379101 := by
    simpa [prefixWord, tailWord_3379101, baseEnd_3379101] using wordTrace_append hprefix tailTrace_3379101
  have hstable : (prefixWord ++ tailWord_3379101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379101).length < 2 ^ (prefixWord ++ tailWord_3379101).sum := by decide
  have hdescent : baseEnd_3379101 < baseStart_3379101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379219 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 1, 5]
def baseStart_3379219 : Nat := 118140960795 + 3379219 * 2 ^ 59
def prefixEnd_3379219 : Nat := 4983230072969 + 3 ^ 40 * 3379219 * 2
def baseEnd_3379219 : Nat := 1156775722537146349214507

theorem tailTrace_3379219 : CollatzResearch.WordTrace tailWord_3379219 prefixEnd_3379219 1156775722537146349214507 := by
  unfold tailWord_3379219
  simp only [CollatzResearch.WordTrace]
  refine ⟨123250242344674162503068711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82166828229782775002045807 123250242344674162503068711)
  ·
    refine ⟨184875363517011243754603067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123250242344674162503068711 184875363517011243754603067)
    ·
      refine ⟨277313045275516865631904601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184875363517011243754603067 277313045275516865631904601)
      ·
        refine ⟨207984783956637649223928451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277313045275516865631904601 207984783956637649223928451)
        ·
          refine ⟨311977175934956473835892677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207984783956637649223928451 311977175934956473835892677)
          ·
            refine ⟨58495720487804338844229877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311977175934956473835892677 58495720487804338844229877)
            ·
              refine ⟨5483973795731656766646551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58495720487804338844229877 5483973795731656766646551)
              ·
                refine ⟨8225960693597485149969827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483973795731656766646551 8225960693597485149969827)
                ·
                  refine ⟨12338941040396227724954741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225960693597485149969827 12338941040396227724954741)
                  ·
                    refine ⟨1156775722537146349214507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12338941040396227724954741 1156775722537146349214507)
                    ·
                      rfl

theorem cell22_3379219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].length) (baseStart_3379219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379219 prefixEnd_3379219 := by exact prefixLift 3379219
  have htrace : WordTrace (prefixWord ++ tailWord_3379219) baseStart_3379219 baseEnd_3379219 := by
    simpa [prefixWord, tailWord_3379219, baseEnd_3379219] using wordTrace_append hprefix tailTrace_3379219
  have hstable : (prefixWord ++ tailWord_3379219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379219).length < 2 ^ (prefixWord ++ tailWord_3379219).sum := by decide
  have hdescent : baseEnd_3379219 < baseStart_3379219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379223 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 1, 4]
def baseStart_3379223 : Nat := 118140960795 + 3379223 * 2 ^ 59
def prefixEnd_3379223 : Nat := 4983230072969 + 3 ^ 40 * 3379223 * 2
def baseEnd_3379223 : Nat := 1156777091818891672114495

theorem tailTrace_3379223 : CollatzResearch.WordTrace tailWord_3379223 prefixEnd_3379223 1156777091818891672114495 := by
  unfold tailWord_3379223
  simp only [CollatzResearch.WordTrace]
  refine ⟨123250388236659671186214323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82166925491106447457476215 123250388236659671186214323)
  ·
    refine ⟨184875582354989506779321485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123250388236659671186214323 184875582354989506779321485)
    ·
      refine ⟨69328343383121065042245557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184875582354989506779321485 69328343383121065042245557)
      ·
        refine ⟨6499532192167599847710521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69328343383121065042245557 6499532192167599847710521)
        ·
          refine ⟨4874649144125699885782891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6499532192167599847710521 4874649144125699885782891)
          ·
            refine ⟨7311973716188549828674337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874649144125699885782891 7311973716188549828674337)
            ·
              refine ⟨5483980287141412371505753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7311973716188549828674337 5483980287141412371505753)
              ·
                refine ⟨4112985215356059278629315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483980287141412371505753 4112985215356059278629315)
                ·
                  refine ⟨6169477823034088917943973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112985215356059278629315 6169477823034088917943973)
                  ·
                    refine ⟨1156777091818891672114495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6169477823034088917943973 1156777091818891672114495)
                    ·
                      rfl

theorem cell22_3379223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_3379223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379223 prefixEnd_3379223 := by exact prefixLift 3379223
  have htrace : WordTrace (prefixWord ++ tailWord_3379223) baseStart_3379223 baseEnd_3379223 := by
    simpa [prefixWord, tailWord_3379223, baseEnd_3379223] using wordTrace_append hprefix tailTrace_3379223
  have hstable : (prefixWord ++ tailWord_3379223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379223).length < 2 ^ (prefixWord ++ tailWord_3379223).sum := by decide
  have hdescent : baseEnd_3379223 < baseStart_3379223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379234 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3379234 : Nat := 118140960795 + 3379234 * 2 ^ 59
def prefixEnd_3379234 : Nat := 4983230072969 + 3 ^ 40 * 3379234 * 2
def baseEnd_3379234 : Nat := 1156780857343691310089461

theorem tailTrace_3379234 : CollatzResearch.WordTrace tailWord_3379234 prefixEnd_3379234 1156780857343691310089461 := by
  unfold tailWord_3379234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30812697359904955016216189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82167192959746546709909837 30812697359904955016216189)
  ·
    refine ⟨11554761509964358131081071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30812697359904955016216189 11554761509964358131081071)
    ·
      refine ⟨17332142264946537196621607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11554761509964358131081071 17332142264946537196621607)
      ·
        refine ⟨25998213397419805794932411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17332142264946537196621607 25998213397419805794932411)
        ·
          refine ⟨38997320096129708692398617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25998213397419805794932411 38997320096129708692398617)
          ·
            refine ⟨29247990072097281519298963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38997320096129708692398617 29247990072097281519298963)
            ·
              refine ⟨43871985108145922278948445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29247990072097281519298963 43871985108145922278948445)
              ·
                refine ⟨16451994415554720854605667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43871985108145922278948445 16451994415554720854605667)
                ·
                  refine ⟨24677991623332081281908501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16451994415554720854605667 24677991623332081281908501)
                  ·
                    refine ⟨1156780857343691310089461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24677991623332081281908501 1156780857343691310089461)
                    ·
                      rfl

theorem cell22_3379234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3379234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379234 prefixEnd_3379234 := by exact prefixLift 3379234
  have htrace : WordTrace (prefixWord ++ tailWord_3379234) baseStart_3379234 baseEnd_3379234 := by
    simpa [prefixWord, tailWord_3379234, baseEnd_3379234] using wordTrace_append hprefix tailTrace_3379234
  have hstable : (prefixWord ++ tailWord_3379234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379234).length < 2 ^ (prefixWord ++ tailWord_3379234).sum := by decide
  have hdescent : baseEnd_3379234 < baseStart_3379234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379249 : List Nat := [1, 2, 2, 3, 1, 5, 8]
def baseStart_3379249 : Nat := 118140960795 + 3379249 * 2 ^ 59
def prefixEnd_3379249 : Nat := 4983230072969 + 3 ^ 40 * 3379249 * 2
def baseEnd_3379249 : Nat := 42843925635193935961645

theorem tailTrace_3379249 : CollatzResearch.WordTrace tailWord_3379249 prefixEnd_3379249 42843925635193935961645 := by
  unfold tailWord_3379249
  simp only [CollatzResearch.WordTrace]
  refine ⟨123251336534565477626660801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82167557689710318417773867 123251336534565477626660801)
  ·
    refine ⟨92438502400924108219995601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123251336534565477626660801 92438502400924108219995601)
    ·
      refine ⟨69328876800693081164996701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92438502400924108219995601 69328876800693081164996701)
      ·
        refine ⟨25998328800259905436873763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69328876800693081164996701 25998328800259905436873763)
        ·
          refine ⟨38997493200389858155310645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25998328800259905436873763 38997493200389858155310645)
          ·
            refine ⟨3656014987536549202060373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38997493200389858155310645 3656014987536549202060373)
            ·
              refine ⟨42843925635193935961645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3656014987536549202060373 42843925635193935961645)
              ·
                rfl

theorem cell22_3379249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 8].length) (baseStart_3379249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379249 prefixEnd_3379249 := by exact prefixLift 3379249
  have htrace : WordTrace (prefixWord ++ tailWord_3379249) baseStart_3379249 baseEnd_3379249 := by
    simpa [prefixWord, tailWord_3379249, baseEnd_3379249] using wordTrace_append hprefix tailTrace_3379249
  have hstable : (prefixWord ++ tailWord_3379249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379249).length < 2 ^ (prefixWord ++ tailWord_3379249).sum := by decide
  have hdescent : baseEnd_3379249 < baseStart_3379249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379270 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3379270 : Nat := 118140960795 + 3379270 * 2 ^ 59
def prefixEnd_3379270 : Nat := 4983230072969 + 3 ^ 40 * 3379270 * 2
def baseEnd_3379270 : Nat := 1156793180879399216189351

theorem tailTrace_3379270 : CollatzResearch.WordTrace tailWord_3379270 prefixEnd_3379270 1156793180879399216189351 := by
  unfold tailWord_3379270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851628202109043694161727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82168068311659598808783509 3851628202109043694161727)
  ·
    refine ⟨5777442303163565541242591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3851628202109043694161727 5777442303163565541242591)
    ·
      refine ⟨8666163454745348311863887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777442303163565541242591 8666163454745348311863887)
      ·
        refine ⟨12999245182118022467795831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666163454745348311863887 12999245182118022467795831)
        ·
          refine ⟨19498867773177033701693747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12999245182118022467795831 19498867773177033701693747)
          ·
            refine ⟨29248301659765550552540621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19498867773177033701693747 29248301659765550552540621)
            ·
              refine ⟨10968113122412081457202733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29248301659765550552540621 10968113122412081457202733)
              ·
                refine ⟨4113042420904530546451025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10968113122412081457202733 4113042420904530546451025)
                ·
                  refine ⟨3084781815678397909838269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113042420904530546451025 3084781815678397909838269)
                  ·
                    refine ⟨1156793180879399216189351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084781815678397909838269 1156793180879399216189351)
                    ·
                      rfl

theorem cell22_3379270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3379270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379270 prefixEnd_3379270 := by exact prefixLift 3379270
  have htrace : WordTrace (prefixWord ++ tailWord_3379270) baseStart_3379270 baseEnd_3379270 := by
    simpa [prefixWord, tailWord_3379270, baseEnd_3379270] using wordTrace_append hprefix tailTrace_3379270
  have hstable : (prefixWord ++ tailWord_3379270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379270).length < 2 ^ (prefixWord ++ tailWord_3379270).sum := by decide
  have hdescent : baseEnd_3379270 < baseStart_3379270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379311 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 5]
def baseStart_3379311 : Nat := 118140960795 + 3379311 * 2 ^ 59
def prefixEnd_3379311 : Nat := 4983230072969 + 3 ^ 40 * 3379311 * 2
def baseEnd_3379311 : Nat := 385602405339096258638075

theorem tailTrace_3379311 : CollatzResearch.WordTrace tailWord_3379311 prefixEnd_3379311 385602405339096258638075 := by
  unfold tailWord_3379311
  simp only [CollatzResearch.WordTrace]
  refine ⟨123253597860340862215417787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82169065240227241476945191 123253597860340862215417787)
  ·
    refine ⟨184880396790511293323126681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123253597860340862215417787 184880396790511293323126681)
    ·
      refine ⟨138660297592883469992345011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184880396790511293323126681 138660297592883469992345011)
      ·
        refine ⟨207990446389325204988517517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138660297592883469992345011 207990446389325204988517517)
        ·
          refine ⟨77996417395996951870694069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207990446389325204988517517 77996417395996951870694069)
          ·
            refine ⟨7312164130874714237877569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77996417395996951870694069 7312164130874714237877569)
            ·
              refine ⟨5484123098156035678408177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7312164130874714237877569 5484123098156035678408177)
              ·
                refine ⟨4113092323617026758806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5484123098156035678408177 4113092323617026758806133)
                ·
                  refine ⟨385602405339096258638075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4113092323617026758806133 385602405339096258638075)
                  ·
                    rfl

theorem cell22_3379311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 5].length) (baseStart_3379311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379311 prefixEnd_3379311 := by exact prefixLift 3379311
  have htrace : WordTrace (prefixWord ++ tailWord_3379311) baseStart_3379311 baseEnd_3379311 := by
    simpa [prefixWord, tailWord_3379311, baseEnd_3379311] using wordTrace_append hprefix tailTrace_3379311
  have hstable : (prefixWord ++ tailWord_3379311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379311).length < 2 ^ (prefixWord ++ tailWord_3379311).sum := by decide
  have hdescent : baseEnd_3379311 < baseStart_3379311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379373 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 6]
def baseStart_3379373 : Nat := 118140960795 + 3379373 * 2 ^ 59
def prefixEnd_3379373 : Nat := 4983230072969 + 3 ^ 40 * 3379373 * 2
def baseEnd_3379373 : Nat := 385609479961447093621345

theorem tailTrace_3379373 : CollatzResearch.WordTrace tailWord_3379373 prefixEnd_3379373 385609479961447093621345 := by
  unfold tailWord_3379373
  simp only [CollatzResearch.WordTrace]
  refine ⟨123255859186116246804174773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82170572790744164536116515 123255859186116246804174773)
  ·
    refine ⟨11555236798698398137891385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123255859186116246804174773 11555236798698398137891385)
    ·
      refine ⟨8666427599023798603418539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11555236798698398137891385 8666427599023798603418539)
      ·
        refine ⟨12999641398535697905127809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666427599023798603418539 12999641398535697905127809)
        ·
          refine ⟨9749731048901773428845857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12999641398535697905127809 9749731048901773428845857)
          ·
            refine ⟨7312298286676330071634393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9749731048901773428845857 7312298286676330071634393)
            ·
              refine ⟨5484223715007247553725795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7312298286676330071634393 5484223715007247553725795)
              ·
                refine ⟨8226335572510871330588693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484223715007247553725795 8226335572510871330588693)
                ·
                  refine ⟨385609479961447093621345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8226335572510871330588693 385609479961447093621345)
                  ·
                    rfl

theorem cell22_3379373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_3379373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379373 prefixEnd_3379373 := by exact prefixLift 3379373
  have htrace : WordTrace (prefixWord ++ tailWord_3379373) baseStart_3379373 baseEnd_3379373 := by
    simpa [prefixWord, tailWord_3379373, baseEnd_3379373] using wordTrace_append hprefix tailTrace_3379373
  have hstable : (prefixWord ++ tailWord_3379373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379373).length < 2 ^ (prefixWord ++ tailWord_3379373).sum := by decide
  have hdescent : baseEnd_3379373 < baseStart_3379373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379384 : List Nat := [2, 1, 2, 1, 2, 1, 4, 9]
def baseStart_3379384 : Nat := 118140960795 + 3379384 * 2 ^ 59
def prefixEnd_3379384 : Nat := 4983230072969 + 3 ^ 40 * 3379384 * 2
def baseEnd_3379384 : Nat := 128536911712126768759889

theorem tailTrace_3379384 : CollatzResearch.WordTrace tailWord_3379384 prefixEnd_3379384 128536911712126768759889 := by
  unfold tailWord_3379384
  simp only [CollatzResearch.WordTrace]
  refine ⟨61628130194538197841412603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82170840259384263788550137 61628130194538197841412603)
  ·
    refine ⟨92442195291807296762118905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61628130194538197841412603 92442195291807296762118905)
    ·
      refine ⟨69331646468855472571589179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92442195291807296762118905 69331646468855472571589179)
      ·
        refine ⟨103997469703283208857383769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69331646468855472571589179 103997469703283208857383769)
        ·
          refine ⟨77998102277462406643037827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103997469703283208857383769 77998102277462406643037827)
          ·
            refine ⟨116997153416193609964556741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77998102277462406643037827 116997153416193609964556741)
            ·
              refine ⟨21936966265536301868354389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116997153416193609964556741 21936966265536301868354389)
              ·
                refine ⟨128536911712126768759889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21936966265536301868354389 128536911712126768759889)
                ·
                  rfl

theorem cell22_3379384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_3379384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379384 prefixEnd_3379384 := by exact prefixLift 3379384
  have htrace : WordTrace (prefixWord ++ tailWord_3379384) baseStart_3379384 baseEnd_3379384 := by
    simpa [prefixWord, tailWord_3379384, baseEnd_3379384] using wordTrace_append hprefix tailTrace_3379384
  have hstable : (prefixWord ++ tailWord_3379384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379384).length < 2 ^ (prefixWord ++ tailWord_3379384).sum := by decide
  have hdescent : baseEnd_3379384 < baseStart_3379384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379491 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 6]
def baseStart_3379491 : Nat := 118140960795 + 3379491 * 2 ^ 59
def prefixEnd_3379491 : Nat := 4983230072969 + 3 ^ 40 * 3379491 * 2
def baseEnd_3379491 : Nat := 385622944565276102137891

theorem tailTrace_3379491 : CollatzResearch.WordTrace tailWord_3379491 prefixEnd_3379491 385622944565276102137891 := by
  unfold tailWord_3379491
  simp only [CollatzResearch.WordTrace]
  refine ⟨123260162999688752956970327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82173441999792501971313551 123260162999688752956970327)
  ·
    refine ⟨184890244499533129435455491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123260162999688752956970327 184890244499533129435455491)
    ·
      refine ⟨277335366749299694153183237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184890244499533129435455491 277335366749299694153183237)
      ·
        refine ⟨52000381265493692653721857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277335366749299694153183237 52000381265493692653721857)
        ·
          refine ⟨39000285949120269490291393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52000381265493692653721857 39000285949120269490291393)
          ·
            refine ⟨29250214461840202117718545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39000285949120269490291393 29250214461840202117718545)
            ·
              refine ⟨21937660846380151588288909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29250214461840202117718545 21937660846380151588288909)
              ·
                refine ⟨8226622817392556845608341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21937660846380151588288909 8226622817392556845608341)
                ·
                  refine ⟨385622944565276102137891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8226622817392556845608341 385622944565276102137891)
                  ·
                    rfl

theorem cell22_3379491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_3379491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379491 prefixEnd_3379491 := by exact prefixLift 3379491
  have htrace : WordTrace (prefixWord ++ tailWord_3379491) baseStart_3379491 baseEnd_3379491 := by
    simpa [prefixWord, tailWord_3379491, baseEnd_3379491] using wordTrace_append hprefix tailTrace_3379491
  have hstable : (prefixWord ++ tailWord_3379491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379491).length < 2 ^ (prefixWord ++ tailWord_3379491).sum := by decide
  have hdescent : baseEnd_3379491 < baseStart_3379491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379508 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3379508 : Nat := 118140960795 + 3379508 * 2 ^ 59
def prefixEnd_3379508 : Nat := 4983230072969 + 3 ^ 40 * 3379508 * 2
def baseEnd_3379508 : Nat := 385624884381081976246207

theorem tailTrace_3379508 : CollatzResearch.WordTrace tailWord_3379508 prefixEnd_3379508 385624884381081976246207 := by
  unfold tailWord_3379508
  simp only [CollatzResearch.WordTrace]
  refine ⟨61630391520313582430169589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82173855360418109906892785 61630391520313582430169589)
  ·
    refine ⟨5777849205029398352828399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61630391520313582430169589 5777849205029398352828399)
    ·
      refine ⟨8666773807544097529242599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777849205029398352828399 8666773807544097529242599)
      ·
        refine ⟨13000160711316146293863899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666773807544097529242599 13000160711316146293863899)
        ·
          refine ⟨19500241066974219440795849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13000160711316146293863899 19500241066974219440795849)
          ·
            refine ⟨14625180800230664580596887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19500241066974219440795849 14625180800230664580596887)
            ·
              refine ⟨21937771200345996870895331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14625180800230664580596887 21937771200345996870895331)
              ·
                refine ⟨32906656800518995306342997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21937771200345996870895331 32906656800518995306342997)
                ·
                  refine ⟨385624884381081976246207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32906656800518995306342997 385624884381081976246207)
                  ·
                    rfl

theorem cell22_3379508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3379508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379508 prefixEnd_3379508 := by exact prefixLift 3379508
  have htrace : WordTrace (prefixWord ++ tailWord_3379508) baseStart_3379508 baseEnd_3379508 := by
    simpa [prefixWord, tailWord_3379508, baseEnd_3379508] using wordTrace_append hprefix tailTrace_3379508
  have hstable : (prefixWord ++ tailWord_3379508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379508).length < 2 ^ (prefixWord ++ tailWord_3379508).sum := by decide
  have hdescent : baseEnd_3379508 < baseStart_3379508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379536 : List Nat := [2, 1, 1, 1, 1, 7, 9]
def baseStart_3379536 : Nat := 118140960795 + 3379536 * 2 ^ 59
def prefixEnd_3379536 : Nat := 4983230072969 + 3 ^ 40 * 3379536 * 2
def baseEnd_3379536 : Nat := 42847564374646784779205

theorem tailTrace_3379536 : CollatzResearch.WordTrace tailWord_3379536 prefixEnd_3379536 42847564374646784779205 := by
  unfold tailWord_3379536
  simp only [CollatzResearch.WordTrace]
  refine ⟨61630902142262862821179231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82174536189683817094905641 61630902142262862821179231)
  ·
    refine ⟨92446353213394294231768847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61630902142262862821179231 92446353213394294231768847)
    ·
      refine ⟨138669529820091441347653271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92446353213394294231768847 138669529820091441347653271)
      ·
        refine ⟨208004294730137162021479907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138669529820091441347653271 208004294730137162021479907)
        ·
          refine ⟨312006442095205743032219861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208004294730137162021479907 312006442095205743032219861)
          ·
            refine ⟨7312650986606384602317653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312006442095205743032219861 7312650986606384602317653)
            ·
              refine ⟨42847564374646784779205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7312650986606384602317653 42847564374646784779205)
              ·
                rfl

theorem cell22_3379536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 9].length) (baseStart_3379536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379536 prefixEnd_3379536 := by exact prefixLift 3379536
  have htrace : WordTrace (prefixWord ++ tailWord_3379536) baseStart_3379536 baseEnd_3379536 := by
    simpa [prefixWord, tailWord_3379536, baseEnd_3379536] using wordTrace_append hprefix tailTrace_3379536
  have hstable : (prefixWord ++ tailWord_3379536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379536).length < 2 ^ (prefixWord ++ tailWord_3379536).sum := by decide
  have hdescent : baseEnd_3379536 < baseStart_3379536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379538 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3379538 : Nat := 118140960795 + 3379538 * 2 ^ 59
def prefixEnd_3379538 : Nat := 4983230072969 + 3 ^ 40 * 3379538 * 2
def baseEnd_3379538 : Nat := 1156884922756335850488529

theorem tailTrace_3379538 : CollatzResearch.WordTrace tailWord_3379538 prefixEnd_3379538 1156884922756335850488529 := by
  unfold tailWord_3379538
  simp only [CollatzResearch.WordTrace]
  refine ⟨30815469307629619995982817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82174584820345653322620845 30815469307629619995982817)
  ·
    refine ⟨23111601980722214996987113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30815469307629619995982817 23111601980722214996987113)
    ·
      refine ⟨17333701485541661247740335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23111601980722214996987113 17333701485541661247740335)
      ·
        refine ⟨26000552228312491871610503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17333701485541661247740335 26000552228312491871610503)
        ·
          refine ⟨39000828342468737807415755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26000552228312491871610503 39000828342468737807415755)
          ·
            refine ⟨58501242513703106711123633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39000828342468737807415755 58501242513703106711123633)
            ·
              refine ⟨43875931885277330033342725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58501242513703106711123633 43875931885277330033342725)
              ·
                refine ⟨8226737228489499381251761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43875931885277330033342725 8226737228489499381251761)
                ·
                  refine ⟨6170052921367124535938821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8226737228489499381251761 6170052921367124535938821)
                  ·
                    refine ⟨1156884922756335850488529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6170052921367124535938821 1156884922756335850488529)
                    ·
                      rfl

theorem cell22_3379538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3379538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379538 prefixEnd_3379538 := by exact prefixLift 3379538
  have htrace : WordTrace (prefixWord ++ tailWord_3379538) baseStart_3379538 baseEnd_3379538 := by
    simpa [prefixWord, tailWord_3379538, baseEnd_3379538] using wordTrace_append hprefix tailTrace_3379538
  have hstable : (prefixWord ++ tailWord_3379538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379538).length < 2 ^ (prefixWord ++ tailWord_3379538).sum := by decide
  have hdescent : baseEnd_3379538 < baseStart_3379538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379540 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3379540 : Nat := 118140960795 + 3379540 * 2 ^ 59
def prefixEnd_3379540 : Nat := 4983230072969 + 3 ^ 40 * 3379540 * 2
def baseEnd_3379540 : Nat := 1156885607397208511938523

theorem tailTrace_3379540 : CollatzResearch.WordTrace tailWord_3379540 prefixEnd_3379540 1156885607397208511938523 := by
  unfold tailWord_3379540
  simp only [CollatzResearch.WordTrace]
  refine ⟨61630975088255617162752037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82174633451007489550336049 61630975088255617162752037)
  ·
    refine ⟨11555807829047928218016007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61630975088255617162752037 11555807829047928218016007)
    ·
      refine ⟨17333711743571892327024011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555807829047928218016007 17333711743571892327024011)
      ·
        refine ⟨26000567615357838490536017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17333711743571892327024011 26000567615357838490536017)
        ·
          refine ⟨19500425711518378867902013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26000567615357838490536017 19500425711518378867902013)
          ·
            refine ⟨7312659641819392075463255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19500425711518378867902013 7312659641819392075463255)
            ·
              refine ⟨10968989462729088113194883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312659641819392075463255 10968989462729088113194883)
              ·
                refine ⟨16453484194093632169792325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10968989462729088113194883 16453484194093632169792325)
                ·
                  refine ⟨3085028286392556031836061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16453484194093632169792325 3085028286392556031836061)
                  ·
                    refine ⟨1156885607397208511938523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085028286392556031836061 1156885607397208511938523)
                    ·
                      rfl

theorem cell22_3379540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3379540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379540 prefixEnd_3379540 := by exact prefixLift 3379540
  have htrace : WordTrace (prefixWord ++ tailWord_3379540) baseStart_3379540 baseEnd_3379540 := by
    simpa [prefixWord, tailWord_3379540, baseEnd_3379540] using wordTrace_append hprefix tailTrace_3379540
  have hstable : (prefixWord ++ tailWord_3379540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379540).length < 2 ^ (prefixWord ++ tailWord_3379540).sum := by decide
  have hdescent : baseEnd_3379540 < baseStart_3379540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379557 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_3379557 : Nat := 118140960795 + 3379557 * 2 ^ 59
def prefixEnd_3379557 : Nat := 4983230072969 + 3 ^ 40 * 3379557 * 2
def baseEnd_3379557 : Nat := 1156891426844626134263471

theorem tailTrace_3379557 : CollatzResearch.WordTrace tailWord_3379557 prefixEnd_3379557 1156891426844626134263471 := by
  unfold tailWord_3379557
  simp only [CollatzResearch.WordTrace]
  refine ⟨123262570217449646228872925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82175046811633097485915283 123262570217449646228872925)
  ·
    refine ⟨46223463831543617335827347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123262570217449646228872925 46223463831543617335827347)
    ·
      refine ⟨69335195747315426003741021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46223463831543617335827347 69335195747315426003741021)
      ·
        refine ⟨26000698405243284751402883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69335195747315426003741021 26000698405243284751402883)
        ·
          refine ⟨39001047607864927127104325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26000698405243284751402883 39001047607864927127104325)
          ·
            refine ⟨7312696426474673836332061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39001047607864927127104325 7312696426474673836332061)
            ·
              refine ⟨2742261159928002688624523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7312696426474673836332061 2742261159928002688624523)
              ·
                refine ⟨4113391739892004032936785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742261159928002688624523 4113391739892004032936785)
                ·
                  refine ⟨3085043804919003024702589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113391739892004032936785 3085043804919003024702589)
                  ·
                    refine ⟨1156891426844626134263471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085043804919003024702589 1156891426844626134263471)
                    ·
                      rfl

theorem cell22_3379557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_3379557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379557 prefixEnd_3379557 := by exact prefixLift 3379557
  have htrace : WordTrace (prefixWord ++ tailWord_3379557) baseStart_3379557 baseEnd_3379557 := by
    simpa [prefixWord, tailWord_3379557, baseEnd_3379557] using wordTrace_append hprefix tailTrace_3379557
  have hstable : (prefixWord ++ tailWord_3379557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379557).length < 2 ^ (prefixWord ++ tailWord_3379557).sum := by decide
  have hdescent : baseEnd_3379557 < baseStart_3379557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379570 : List Nat := [3, 2, 1, 2, 1, 5, 2, 6]
def baseStart_3379570 : Nat := 118140960795 + 3379570 * 2 ^ 59
def prefixEnd_3379570 : Nat := 4983230072969 + 3 ^ 40 * 3379570 * 2
def baseEnd_3379570 : Nat := 128543986334477603743159

theorem tailTrace_3379570 : CollatzResearch.WordTrace tailWord_3379570 prefixEnd_3379570 128543986334477603743159 := by
  unfold tailWord_3379570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30815761091600637362274041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82175362910935032966064109 30815761091600637362274041)
  ·
    refine ⟨23111820818700478021705531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30815761091600637362274041 23111820818700478021705531)
    ·
      refine ⟨34667731228050717032558297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23111820818700478021705531 34667731228050717032558297)
      ·
        refine ⟨26000798421038037774418723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34667731228050717032558297 26000798421038037774418723)
        ·
          refine ⟨39001197631557056661628085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26000798421038037774418723 39001197631557056661628085)
          ·
            refine ⟨3656362277958474062027633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39001197631557056661628085 3656362277958474062027633)
            ·
              refine ⟨2742271708468855546520725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3656362277958474062027633 2742271708468855546520725)
              ·
                refine ⟨128543986334477603743159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2742271708468855546520725 128543986334477603743159)
                ·
                  rfl

theorem cell22_3379570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_3379570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379570 prefixEnd_3379570 := by exact prefixLift 3379570
  have htrace : WordTrace (prefixWord ++ tailWord_3379570) baseStart_3379570 baseEnd_3379570 := by
    simpa [prefixWord, tailWord_3379570, baseEnd_3379570] using wordTrace_append hprefix tailTrace_3379570
  have hstable : (prefixWord ++ tailWord_3379570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379570).length < 2 ^ (prefixWord ++ tailWord_3379570).sum := by decide
  have hdescent : baseEnd_3379570 < baseStart_3379570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379658 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3379658 : Nat := 118140960795 + 3379658 * 2 ^ 59
def prefixEnd_3379658 : Nat := 4983230072969 + 3 ^ 40 * 3379658 * 2
def baseEnd_3379658 : Nat := 1156926001208695537488161

theorem tailTrace_3379658 : CollatzResearch.WordTrace tailWord_3379658 prefixEnd_3379658 1156926001208695537488161 := by
  unfold tailWord_3379658
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816563497520935119574907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82177502660055826985533085 30816563497520935119574907)
  ·
    refine ⟨46224845246281402679362361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30816563497520935119574907 46224845246281402679362361)
    ·
      refine ⟨34668633934711052009521771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46224845246281402679362361 34668633934711052009521771)
      ·
        refine ⟨52002950902066578014282657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34668633934711052009521771 52002950902066578014282657)
        ·
          refine ⟨39002213176549933510711993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52002950902066578014282657 39002213176549933510711993)
          ·
            refine ⟨29251659882412450133033995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39002213176549933510711993 29251659882412450133033995)
            ·
              refine ⟨43877489823618675199550993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29251659882412450133033995 43877489823618675199550993)
              ·
                refine ⟨32908117367714006399663245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43877489823618675199550993 32908117367714006399663245)
                ·
                  refine ⟨12340544012892752399873717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32908117367714006399663245 12340544012892752399873717)
                  ·
                    refine ⟨1156926001208695537488161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12340544012892752399873717 1156926001208695537488161)
                    ·
                      rfl

theorem cell22_3379658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3379658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379658 prefixEnd_3379658 := by exact prefixLift 3379658
  have htrace : WordTrace (prefixWord ++ tailWord_3379658) baseStart_3379658 baseEnd_3379658 := by
    simpa [prefixWord, tailWord_3379658, baseEnd_3379658] using wordTrace_append hprefix tailTrace_3379658
  have hstable : (prefixWord ++ tailWord_3379658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379658).length < 2 ^ (prefixWord ++ tailWord_3379658).sum := by decide
  have hdescent : baseEnd_3379658 < baseStart_3379658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379673 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_3379673 : Nat := 118140960795 + 3379673 * 2 ^ 59
def prefixEnd_3379673 : Nat := 4983230072969 + 3 ^ 40 * 3379673 * 2
def baseEnd_3379673 : Nat := 1156931136015240498363115

theorem tailTrace_3379673 : CollatzResearch.WordTrace tailWord_3379673 prefixEnd_3379673 1156931136015240498363115 := by
  unfold tailWord_3379673
  simp only [CollatzResearch.WordTrace]
  refine ⟨123266801085029398040095673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82177867390019598693397115 123266801085029398040095673)
  ·
    refine ⟨92450100813772048530071755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123266801085029398040095673 92450100813772048530071755)
    ·
      refine ⟨138675151220658072795107633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92450100813772048530071755 138675151220658072795107633)
      ·
        refine ⟨104006363415493554596330725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138675151220658072795107633 104006363415493554596330725)
        ·
          refine ⟨19501193140405041486812011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104006363415493554596330725 19501193140405041486812011)
          ·
            refine ⟨29251789710607562230218017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19501193140405041486812011 29251789710607562230218017)
            ·
              refine ⟨21938842282955671672663513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29251789710607562230218017 21938842282955671672663513)
              ·
                refine ⟨16454131712216753754497635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21938842282955671672663513 16454131712216753754497635)
                ·
                  refine ⟨24681197568325130631746453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16454131712216753754497635 24681197568325130631746453)
                  ·
                    refine ⟨1156931136015240498363115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24681197568325130631746453 1156931136015240498363115)
                    ·
                      rfl

theorem cell22_3379673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_3379673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379673 prefixEnd_3379673 := by exact prefixLift 3379673
  have htrace : WordTrace (prefixWord ++ tailWord_3379673) baseStart_3379673 baseEnd_3379673 := by
    simpa [prefixWord, tailWord_3379673, baseEnd_3379673] using wordTrace_append hprefix tailTrace_3379673
  have hstable : (prefixWord ++ tailWord_3379673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379673).length < 2 ^ (prefixWord ++ tailWord_3379673).sum := by decide
  have hdescent : baseEnd_3379673 < baseStart_3379673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379690 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3379690 : Nat := 118140960795 + 3379690 * 2 ^ 59
def prefixEnd_3379690 : Nat := 4983230072969 + 3 ^ 40 * 3379690 * 2
def baseEnd_3379690 : Nat := 1156936955462658120688063

theorem tailTrace_3379690 : CollatzResearch.WordTrace tailWord_3379690 prefixEnd_3379690 1156936955462658120688063 := by
  unfold tailWord_3379690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816855281491952485866131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82178280750645206628976349 30816855281491952485866131)
  ·
    refine ⟨46225282922237928728799197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30816855281491952485866131 46225282922237928728799197)
    ·
      refine ⟨17334481095839223273299699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46225282922237928728799197 17334481095839223273299699)
      ·
        refine ⟨26001721643758834909949549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17334481095839223273299699 26001721643758834909949549)
        ·
          refine ⟨9750645616409563091231081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26001721643758834909949549 9750645616409563091231081)
          ·
            refine ⟨7312984212307172318423311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9750645616409563091231081 7312984212307172318423311)
            ·
              refine ⟨10969476318460758477634967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312984212307172318423311 10969476318460758477634967)
              ·
                refine ⟨16454214477691137716452451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10969476318460758477634967 16454214477691137716452451)
                ·
                  refine ⟨24681321716536706574678677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16454214477691137716452451 24681321716536706574678677)
                  ·
                    refine ⟨1156936955462658120688063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24681321716536706574678677 1156936955462658120688063)
                    ·
                      rfl

theorem cell22_3379690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3379690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379690 prefixEnd_3379690 := by exact prefixLift 3379690
  have htrace : WordTrace (prefixWord ++ tailWord_3379690) baseStart_3379690 baseEnd_3379690 := by
    simpa [prefixWord, tailWord_3379690, baseEnd_3379690] using wordTrace_append hprefix tailTrace_3379690
  have hstable : (prefixWord ++ tailWord_3379690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379690).length < 2 ^ (prefixWord ++ tailWord_3379690).sum := by decide
  have hdescent : baseEnd_3379690 < baseStart_3379690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379797 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3379797 : Nat := 118140960795 + 3379797 * 2 ^ 59
def prefixEnd_3379797 : Nat := 4983230072969 + 3 ^ 40 * 3379797 * 2
def baseEnd_3379797 : Nat := 1156973583749345508262735

theorem tailTrace_3379797 : CollatzResearch.WordTrace tailWord_3379797 prefixEnd_3379797 1156973583749345508262735 := by
  unfold tailWord_3379797
  simp only [CollatzResearch.WordTrace]
  refine ⟨123271323736580167217609645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82180882491053444811739763 123271323736580167217609645)
  ·
    refine ⟨46226746401217562706603617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123271323736580167217609645 46226746401217562706603617)
    ·
      refine ⟨34670059800913172029952713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46226746401217562706603617 34670059800913172029952713)
      ·
        refine ⟨26002544850684879022464535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34670059800913172029952713 26002544850684879022464535)
        ·
          refine ⟨39003817276027318533696803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26002544850684879022464535 39003817276027318533696803)
          ·
            refine ⟨58505725914040977800545205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39003817276027318533696803 58505725914040977800545205)
            ·
              refine ⟨5484911804441341668801113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58505725914040977800545205 5484911804441341668801113)
              ·
                refine ⟨4113683853331006251600835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5484911804441341668801113 4113683853331006251600835)
                ·
                  refine ⟨6170525779996509377401253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113683853331006251600835 6170525779996509377401253)
                  ·
                    refine ⟨1156973583749345508262735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6170525779996509377401253 1156973583749345508262735)
                    ·
                      rfl

theorem cell22_3379797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3379797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379797 prefixEnd_3379797 := by exact prefixLift 3379797
  have htrace : WordTrace (prefixWord ++ tailWord_3379797) baseStart_3379797 baseEnd_3379797 := by
    simpa [prefixWord, tailWord_3379797, baseEnd_3379797] using wordTrace_append hprefix tailTrace_3379797
  have hstable : (prefixWord ++ tailWord_3379797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379797).length < 2 ^ (prefixWord ++ tailWord_3379797).sum := by decide
  have hdescent : baseEnd_3379797 < baseStart_3379797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379812 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 4]
def baseStart_3379812 : Nat := 118140960795 + 3379812 * 2 ^ 59
def prefixEnd_3379812 : Nat := 4983230072969 + 3 ^ 40 * 3379812 * 2
def baseEnd_3379812 : Nat := 385659572851963489712563

theorem tailTrace_3379812 : CollatzResearch.WordTrace tailWord_3379812 prefixEnd_3379812 385659572851963489712563 := by
  unfold tailWord_3379812
  simp only [CollatzResearch.WordTrace]
  refine ⟨61635935415762912389702845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82181247221017216519603793 61635935415762912389702845)
  ·
    refine ⟨23113475780911092146138567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61635935415762912389702845 23113475780911092146138567)
    ·
      refine ⟨34670213671366638219207851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23113475780911092146138567 34670213671366638219207851)
      ·
        refine ⟨52005320507049957328811777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34670213671366638219207851 52005320507049957328811777)
        ·
          refine ⟨39003990380287467996608833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52005320507049957328811777 39003990380287467996608833)
          ·
            refine ⟨29252992785215600997456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39003990380287467996608833 29252992785215600997456625)
            ·
              refine ⟨21939744588911700748092469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29252992785215600997456625 21939744588911700748092469)
              ·
                refine ⟨2056851055210471945133669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21939744588911700748092469 2056851055210471945133669)
                ·
                  refine ⟨385659572851963489712563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056851055210471945133669 385659572851963489712563)
                  ·
                    rfl

theorem cell22_3379812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_3379812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379812 prefixEnd_3379812 := by exact prefixLift 3379812
  have htrace : WordTrace (prefixWord ++ tailWord_3379812) baseStart_3379812 baseEnd_3379812 := by
    simpa [prefixWord, tailWord_3379812, baseEnd_3379812] using wordTrace_append hprefix tailTrace_3379812
  have hstable : (prefixWord ++ tailWord_3379812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379812).length < 2 ^ (prefixWord ++ tailWord_3379812).sum := by decide
  have hdescent : baseEnd_3379812 < baseStart_3379812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379840 : List Nat := [2, 1, 1, 2, 1, 5, 3, 7]
def baseStart_3379840 : Nat := 118140960795 + 3379840 * 2 ^ 59
def prefixEnd_3379840 : Nat := 4983230072969 + 3 ^ 40 * 3379840 * 2
def baseEnd_3379840 : Nat := 128554255947567525493067

theorem tailTrace_3379840 : CollatzResearch.WordTrace tailWord_3379840 prefixEnd_3379840 128554255947567525493067 := by
  unfold tailWord_3379840
  simp only [CollatzResearch.WordTrace]
  refine ⟨61636446037712192780712487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82181928050282923707616649 61636446037712192780712487)
  ·
    refine ⟨92454669056568289171068731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61636446037712192780712487 92454669056568289171068731)
    ·
      refine ⟨138682003584852433756603097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92454669056568289171068731 138682003584852433756603097)
      ·
        refine ⟨104011502688639325317452323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138682003584852433756603097 104011502688639325317452323)
        ·
          refine ⟨156017254032958987976178485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104011502688639325317452323 156017254032958987976178485)
          ·
            refine ⟨14626617565589905122766733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156017254032958987976178485 14626617565589905122766733)
            ·
              refine ⟨5484981587096214421037525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14626617565589905122766733 5484981587096214421037525)
              ·
                refine ⟨128554255947567525493067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5484981587096214421037525 128554255947567525493067)
                ·
                  rfl

theorem cell22_3379840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_3379840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379840 prefixEnd_3379840 := by exact prefixLift 3379840
  have htrace : WordTrace (prefixWord ++ tailWord_3379840) baseStart_3379840 baseEnd_3379840 := by
    simpa [prefixWord, tailWord_3379840, baseEnd_3379840] using wordTrace_append hprefix tailTrace_3379840
  have hstable : (prefixWord ++ tailWord_3379840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379840).length < 2 ^ (prefixWord ++ tailWord_3379840).sum := by decide
  have hdescent : baseEnd_3379840 < baseStart_3379840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379844 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_3379844 : Nat := 118140960795 + 3379844 * 2 ^ 59
def prefixEnd_3379844 : Nat := 4983230072969 + 3 ^ 40 * 3379844 * 2
def baseEnd_3379844 : Nat := 1156989672809853052337591

theorem tailTrace_3379844 : CollatzResearch.WordTrace tailWord_3379844 prefixEnd_3379844 1156989672809853052337591 := by
  unfold tailWord_3379844
  simp only [CollatzResearch.WordTrace]
  refine ⟨61636518983704947122285293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82182025311606596163047057 61636518983704947122285293)
  ·
    refine ⟨23113694618889355170856985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61636518983704947122285293 23113694618889355170856985)
    ·
      refine ⟨17335270964167016378142739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23113694618889355170856985 17335270964167016378142739)
      ·
        refine ⟨26002906446250524567214109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17335270964167016378142739 26002906446250524567214109)
        ·
          refine ⟨9751089917343946712705291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26002906446250524567214109 9751089917343946712705291)
          ·
            refine ⟨14626634876015920069057937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9751089917343946712705291 14626634876015920069057937)
            ·
              refine ⟨10969976157011940051793453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14626634876015920069057937 10969976157011940051793453)
              ·
                refine ⟨4113741058879477519422545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10969976157011940051793453 4113741058879477519422545)
                ·
                  refine ⟨3085305794159608139566909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113741058879477519422545 3085305794159608139566909)
                  ·
                    refine ⟨1156989672809853052337591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085305794159608139566909 1156989672809853052337591)
                    ·
                      rfl

theorem cell22_3379844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_3379844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379844 prefixEnd_3379844 := by exact prefixLift 3379844
  have htrace : WordTrace (prefixWord ++ tailWord_3379844) baseStart_3379844 baseEnd_3379844 := by
    simpa [prefixWord, tailWord_3379844, baseEnd_3379844] using wordTrace_append hprefix tailTrace_3379844
  have hstable : (prefixWord ++ tailWord_3379844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379844).length < 2 ^ (prefixWord ++ tailWord_3379844).sum := by decide
  have hdescent : baseEnd_3379844 < baseStart_3379844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379966 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3379966 : Nat := 118140960795 + 3379966 * 2 ^ 59
def prefixEnd_3379966 : Nat := 4983230072969 + 3 ^ 40 * 3379966 * 2
def baseEnd_3379966 : Nat := 1157031435903085400787217

theorem tailTrace_3379966 : CollatzResearch.WordTrace tailWord_3379966 prefixEnd_3379966 1157031435903085400787217 := by
  unfold tailWord_3379966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15409685959120988635063969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82184991781978606053674501 15409685959120988635063969)
  ·
    refine ⟨11557264469340741476297977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15409685959120988635063969 11557264469340741476297977)
    ·
      refine ⟨8667948352005556107223483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11557264469340741476297977 8667948352005556107223483)
      ·
        refine ⟨13001922528008334160835225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667948352005556107223483 13001922528008334160835225)
        ·
          refine ⟨9751441896006250620626419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13001922528008334160835225 9751441896006250620626419)
          ·
            refine ⟨14627162844009375930939629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9751441896006250620626419 14627162844009375930939629)
            ·
              refine ⟨5485186066503515974102361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14627162844009375930939629 5485186066503515974102361)
              ·
                refine ⟨4113889549877636980576771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485186066503515974102361 4113889549877636980576771)
                ·
                  refine ⟨6170834324816455470865157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113889549877636980576771 6170834324816455470865157)
                  ·
                    refine ⟨1157031435903085400787217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6170834324816455470865157 1157031435903085400787217)
                    ·
                      rfl

theorem cell22_3379966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3379966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379966 prefixEnd_3379966 := by exact prefixLift 3379966
  have htrace : WordTrace (prefixWord ++ tailWord_3379966) baseStart_3379966 baseEnd_3379966 := by
    simpa [prefixWord, tailWord_3379966, baseEnd_3379966] using wordTrace_append hprefix tailTrace_3379966
  have hstable : (prefixWord ++ tailWord_3379966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379966).length < 2 ^ (prefixWord ++ tailWord_3379966).sum := by decide
  have hdescent : baseEnd_3379966 < baseStart_3379966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379977 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_3379977 : Nat := 118140960795 + 3379977 * 2 ^ 59
def prefixEnd_3379977 : Nat := 4983230072969 + 3 ^ 40 * 3379977 * 2
def baseEnd_3379977 : Nat := 1157035201427885038762183

theorem tailTrace_3379977 : CollatzResearch.WordTrace tailWord_3379977 prefixEnd_3379977 1157035201427885038762183 := by
  unfold tailWord_3379977
  simp only [CollatzResearch.WordTrace]
  refine ⟨123277888875928057959162185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82185259250618705306108123 123277888875928057959162185)
  ·
    refine ⟨92458416656946043469371639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123277888875928057959162185 92458416656946043469371639)
    ·
      refine ⟨138687624985419065204057459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92458416656946043469371639 138687624985419065204057459)
      ·
        refine ⟨208031437478128597806086189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138687624985419065204057459 208031437478128597806086189)
        ·
          refine ⟨78011789054298224177282321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208031437478128597806086189 78011789054298224177282321)
          ·
            refine ⟨58508841790723668132961741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78011789054298224177282321 58508841790723668132961741)
            ·
              refine ⟨21940815671521375549860653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58508841790723668132961741 21940815671521375549860653)
              ·
                refine ⟨8227805876820515831197745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21940815671521375549860653 8227805876820515831197745)
                ·
                  refine ⟨6170854407615386873398309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8227805876820515831197745 6170854407615386873398309)
                  ·
                    refine ⟨1157035201427885038762183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6170854407615386873398309 1157035201427885038762183)
                    ·
                      rfl

theorem cell22_3379977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_3379977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379977 prefixEnd_3379977 := by exact prefixLift 3379977
  have htrace : WordTrace (prefixWord ++ tailWord_3379977) baseStart_3379977 baseEnd_3379977 := by
    simpa [prefixWord, tailWord_3379977, baseEnd_3379977] using wordTrace_append hprefix tailTrace_3379977
  have hstable : (prefixWord ++ tailWord_3379977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379977).length < 2 ^ (prefixWord ++ tailWord_3379977).sum := by decide
  have hdescent : baseEnd_3379977 < baseStart_3379977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379996 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_3379996 : Nat := 118140960795 + 3379996 * 2 ^ 59
def prefixEnd_3379996 : Nat := 4983230072969 + 3 ^ 40 * 3379996 * 2
def baseEnd_3379996 : Nat := 1157041705516175322537125

theorem tailTrace_3379996 : CollatzResearch.WordTrace tailWord_3379996 prefixEnd_3379996 1157041705516175322537125 := by
  unfold tailWord_3379996
  simp only [CollatzResearch.WordTrace]
  refine ⟨61639290931429612102051921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82185721241906149469402561 61639290931429612102051921)
  ·
    refine ⟨46229468198572209076538941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61639290931429612102051921 46229468198572209076538941)
    ·
      refine ⟨17336050574464578403702103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46229468198572209076538941 17336050574464578403702103)
      ·
        refine ⟨26004075861696867605553155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17336050574464578403702103 26004075861696867605553155)
        ·
          refine ⟨39006113792545301408329733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26004075861696867605553155 39006113792545301408329733)
          ·
            refine ⟨7313646336102244014061825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39006113792545301408329733 7313646336102244014061825)
            ·
              refine ⟨5485234752076683010546369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7313646336102244014061825 5485234752076683010546369)
              ·
                refine ⟨4113926064057512257909777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485234752076683010546369 4113926064057512257909777)
                ·
                  refine ⟨3085444548043134193432333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113926064057512257909777 3085444548043134193432333)
                  ·
                    refine ⟨1157041705516175322537125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085444548043134193432333 1157041705516175322537125)
                    ·
                      rfl

theorem cell22_3379996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_3379996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3379996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3379996 prefixEnd_3379996 := by exact prefixLift 3379996
  have htrace : WordTrace (prefixWord ++ tailWord_3379996) baseStart_3379996 baseEnd_3379996 := by
    simpa [prefixWord, tailWord_3379996, baseEnd_3379996] using wordTrace_append hprefix tailTrace_3379996
  have hstable : (prefixWord ++ tailWord_3379996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379996).length < 2 ^ (prefixWord ++ tailWord_3379996).sum := by decide
  have hdescent : baseEnd_3379996 < baseStart_3379996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380013 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3380013 : Nat := 118140960795 + 3380013 * 2 ^ 59
def prefixEnd_3380013 : Nat := 4983230072969 + 3 ^ 40 * 3380013 * 2
def baseEnd_3380013 : Nat := 1157047524963592944862073

theorem tailTrace_3380013 : CollatzResearch.WordTrace tailWord_3380013 prefixEnd_3380013 1157047524963592944862073 := by
  unfold tailWord_3380013
  simp only [CollatzResearch.WordTrace]
  refine ⟨123279201903797636107472693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82186134602531757404981795 123279201903797636107472693)
  ·
    refine ⟨11557425178481028385075565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123279201903797636107472693 11557425178481028385075565)
    ·
      refine ⟨4334034441930385644403337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11557425178481028385075565 4334034441930385644403337)
      ·
        refine ⟨3250525831447789233302503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4334034441930385644403337 3250525831447789233302503)
        ·
          refine ⟨4875788747171683849953755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250525831447789233302503 4875788747171683849953755)
          ·
            refine ⟨7313683120757525774930633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875788747171683849953755 7313683120757525774930633)
            ·
              refine ⟨5485262340568144331197975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7313683120757525774930633 5485262340568144331197975)
              ·
                refine ⟨8227893510852216496796963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485262340568144331197975 8227893510852216496796963)
                ·
                  refine ⟨12341840266278324745195445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8227893510852216496796963 12341840266278324745195445)
                  ·
                    refine ⟨1157047524963592944862073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12341840266278324745195445 1157047524963592944862073)
                    ·
                      rfl

theorem cell22_3380013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3380013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380013 prefixEnd_3380013 := by exact prefixLift 3380013
  have htrace : WordTrace (prefixWord ++ tailWord_3380013) baseStart_3380013 baseEnd_3380013 := by
    simpa [prefixWord, tailWord_3380013, baseEnd_3380013] using wordTrace_append hprefix tailTrace_3380013
  have hstable : (prefixWord ++ tailWord_3380013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380013).length < 2 ^ (prefixWord ++ tailWord_3380013).sum := by decide
  have hdescent : baseEnd_3380013 < baseStart_3380013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
